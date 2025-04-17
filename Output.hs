module Output(clearScreen,putMozi,putChara,playAudio
             ,putText,drawCons,startGame,randomMessage) where

import Haste.Graphics.Canvas(Canvas,Color(RGB),Bitmap,Point,Vector,Shape
                            ,color,font,translate,rotate,line,arc,rect
                            ,text,draw,scale,render,stroke,fill,lineWidth
                            ,renderOnTop)
import Haste.Audio (play,Audio)
import Control.Monad (when)
import Define (miy,wg,hg,wt,ht,cvT,nfs,rfs,wstIndex
              ,State(..),Switch(..),Con(..),CRect(..),CInfo
              ,Pos,Size,Fsize,Bord(..),TxType(..))
import Browser(chColors)
import Initialize (testCon)
import EAffirm (affr)
import Libs(getIndex)

type Bmps = ([Bitmap],[Bitmap])


clearScreen :: Canvas -> IO ()
clearScreen c = render c $ text (0,0) "" 

putMozi :: Canvas -> Color -> Pos -> String -> IO ()
putMozi c col (x,y) str = renderOnTop c $ 
    mapM_ (\(ch,n)->color col$font (show nfs++"px Courier")$
      text (x*wg+wg*n,y*hg) [ch]) (zip str [0..]) 

putChara :: Canvas -> [Bitmap] -> Double -> Pos -> Int -> IO ()
putChara c chrs cvW pos ind = do  
  renderOnTop c $ translate pos $ scale (1,1) $ draw (chrs!!ind) (0,0)

playAudio :: Audio -> State -> IO State 
playAudio audio st = do
  let iAS = (ias . swc) st
  if iAS then return st else do
    play audio
    return st{swc=(swc st){ias=True}}

----------------------------
startGame :: Canvas -> CInfo -> Bmps -> State -> IO ()
startGame  = randomMessage  

randomMessage :: Canvas -> CInfo -> Bmps -> State -> IO ()
randomMessage c ci bmps st = do
  let randomG = rgn st
  (affText,ng) <- affr randomG
  let affCons = [testCon{txts=[affText]}]
  drawCons c ci bmps affCons 

drawCons :: Canvas -> CInfo -> Bmps -> [Con] -> IO ()
drawCons _ _ _ [] = return ()
drawCons c ((_,cvH),_) bmps consSt = mapM_ (putCon c cvH bmps) consSt

putCon :: Canvas -> Double -> Bmps -> Con -> IO ()
putCon c cvH bmps con = do
  let (CRect cx cy cw ch) = cRec con
      bocol = borCol con
      ficol = filCol con
      txpos = txtPos con
      txfsz = txtFsz con
      txcol = txtCos con
      txs = txts con
      tps = typs con
      bcol = chColors!!bocol
      fcol = chColors!!ficol
      (_,wbmp) = bmps
  case border con of
    Rigid -> renderOnTop c $ color bcol $ stroke $ rect (cx,cy) (cx+cw,cy+ch)
    Round -> do
      renderOnTop c $ color fcol $ fill $ roundRect (cx,cy) (cw,ch)
      renderOnTop c $ color bcol $ lineWidth 3 $
                                       stroke $ roundRect (cx,cy) (cw,ch)
    _ -> return ()
  mapM_ (\((tx,tp),((tpx,tpy),(fz,col))) ->
             putTextV c wbmp (chColors!!col) tp fz (cw,ch) (tpx+cx,tpy+cy) tx)
                                 $ zip (zip txs tps) (zip txpos (zip txfsz txcol))

putText :: Canvas -> Color -> Fsize -> Point -> String -> IO ()
putText c col fz (x,y) str = renderOnTop c $ 
    mapM_ (\(ch,n)->color col$font (show fz++"px Courier")$
      text (x*wg+wg*n,y*hg) [ch]) (zip str [0..]) 

putTextV :: Canvas -> [Bitmap] -> Color -> TxType -> Fsize -> Size 
                                                -> Point -> String -> IO ()
putTextV c wbmp col tp fz sz (p,q) = putLettersV c wbmp col tp fz sz q 0 (p,q) 

putLettersV :: Canvas -> [Bitmap] -> Color -> TxType -> Fsize -> Size
                     -> Double -> Int -> Point -> String -> IO ()
putLettersV _ _ _ _ _ _ _ _ _ [] = return ()
putLettersV c wbmp col tp fz sz@(w,h) miq cln (pd,qd) (x:xs) = do
  let fzD = fromIntegral fz 
      ltw = fzD * 1.2
      lth = fzD * 1.1 
      mll = floor (h/lth) - 2 -- max letter length
  case x of 
    '\r'  -> putLettersV c wbmp col tp fz sz miq 0 (pd-ltw,miq) xs
    _     -> do 
        case tp of
          Normal -> putLet c col fz 0 (pd,qd) x  
          Osite -> putWst c wbmp fz (pd-fzD/6,qd-fzD*3/4) x 
        let isMax = cln+1 > mll
        let ncln = if isMax then 0 else cln+1
        let npd = if isMax then pd-ltw else pd
        let nqd = if isMax then miq else qd+lth 
        putLettersV c wbmp col tp fz sz miq ncln (npd,nqd) xs

putWst :: Canvas -> [Bitmap] -> Fsize -> Point -> Char -> IO () 
putWst c wsts fs (x,y) ch = do
  let sc = fromIntegral fs/fromIntegral nfs -- nfs: normal font size
  renderOnTop c $ translate (x,y) $ scale (sc,sc) $ draw (wsts!!ind) (0,0)
    where ind = if ch `elem` wstIndex then getIndex ch wstIndex else 14

putLet :: Canvas -> Color -> Fsize -> Double -> Point -> Char -> IO ()
putLet c col fs rd (x,y) ch = do
  renderOnTop c $ color col$font (show fs++"px IPAGothic")$
    translate (x,y)$rotate rd$text (0,0) [ch]

roundRectLine :: Point -> Vector -> Shape ()
roundRectLine (x,y) (w,h) = do  
  line (x,y+10) (x,y+h-10)
--  arc (x+10,y+h-10) 10 (pi*0.5) pi
  line (x+10,y+h) (x+w-10,y+h)
--  arc (x+w-10,y+h-10) 10 0 (pi*0.5)
  line (x+w,y+h-10) (x+w,y+10)
--  arc (x+w-10,y+10) 10 (pi*1.5) (pi*2)
  line (x+w-10,y) (x+10,y)
--  arc (x+10,y+10) 10 pi (pi*1.5)

roundRect :: Point -> Vector -> Shape ()
roundRect (x,y) (w,h) = do  
  arc (x+w-10,y+h-10) 10 0 (pi*0.5)
  arc (x+10,y+h-10) 10 (pi*0.5) pi
  arc (x+10,y+10) 10 pi (pi*1.5)
  arc (x+w-10,y+10) 10 (pi*1.5) (pi*2)
  line (x+w,y+h-10) (x+w,y+10)
