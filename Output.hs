module Output(clearScreen,putMozi,putChara,playAudio
             ,putText,drawCons,startGame,randomMessage
             ,drawGauges) where

import Haste.Graphics.Canvas(Canvas,Color(RGB),Bitmap,Point,Vector,Shape
                            ,color,font,translate,rotate,line,arc,rect,circle
                            ,text,draw,scale,render,stroke,fill,lineWidth
                            ,renderOnTop)
import Haste.Audio (play,Audio)
import Control.Monad (when,unless)
import Define (miy,wg,hg,wt,ht,cvT,nfs,rfs,wstIndex,storeName
              ,State(..),Switch(..),Con(..),CRect(..),CInfo
              ,Pos,Size,Fsize,Bord(..),TxType(..),LSA(..),Gauge(..))
import Browser (chColors,localStore)
import Initialize (testCon)
import EAffirm (affr)
import Events (loadState)
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

startGame :: Canvas -> CInfo -> Bmps -> State -> IO State 
startGame c ci bmps st = do
  randomMessage c ci bmps st 
  sData <- localStore Load storeName "" 
  return $ if sData=="loadError" then st else loadState sData st

randomMessage :: Canvas -> CInfo -> Bmps -> State -> IO ()
randomMessage c ci bmps st = do
  let randomG = rgn st
  (affText,ng) <- affr randomG
  let affCons = [testCon{txts=[affText]}]
  drawCons c ci bmps affCons 

drawGauges :: Canvas -> [Gauge] -> IO ()
drawGauges _ [] = return ()
drawGauges c gausSt = mapM_ (putGauge c) gausSt  

drawCons :: Canvas -> CInfo -> Bmps -> [Con] -> IO ()
drawCons _ _ _ [] = return ()
drawCons c ((_,cvH),_) bmps consSt = mapM_ (putCon c cvH bmps) consSt

putGauge :: Canvas -> Gauge -> IO ()
putGauge c (Gauge title (gx,gy) (gw,gh) mx cu) = do
  let scol = chColors!!3 -- red
      mcol = chColors!!6 -- yellow
      lcol = chColors!!4 -- cyan
      scu 
        | cu<0 = 0
        | cu>mx = mx
        | otherwise = cu
      mxD = fromIntegral mx; cuD = fromIntegral scu
      mdc = mxD / cuD
      fcol
        | mdc > 3 = scol
        | mdc < 2 = lcol
        | otherwise = mcol
      bcol = head chColors
  putText c bcol (floor gh*2) (gx,gy) title
  unless (cu==0) $ renderOnTop c $ color fcol $ fill $ roundRect (gx,gy) (gw/mdc,gh)
  renderOnTop c $ color bcol $ lineWidth 1 $
                                       stroke $ roundRect (gx,gy) (gw,gh)
  putText c fcol (floor gh*2) (gx+gw,gy+gh) (show (max cu 0))

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
    Circle -> do
      let rd = cw/2
      renderOnTop c $ color fcol $ fill $ circle (cx+rd,cy+rd) rd 
      renderOnTop c $ color bcol $ lineWidth 3 $
                                       stroke $ circle (cx+rd,cy+rd) rd 
    _ -> return ()
  mapM_ (\((tx,tp),((tpx,tpy),(fz,col))) ->
             putTextV c wbmp (chColors!!col) tp fz (cw,ch) (tpx+cx,tpy+cy) tx)
                                 $ zip (zip txs tps) (zip txpos (zip txfsz txcol))

putText :: Canvas -> Color -> Fsize -> Point -> String -> IO ()
putText c col fz (x,y) str = renderOnTop c $ 
    color col $ font (show fz++"px Courier") $ text (x,y) str

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
        let isMax = cln > mll
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
