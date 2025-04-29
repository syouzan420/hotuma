module Loop (inputLoop,mouseClick,timerEvent) where

import Haste.Graphics.Canvas(Canvas,Bitmap)
import Haste.Audio(Audio,play)
import Control.Monad(unless,when)
import Browser(chColors,cvRatio,localStore,stringToJson)
import Output(clearScreen,drawCons,drawGauges,randomMessage)
import Generate(genMGauges)
import Events(makeStgLt,makeStgWd,makeChoice,makeAns,makeResult
             ,makeStudy,makeLearn,makeSummary,makeChClick,makeMission
             ,makeMEnd,makeStart,getScore,makeResetNotice,removeData)
import Define(State(..),Switch(..),Con(..),CRect(..),CInfo,Pos
             ,Event(..),Stage(..),Score(..))

type Bmps = ([Bitmap],[Bitmap])
type Auds = ([Audio],[Audio])

mouseClick :: Canvas -> CInfo -> Bmps -> Auds -> (Int,Int) -> State -> IO State
mouseClick c ci bmps aus (x,y) st = do
  let (rtx,rty) = cvRatio ci
      nx = fromIntegral x*rtx
      ny = fromIntegral y*rty
      consSt = cons st
  inputLoop c ci bmps aus (getConID (nx,ny) (reverse consSt)) st 

inputLoop :: Canvas -> CInfo -> Bmps -> Auds -> Int -> State -> IO State 
inputLoop c ci@(cvSz,_) bmps (oss,ses) cid st = do
  let consSt = cons st
      conNum = length consSt
      mbCon = if cid==(-1) then Nothing else findCon cid consSt
  nst <- case mbCon of
              Nothing -> return st
              Just co -> do 
                  let ev = clEv co
                  case ev of
                    ScrReset -> do 
                      let nst = st{cli=[]}
                      removeData
                      return $ makeStudy cvSz nst
                    IsReset -> return $ makeResetNotice cvSz st
                    Start -> return $ makeStart cvSz st
                    Study -> return $ makeStudy cvSz st
                    Learn stg num -> makeLearn cvSz oss stg num st
                    Summary stg -> return $ makeSummary cvSz stg st
                    ChClick oi -> makeChClick oss cid oi st
                    Mission stg i lv -> makeMission cvSz (oss,ses) stg i lv st
                    MEnd stg lv -> makeMEnd cvSz ses stg lv st
                    Quest stg -> case stg of
                        StgLetter lv -> if lv > 45
                            then makeResult cvSz st 
                            else makeStgLt cvSz oss lv st{stage=Just stg} 
                        StgWord lv -> makeStgWd cvSz lv st{stage=Just stg}
                    Choice i -> return $ makeChoice cvSz conNum i st
                    Answer i -> return $ makeAns cvSz i st
                    _ -> return st
  unless (st==nst) $ drawScreen c ci bmps nst
  case seAu nst of
    Just seInd -> play (ses!!seInd) >> return nst{seAu=Nothing}
    Nothing -> return nst

drawScreen :: Canvas -> CInfo -> Bmps -> State -> IO ()
drawScreen c ci bmps st = 
  clearScreen c >> drawCons c ci bmps (cons st) >> drawGauges c (gaus st)

timerEvent :: Canvas -> CInfo -> Bmps -> State -> IO State
timerEvent c ci@(cvSz,_) bmps st = do
  let itime = ita (swc st) -- is timer active? 
      (Score ms tm) = score st
      mtp = mtype st
      lv = level st
      ngaus = genMGauges cvSz mtp (getScore mtp lv ms) (tm+1)
      nst = if not itime then st else st{score=Score ms (tm+1),gaus=ngaus}
  when itime $ drawScreen c ci bmps nst
  return nst

findCon :: Int -> [Con] -> Maybe Con
findCon _ [] = Nothing  
findCon i (co:xs) = let cid = conID co in if i==cid then Just co else findCon i xs

getConID :: Pos -> [Con] -> Int
getConID _ [] = -1
getConID (x,y) (co:xs) = 
  let (CRect cx cy cw ch) = cRec co
      isIn = x > cx && x < cx+cw && y > cy && y < cy+ch
   in if isIn then conID co else getConID (x,y) xs  
