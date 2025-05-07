module Loop (inputLoop,mouseClick,timerEvent) where

import Haste.Graphics.Canvas(Canvas,Bitmap)
import Haste.Audio(Audio,play)
import Control.Monad(unless,when)
import Browser(chColors,cvRatio,localStore,stringToJson)
import Output(clearScreen,drawCons,drawGauges,drawBoard,randomMessage)
import Generate(genMGauges)
import Getting (findCon,getConID,getBoardEv,getScore,getOstInd)
import Events(evStgLt,evStgWd,evChoice,evAns,evResult,evIntro
             ,evStudy,evLearn,evSummary,evChClick,evMission
             ,evMEnd,evStart,evResetNotice,removeData,evExplain,evRevealL)
import Initialize(initBoard)
import Define(State(..),Switch(..),Con(..),CRect(..),CInfo,Pos
             ,Event(..),BEvent(..),Stage(..),Score(..)
             ,Board(..),BMode(..),Size)

type Bmps = ([Bitmap],[Bitmap])
type Auds = ([Audio],[Audio])

mouseClick :: Canvas -> CInfo -> Bmps -> Auds -> (Int,Int) -> State -> IO State
mouseClick c ci bmps aus (x,y) st = do
  let (rtx,rty) = cvRatio ci
      nx = fromIntegral x*rtx
      ny = fromIntegral y*rty
      consSt = cons st
      boardSt = board st
      ncid = getConID (nx,ny) (reverse consSt)
      nbev = getBoardEv (nx,ny) boardSt
  inputLoop c ci bmps aus ncid nbev st 

inputLoop :: Canvas -> CInfo -> Bmps -> Auds -> Int -> BEvent -> State -> IO State 
inputLoop c ci@(cvSz,_) bmps (oss,ses) cid bev st = do
  let consSt = cons st
      conNum = length consSt
      mbCon = if cid==(-1) then Nothing else findCon cid consSt
      boardSt@(Board _ bps bsc bi xev) = board st
      nboard = case bev of
          NoBEvent -> boardSt
          GetNe i -> Board (Ne i) bps bsc bi xev
          GetOs i j -> Board (Os (getOstInd i j)) bps bsc bi xev
      (Board nbmd _ _ nbi nxev) = nboard
  st' <- case nbmd of 
    Os i -> do
        play $ oss!!i
        if i==nbi 
          then execEvent cvSz (oss,ses) cid conNum nxev st{board=initBoard}
          else return st{board=Board Ko bps bsc bi xev}
    _ -> return st{board=nboard}
  nst <- case mbCon of
              Nothing -> return st'
              Just co -> if enable co 
                then execEvent cvSz (oss,ses) cid conNum (clEv co) st' 
                else return st'
  unless (st==nst) $ drawScreen c ci bmps nst
  case seAu nst of
    Just seInd -> play (ses!!seInd) >> return nst{seAu=Nothing}
    Nothing -> return nst

execEvent :: Size ->  Auds -> Int -> Int -> Event -> State -> IO State
execEvent cvSz (oss,ses) cid conNum ev st = case ev of
   ScrReset -> do 
       let nst = st{cli=[]}
       removeData
       return $ evStudy cvSz nst
   IsReset -> return $ evResetNotice cvSz st
   Intro -> return $ evIntro cvSz st
   Explain i -> return $ evExplain cvSz i st
   Start -> return $ evStart cvSz st
   Study -> return $ evStudy cvSz st
   Learn stg num -> evLearn cvSz oss stg num st
   RevealL -> return $ evRevealL st
   Summary stg -> return $ evSummary cvSz stg st
   ChClick oi -> evChClick oss cid oi st
   Mission stg i lv -> evMission cvSz (oss,ses) stg i lv st
   MEnd stg lv -> evMEnd cvSz ses stg lv st
   Quest stg -> case stg of
          StgLetter lv -> if lv > 45
              then evResult cvSz st
              else evStgLt cvSz oss lv st{stage=Just stg} 
          StgWord lv -> evStgWd cvSz lv st{stage=Just stg}
   Choice i -> return $ evChoice cvSz conNum i st
   Answer i -> return $ evAns cvSz i st
   _ -> return st

drawScreen :: Canvas -> CInfo -> Bmps -> State -> IO ()
drawScreen c ci bmps@(_,wbmp) st = 
  clearScreen c >> drawCons c ci bmps (cons st) >> drawGauges c (gaus st)
                >> drawBoard c wbmp (board st)

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

