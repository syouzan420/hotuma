{-# LANGUAGE LambdaCase #-}
module Loop (inputLoop,mouseClick,timerEvent) where

import Haste.Graphics.Canvas(Canvas,Bitmap)
import Haste.Audio(Audio,play)
import Control.Monad(unless,when,void)
import Browser(chColors,cvRatio,localStore,stringToJson)
import Output(clearScreen,drawCons,drawGauges,drawBoard)
import Generate(genMGauges)
import Getting (findCon,getConID,getBoardEv,getScore,getOstInd,getPlNDir
               ,getCellSize,getNextPos)
import Events(evStgLt,evStgWd,evChoice,evAns,evResult,evIntro
             ,evStudy,evLearn,evSummary,evChClick,evMission
             ,evMEnd,evStart,evResetNotice,evExplain,evRevealL)
import Initialize(initBoard)
import Define(storeName,Pos,Size,CInfo
             ,State(..),Switch(..),Con(..),CRect(..)
             ,Event(..),BEvent(..),Stage(..),Score(..)
             ,Board(..),BMode(..),Dir(..),Sound(..)
             ,DCon(..),Obj(..),Role(..),LSA(..))

type Bmps = ([Bitmap],[Bitmap],[Bitmap]) -- image, wosite, characters
type Auds = ([Audio],[Audio]) -- wosite sound, sound effect

mouseClick :: Canvas -> CInfo -> Bmps -> Auds -> (Int,Int) -> State -> IO State
mouseClick c ci bmps aus (x,y) st = do
  let (rtx,rty) = cvRatio ci
      nx = fromIntegral x*rtx
      ny = fromIntegral y*rty
      consSt = cons st
      dconSt = dcon st
      boardSt = board st
      bmdSt = bMode boardSt
      ncid = if null consSt then (-1) else getConID (nx,ny) (reverse consSt)
      nbev = if bmdSt==NoB then NoBEvent else getBoardEv (nx,ny) boardSt
      npdr = case dconSt of Nothing -> NoDir; Just dc -> getPlNDir (nx,ny) dc
  inputLoop c ci bmps aus ncid nbev npdr st 

evBoard :: Size -> Int -> Int -> BEvent -> State -> State
evBoard _ _ _ NoBEvent st = st
evBoard cvSz cid conNum bev st = 
  let boardSt@(Board _ bps bsc bi xev) = board st
      nboard = case bev of
          NoBEvent -> boardSt
          GetNe i -> Board (Ne i) bps bsc bi xev
          GetOs i j -> Board (Os (getOstInd i j)) bps bsc bi xev
      (Board nbmd _ _ nbi nxev) = nboard
   in case nbmd of 
    Os i -> do
        let st' = st{seAu=[Aoss i]}
        if i==nbi 
          then execEvent cvSz cid conNum nxev st'{board=initBoard}
          else st'{board=Board Ko bps bsc bi xev}
    _ -> st{board=nboard}

dcUpdate :: Dir -> State -> State
dcUpdate NoDir st = st
dcUpdate pdr st = 
  let mbDCon = dcon st
   in case mbDCon of
        Nothing -> st
        Just dcn@(DCon cbs gsz objs tmc) -> 
              let (Obj (Pl _) pps ai) = head objs 
                  oths = tail objs
                  rec = cRec cbs -- con rect
                  csz = getCellSize cbs gsz -- cell size
                  nai = if ai==0 then 1 else 0
                  (npos,pev) = getNextPos rec csz pdr pps oths
                  npl = Obj (Pl pdr) npos nai
                  nobjs = npl:oths
               in st{dcon=Just (DCon cbs gsz nobjs tmc)}

inputLoop :: Canvas -> CInfo -> Bmps -> Auds
                   -> Int -> BEvent -> Dir -> State -> IO State 
inputLoop c ci@(cvSz,_) bmps (oss,ses) cid bev pdr st = do
  let consSt = cons st
      conNum = length consSt
      mbCon = if cid==(-1) then Nothing else findCon cid consSt
      st' = evBoard cvSz cid conNum bev st
  nst <- case mbCon of
              Nothing -> return st'
              Just co -> if enable co 
                then execEventIO cvSz cid conNum (clEv co) st' 
                else return st'
  unless (st==nst) $ drawScreen c ci bmps nst
  case lsa nst of
    Save dt -> void $ localStore (Save dt) storeName
    Remv -> void $ localStore Remv storeName 
    _ -> return ()
  mapM_ (\case
    Aoss osInd -> play (oss!!osInd)
    Ases seInd -> play (ses!!seInd) 
    NoSound -> return ()) (seAu nst) 
  return nst{seAu=[],lsa=NoLSA}

execEventIO :: Size -> Int -> Int -> Event -> State -> IO State
execEventIO cvSz cid conNum ev st = case ev of   
   Mission stg i lv -> evMission cvSz stg i lv st
   Quest stg -> case stg of
          StgLetter lv -> if lv > 45
              then return $ evResult cvSz st
              else evStgLt cvSz lv st{stage=Just stg} 
          StgWord lv -> evStgWd cvSz lv st{stage=Just stg}
   _ -> return $ execEvent cvSz cid conNum ev st

execEvent :: Size -> Int -> Int -> Event -> State -> State
execEvent cvSz cid conNum ev st = case ev of
   ScrReset -> evStudy cvSz st{cli=[],lsa=Remv}
   IsReset -> evResetNotice cvSz st
   Intro -> evIntro cvSz st
   Explain i -> evExplain cvSz i st
   Start -> evStart cvSz st
   Study -> evStudy cvSz st
   Learn stg num -> evLearn cvSz stg num st
   RevealL -> evRevealL st
   Summary stg -> evSummary cvSz stg st
   ChClick oi -> evChClick cid oi st
   MEnd stg lv -> evMEnd cvSz stg lv st
   Choice i -> evChoice cvSz conNum i st
   Answer i -> evAns cvSz i st
   _ -> st

drawScreen :: Canvas -> CInfo -> Bmps -> State -> IO ()
drawScreen c ci bmps@(_,wbmp,_) st = 
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

