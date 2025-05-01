module Events(makeStgLt,makeStgWd,makeChoice,makeAns,makeSaveData
             ,makeStudy,makeLearn,makeResult,loadState,getScore
             ,makeSummary,makeChClick,makeMission,makeMEnd,makeStart
             ,makeResetNotice,removeData) where

import Haste.Audio (Audio,play)
import Data.List (intercalate)
import Control.Monad (when,void)
import Generate (genLtQuest,genCons,genSCons,genAnsCon,genLCons
                ,genSumCons,genMission,genNoticeCon,genStartCons
                ,genBackCon,genMGauges,genScrResetCon)
import Libs (sepByChar)
import Browser (localStore)
import Initialize (testCon)
import Define (State(..),Event(..),Stage(..),Question(..),Con(..),MType(..)
              ,Size,CRect(..),Score(..),Switch(..),TxType(..),LSA(..)
              ,mTimeLimit,clearScore,storeName)

type Auds = ([Audio],[Audio])

removeData :: IO ()
removeData = void $ localStore Remv storeName "" 

makeSaveData :: State -> String
makeSaveData st =
  let clearData = cli st
      hiScoreData = hiscs st
   in "\""++intercalate "~" [show clearData,show hiScoreData]++"\""

loadState :: String -> State -> State
loadState "" st = st
loadState str st =
  let dt = if head str=='\"' then tail$init str else str
      dts = sepByChar '~' dt
      clearData = read (head dts) :: [Int]
      hiScoreData = read (dts!!1) :: [Int] 
   in st{hiscs=hiScoreData,cli=clearData}

makeResetNotice :: Size -> State -> State
makeResetNotice cvSz@(cW,cH) st =
  let mgnX = cW/3 
      conW = cW-mgnX*2
      fsz = 30
      fsD = fromIntegral fsz
      cns = cons st
      ncons = map (changeEvent NoEvent) cns 
      lng = length cns
      srCon = genNoticeCon cvSz lng 3 "スコアをリセットしますか？" NoEvent
      srCon' = srCon{txtPos=[(conW-fsD*2,fsD)],txtFsz=[fsz],txtCos=[7]}
      nCon = genNoticeCon cvSz (lng+1) 7 "いいえ" Study 
      nCon' = nCon{cRec=CRect (cW/20) (cH/3*2) conW (cH/4)
                  ,txtPos=[(conW-80,40)],txtCos=[0]} 
      yCon = genNoticeCon cvSz (lng+2) 7 "はい" ScrReset 
      yCon' = yCon{cRec=CRect (cW/3*2-cW/20) (cH/3*2) conW (cH/4)
                  ,txtPos=[(conW-80,80)]}
   in st{cons=ncons++[srCon',yCon',nCon']}

makeStart :: Size -> State -> State
makeStart cvSz st = st{mtype=NoMission,cons=genStartCons cvSz
                      ,gaus=[],swc=(swc st){ita=False}} 

makeMEnd :: Size -> [Audio] -> Int -> Int -> State -> IO State
makeMEnd cvSz ses stg lv st = do 
  let Score ms _ = score st 
      scr = lv - ms*2
      hiscores = hiscs st
      phscr = hiscores!!stg  -- previous high score
      nhscr = max scr phscr
      nhiscs = repList nhscr stg hiscores 
      isClear = scr > clearScore
      cos = cons st
      ncons = map (changeEvent NoEvent) cos
      cln = length cos
      tx = if isClear then " クリア！" else "ざんねん！"
      flco = if isClear then 6 else 8
      atCo = genNoticeCon cvSz cln flco tx Study  
      ci = cli st
      ncli = if isClear then if stg `elem` ci then ci else stg:ci
                        else ci
      nst = st{hiscs=nhiscs,cons=ncons++[atCo],cli=ncli}
  if isClear then play (head ses) else play (ses!!1)
  when isClear $ void $ localStore Save storeName (makeSaveData nst) 
  return nst

makeMission :: Size -> Auds -> Int -> Int -> Int -> State -> IO State
makeMission cvSz (oss,ses) stg i lv st = do 
  let pq = quest st -- previous question
      (pai,pan) = case pq of
        Just pq' -> (audios pq'!!aInd pq',aInd pq')
        Nothing -> (-1,0)
      correct = i==pan
  if correct then return () else when (lv>0) $ play (ses!!1)
  let Score ms tm = score st
      nms = if pai==(-1) || correct then ms else ms+1
      nscr = Score nms tm
      g = rgn st -- random number generator 
  (q,ng) <- genMission g stg pai 
  let (hco:cos) = genCons cvSz q
      ai = audios q!!aInd q 
      end = tm>=mTimeLimit
      ncos = hco:zipWith (\n co -> 
            changeEvent (if end then MEnd stg lv else Mission stg n (lv+1)) co)
                                                                       [0..] cos 
      ngaus = genMGauges cvSz Mi (getScore Mi lv nms) tm
      tau = oss!!ai
  play tau
--  print nscr 
  return st{mtype=Mi,level=lv,score=nscr,quest=Just q,cons=ncos,gaus=ngaus
           ,rgn=ng,swc=(swc st){ita=True}}

getScore :: MType -> Int -> Int -> Int
getScore Mi lv ms = lv-ms*2
getScore Qu lv _  = lv 
getScore _ _ _ = 0


makeChClick :: [Audio] -> Int -> Int -> State -> IO State
makeChClick oss i oi st = do
  let cos = cons st
      co = cos!!i
      tp = head (typs co) -- text type 
      eps = fromIntegral (head (txtFsz co)) / 4
      (psx,psy) = head (txtPos co) -- text position
      ntp = if tp==Osite then Normal else Osite
      ntps = if tp==Osite then (psx,psy+eps) else (psx,psy-eps) 
      nco = co{typs=[ntp],txtPos=[ntps]}
      ncons = repList nco i cos
  play (oss!!oi)
  return $ st{cons=ncons}

makeSummary :: Size -> Int -> State -> State
makeSummary cvSz stg st = st{cons=genSumCons cvSz stg} 

makeLearn :: Size -> [Audio] -> Int -> Int -> State -> IO State 
makeLearn cvSz oss stg num st = do 
  let stype = stg `mod` 2
      dif = stg `div` 2 * 12 + num
      maxNum = if stype==0 then 4 else 6
      oi = if stype==0 then dif else dif + 5 
      clEvnt = if num==maxNum then Summary stg else Learn stg (num+1) 
      lCons = genLCons cvSz oi clEvnt
  play (oss!!oi)
  return st{cons=lCons}

makeStudy :: Size -> State -> State
makeStudy cvSz st =
  let clIndexes = cli st 
      hiScores = hiscs st
      ncos = genSCons cvSz clIndexes hiScores
      lngCos = length ncos
      bco = genBackCon cvSz lngCos Start
      rco = genScrResetCon cvSz (lngCos+1)
      exco = if null clIndexes then [bco] else [bco,rco]
   in st{score=Score 0 0,quest=Nothing,cons=ncos++exco,gaus=[]
        ,swc=(swc st){ita=False}}

makeStgLt :: Size -> [Audio] -> Int -> State -> IO State
makeStgLt cvSz oss lv st = do  
  let g = rgn st -- random number generator 
      qs = qsrc st -- quest source
  ((q,nqs),ng) <- genLtQuest g lv qs
  let cos = genCons cvSz q
      tau = oss!!(audios q!!aInd q)
  play tau
  return st{mtype=Qu,quest=Just q,level=lv,cons=cos,qsrc=nqs,rgn=ng,swc=(swc st){ita=True}}

makeStgWd :: Size -> Int -> State -> IO State
makeStgWd cvSz lv st = undefined

makeResult :: Size -> State -> IO State
makeResult cvSz st = do 
  let (Score mis tim) = score st 
      ntxt = if mis==0 then "すごい！ 全問正解！"
                       else show mis ++ "回まちがへちゃったね！"
      ntxt2 = "\rかかった時間は " ++ show tim ++ " 秒だったよ"
      ncon = testCon{txts=[ntxt++ntxt2]}
      nScr = Score 0 0
      nst = st{score=nScr,cons=[ncon]}
  return nst

makeChoice :: Size -> Int -> Int -> State -> State
makeChoice cvSz conNum i st =
  let mbQ = quest st
      qNum = case mbQ of
        Just (Question qlist _ _) -> length qlist
        Nothing -> 0
      (hco:chCos) = cons st 
      tco = chCos!!i
      chCos' = map (changeFColor 7 . changeBColor 0) chCos 
      ntco = (changeFColor 8 . changeBColor 4) tco
      chCos'' = repList ntco i chCos'
      nchCos = if qNum+1==conNum then chCos'' else init chCos'' 
      aco = genAnsCon cvSz (qNum+1) i
   in st{cons=hco:nchCos++[aco]}

repList :: a -> Int -> [a] -> [a]
repList tg i lst = take i lst ++ [tg] ++ drop (i+1) lst

makeAns :: Size -> Int -> State -> State
makeAns cvSz i st =  
  let mbQ = quest st
      (qs,au,ai) = case mbQ of
          Just (Question qs' au' ai') -> (qs',au',ai')
          Nothing -> ([],[],0)
      isCorrect = ai==i
      nst = st{swc=(swc st){ita=False}}
   in if isCorrect then evCorrect cvSz i nst else evWrong i nst

evCorrect :: Size -> Int -> State -> State
evCorrect (cW,cH) i st =  
  let mbStg = stage st
      nstg = case mbStg of 
        Just (StgLetter i) -> StgLetter (i+1) 
        Just (StgWord i) -> StgWord (i+1)
        Nothing -> StgLetter 1
      cos = cons st 
      iCos = init cos
      niCos = map (changeEvent NoEvent) iCos
      lco = last cos
      lind = length cos - 1
      indX = cW/3; indY = cH/6
      fsz = 40
      fsD = fromIntegral fsz
      nlco = lco{cRec=CRect indX indY (cW-indX*2) (cH-indY*2)
                ,txtPos=[(cW/2-indX-fsD/2,fsD*3)]
                ,txtFsz=[fsz]
                ,txts=["せいかい！"]
                ,clEv=Quest nstg}
   in st{cons=niCos++[nlco],seAu=Just 0} 

evWrong :: Int -> State -> State
evWrong i st = 
  let mbStg = stage st
      nstg = case mbStg of
        Just stg -> stg
        Nothing -> StgLetter 1 
      mbq = quest st
      ai = case mbq of
            Just (Question _ _ a) -> a
            Nothing -> 0
      (hco:tlCos) = cons st 
      chCos = init tlCos
      tco = chCos!!i
      aco = chCos!!ai
      lco = last tlCos 
      ntco = changeBColor 3 tco
      naco = changeBColor 4 aco
      lco' = changeText ["は","づ","れ"] lco
      nlco = changeEvent (Quest nstg) lco'
      chCos' = repList ntco i chCos
      chCos'' = repList naco ai chCos'
      nchCos = map (changeEvent NoEvent) chCos''
      (Score pmis tim) = score st  
   in st{score=Score (pmis+1) tim,cons=hco:nchCos++[nlco],seAu=Just 1}


changeBColor :: Int -> Con -> Con
changeBColor i co = co{borCol=i}

changeFColor :: Int -> Con -> Con
changeFColor i co = co{filCol=i}

changeText :: [String] -> Con -> Con
changeText txs co = co{txts=txs}

changeEvent :: Event -> Con -> Con
changeEvent ev co = co{clEv=ev}

