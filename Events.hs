module Events(makeStgLt,makeStgWd,makeChoice,makeAns,makeSaveData
             ,makeStudy,makeLearn,makeResult,timerEvent,loadState
             ,makeSummary,makeChClick,makeMission) where

import Haste.Audio (Audio,play)
import Data.List (intercalate)
import Generate (genLtQuest,genCons,genSCons,genAnsCon,genLCons
                ,genSumCons,genMission)
import Libs (sepByChar)
import Initialize (testCon)
import Define (State(..),Event(..),Stage(..),Question(..),Con(..)
              ,Size,CRect(..),Score(..),Switch(..),TxType(..),mTimeLimit)

makeSaveData :: State -> String
makeSaveData st =
  let clearData = cli st
      scoreData = score st
   in "\""++intercalate "~" [show clearData,show scoreData]++"\""

loadState :: String -> State -> State
loadState "" st = st
loadState str st =
  let dt = if head str=='\"' then tail$init str else str
      dts = sepByChar '~' dt
      clearData = read (head dts) :: [Int]
      scoreData = read (dts!!1) :: Score
   in st{score=scoreData,cli=clearData}

makeMission :: Size -> [Audio] -> Int -> Int -> Int -> State -> IO State
makeMission cvSz oss stg i lv st = do 
  let pq = quest st -- previous question
      (pai,pan) = case pq of
        Just pq' -> (audios pq'!!aInd pq',aInd pq')
        Nothing -> (-1,0)
      correct = i==pan
      Score ms tm = score st
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
      tau = oss!!ai
  play tau
  print nscr 
  return st{score=nscr,quest=Just q,cons=ncos,rgn=ng,swc=(swc st){ita=True}}

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
      ncos = genSCons cvSz clIndexes
   in st{cons=ncos}

makeStgLt :: Size -> [Audio] -> Int -> State -> IO State
makeStgLt cvSz oss lv st = do  
  let g = rgn st -- random number generator 
      qs = qsrc st -- quest source
  ((q,nqs),ng) <- genLtQuest g lv qs
  let cos = genCons cvSz q
      tau = oss!!(audios q!!aInd q)
  play tau
  return st{quest=Just q,cons=cos,qsrc=nqs,rgn=ng,swc=(swc st){ita=True}}

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

timerEvent :: State -> State
timerEvent st = let it = ita (swc st) -- is timer active? 
                    (Score ms tm) = score st
                 in if not it then st else st{score=Score ms (tm+1)}
