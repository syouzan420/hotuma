module Events(makeStgLt,makeStgWd,makeChoice,makeAns,makeResult) where

import Haste.Audio(Audio,play)
import Generate (genLtQuest,genCons,genAnsCon)
import Initialize (testCon)
import Define (State(..),Event(..),Stage(..),Question(..),Con(..)
              ,Size,CRect(..),Score(..))


makeStgLt :: Size -> [Audio] -> Int -> State -> IO State
makeStgLt cvSz oss lv st = do  
  let g = rgn st -- random number generator 
  (q,ng) <- genLtQuest g lv 
  let cos = genCons cvSz q
      tau = oss!!(audios q!!aInd q)
  play tau
  return st{quest=Just q,cons=cos,rgn=ng}

makeStgWd :: Size -> Int -> State -> IO State
makeStgWd cvSz lv st = undefined

makeResult :: Size -> State -> IO State
makeResult cvSz st = do 
  let (Score mis _) = score st 
      ntxt = if mis==0 then "すごい！ 全問正解！"
                       else show mis ++ "回まちがへちゃったね！"
      ncon = testCon{txts=[ntxt]}
      nst = st{cons=[ncon]}
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
   in if isCorrect then evCorrect cvSz i st else evWrong i st

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
