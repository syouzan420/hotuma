module Events(makeStgLt,makeStgWd,makeChoice,makeAns) where

import Haste.Audio(Audio,play)
import Generate (genLtQuest,genCons,genAnsCon)
import Define (State(..),Event(..),Stage(..),Question(..),Con(..),Size,CRect(..))

type Auds = [Audio]

makeStgLt :: Size -> Auds -> Int -> State -> IO State
makeStgLt cvSz aus lv st = do  
  let g = rgn st -- random number generator 
  (q,ng) <- genLtQuest g lv 
  let cos = genCons cvSz q
      tau = aus!!(audios q!!aInd q)
  play tau
  return st{quest=Just q,cons=cos,rgn=ng}

makeStgWd :: Size -> Int -> State -> IO State
makeStgWd cvSz lv st = undefined

makeChoice :: Size -> Int -> Int -> State -> State
makeChoice cvSz conNum i st =
  let mbQ = quest st
      qNum = case mbQ of
        Just (Question qlist _ _) -> length qlist
        Nothing -> 0
      (hco:chCos) = cons st 
      tco = chCos!!i
      chCos' = map (changeBColor 0) chCos 
      ntco = changeBColor 4 tco
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
   in st{cons=niCos++[nlco]} 

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
   in st{cons=hco:nchCos++[nlco]}

makeNextStg :: State -> IO State
makeNextStg st = undefined


changeBColor :: Int -> Con -> Con
changeBColor i co = co{borCol=i}

changeText :: [String] -> Con -> Con
changeText txs co = co{txts=txs}

changeEvent :: Event -> Con -> Con
changeEvent ev co = co{clEv=ev}
