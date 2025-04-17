module Generate(genLtQuest,genCons,genAnsCon) where

import Libs (selectData,getRan)
import Initialize (emCon)
import Define (State(..),Con(..),Question(..),Size,CRect(..)
              ,Bord(..),Event(..),TxType(..)
              ,ltQuestSrc)

genLtQuest :: Int -> Int -> IO (Question,Int)
genLtQuest g lv = do
  let aqn = lv+3 -- avalable question numbers 
      qn = 4 + lv `div` (8 - lv `div` 8) -- question numbers
  (ai,g') <- getRan qn g 
  (iqlist,ng) <- selectData qn g' (zip [0..] (take aqn ltQuestSrc))
  let (auInd,qlist) = unzip iqlist
  return (Question (map (:[]) qlist) auInd ai,ng)

genCons :: Size -> Question -> [Con]
genCons cSz@(cW,cH) (Question qlist auInd ai) = 
  let qLen = length qlist
      aText = qlist!!ai
      aAudio = auInd!!ai
      hConRec = CRect (cW/8) (cH/10) (cW/3) (cH/5)
      qConRecs = makeConsRec cSz qLen
      hCon = emCon{conID=0,cRec=hConRec,border=Round,filCol=5,txtPos=[(40,60)]
                ,txtFsz=[50],txtCos=[1],txts=[aText],typs=[Normal]
                ,audio=Just aAudio,clEv=NoEvent}
      qCons = zipWith (\i rec -> hCon{conID=i+1,cRec=rec,border=Round,filCol=7
                                     ,txts=[qlist!!i],typs=[Osite]
                                     ,audio=Just (auInd!!i)
                                     ,clEv=Choice i}) [0..] qConRecs
   in hCon:qCons 

genAnsCon :: Size -> Int -> Int -> Con
genAnsCon cvSz@(cW,_) conNum i = 
  let rec = makeAnsRec cvSz
      hcW = cW/8*3-20
      indY = 50
      spcX = 50
      tfsz = 50
      tps = [(hcW-spcX,indY),(hcW,indY),(hcW+spcX,indY)]
   in emCon{conID=conNum,cRec=rec,border=Round,borCol=1,filCol=6,txtPos=tps
           ,txtFsz=[tfsz,tfsz,tfsz],txtCos=[5,5,5]
           ,txts=["こ","た","ふ"]
           ,typs=[Normal,Normal,Normal]
           ,audio=Nothing
           ,clEv=Answer i}

makeAnsRec :: Size -> CRect
makeAnsRec (cW,cH) = let indX = cW/8; indY = cH/6
                         conW = cW-indX*2; conH = cH/8
                      in CRect indX (cH-indY) conW conH

makeConsRec :: Size -> Int -> [CRect]
makeConsRec (cW,cH) i 
  | i==4 = let indX = cW/8; indY = cH/10
               spaX = cW/16; spaY = cW/20
               conW = cW/3; conH = cH/5
               fstX = indX; sndX = fstX+conW+spaX
               fstY = cH/4+indY; sndY = conH+fstY+spaY
            in [CRect fstX fstY conW conH, CRect sndX fstY conW conH
               ,CRect fstX sndY conW conH, CRect sndX sndY conW conH]
  | otherwise = [] -- not yet for other i !!!
