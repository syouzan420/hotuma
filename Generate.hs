module Generate(genLtQuest,genCons,genAnsCon) where

import qualified Data.Map as M
import Libs (selectData,getRan)
import Initialize (emCon)
import Define (State(..),Con(..),Question(..),Size,CRect(..)
              ,Bord(..),Event(..),TxType(..),QSource
              ,ltQuestSrc)

genLtQuest :: Int -> Int -> QSource -> IO ((Question,QSource),Int)
genLtQuest g lv qs = do
  let aqn = lv+3 -- avalable question numbers 
      qn = 4 + lv `div` 8 -- question numbers
  (an,g') <- selectData 1 g (M.toList qs) 
  let ans = head an
  let nqs = M.delete (fst ans) qs 
  let aqs = M.delete (fst ans) ltQuestSrc 
  (ai,g'') <- getRan qn g' 
  (iqlist,ng) <- selectData (qn-1) g'' (M.toList aqs) 
  let iqlist' = insertToList ai ans iqlist
  let (auInd,qlist) = unzip iqlist'
  return ((Question (map (:[]) qlist) auInd ai,nqs),ng)

insertToList :: Int -> a -> [a] -> [a]
insertToList i tg lst = take i lst ++ [tg] ++ drop i lst

genCons :: Size -> Question -> [Con]
genCons cSz@(cW,cH) (Question qlist auInd ai) = 
  let qLen = length qlist
      aText = qlist!!ai
      aAudio = auInd!!ai
      hConRec = CRect (cW/8) (cH/10) (cW/3) (cH/5)
      qConRecs = makeConsRec cSz qLen
      ext = fromIntegral (div (qLen-3) 2)
      ifsz = 50
      fsz = floor (fromIntegral ifsz - ext*8)
      itpX = 40
      tpX = itpX - (fromIntegral fsz/9)*4*ext
      tpY = 60
      
      hCon = emCon{conID=0,cRec=hConRec,border=Round,filCol=5,txtPos=[(itpX,tpY)]
                ,txtFsz=[ifsz],txtCos=[1],txts=[aText],typs=[Normal]
                ,audio=Just aAudio,clEv=NoEvent}
      qCons = zipWith (\i rec -> hCon{conID=i+1,cRec=rec,border=Round,filCol=7
                                     ,txtPos=[(tpX,tpY)]
                                     ,txtFsz=[fsz]
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
makeConsRec (cW,cH) i =
  let bi = div i 2 -- the numbers of the bottom lined cons 
      biD = fromIntegral bi
      rm = mod i 2 -- the reminder (0 or 1)
      ti = bi + rm -- the numbers of the top lined cons
      tiD = fromIntegral ti
      cntX = cW/2  -- center x
      spX = cW/16 - fromIntegral (div (i-3) 2)
      spY = cW/20
      mgnX = spX*2
      mgnY = cH/10
      conW = (cW - mgnX*2 - spX*(tiD-1))/tiD
      conH = cH/5 - fromIntegral (div (i-3) 2) *3
      psX n = mgnX + (conW + spX)* fromIntegral n
      mgnBX = (cW - (conW*biD + spX*(biD-1)))/2
      psBX n = mgnBX + (conW + spX)* fromIntegral n
      tpsY = cH/4+mgnY
      bpsY = tpsY + conH + spY
      tps = map (\n -> (psX n,tpsY)) [0..(ti-1)]
      bps = map (\n -> (psBX n,bpsY)) [0..(bi-1)]
      recs = map (\(px,py) -> CRect px py conW conH) (tps ++ bps)
   in recs 

