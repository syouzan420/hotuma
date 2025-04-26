module Generate(genLtQuest,genCons,genAnsCon,genSCons,genLCons
               ,genSumCons,genMission,genMCons) where

import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Libs (selectData,getRan)
import Initialize (emCon)
import Define (State(..),Con(..),Question(..),Size,CRect(..)
              ,Bord(..),Event(..),TxType(..),QSource
              ,ltQuestSrc)

genMission :: Int -> Int -> IO (Question,Int)
genMission g stg = undefined

genMCons :: Size -> Question -> [Con]
genMCons cvSz q = undefined

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

genSumCons :: Size -> Int -> [Con]
genSumCons cvSz@(cW,cH) stg =
  let dvTwo = stg `div` 2
      mdTwo = stg `mod` 2
      psi = if mdTwo==0 then dvTwo*12 else dvTwo*12+5
      tkn = if mdTwo==0 then 5 else 7
      taso = take tkn (drop psi (M.toList ltQuestSrc)) -- target associate list
      sumConRecs = makeSumConsRec cvSz tkn 
      tpX = 20; tpY = 40 
      fsz = 45 
      hcW = cW/8*3-20
      indY = 50
      spcX = 50
      btfsz = 50
      btTps = [(hcW-spcX,indY),(hcW,indY),(hcW+spcX,indY)]
      sumCons = zipWith (\(i,(k,ch)) rec -> emCon{conID=i,cRec=rec
                   ,border=Round,borCol=4,filCol=9
                   ,txtPos=[(tpX,tpY)],txtFsz=[fsz],txtCos=[1]
                   ,txts=[[ch]],typs=[Osite]
                   ,clEv=ChClick k}) (zip [0..(tkn-1)] taso) sumConRecs
      btCon = emCon{conID=tkn,cRec=makeBtmRec cvSz
                   ,border=Round,borCol=1,filCol=6,txtPos=btTps
                   ,txtFsz=[btfsz,btfsz,btfsz],txtCos=[5,5,5]
                   ,txts=["は","じ","め"]
                   ,typs=[Normal,Normal,Normal]
                   ,audio=Nothing
                   ,clEv=Mission stg 0} 
      noticeCon0 = emCon{conID=tkn+1
                   ,cRec=CRect (cW/4*3) (cH/20) (cW/4) (cH/2)
                   ,txtPos=[(20,20)],txtFsz=[30],txtCos=[1]
                   ,txts=["もじを タップして かくにん してね"]
                   ,typs=[Normal]}
      noticeCon1 = emCon{conID=tkn+2
                   ,cRec=CRect (cW/5) (cH/10) (cW/4) (cH/2)
                   ,txtPos=[(20,20)],txtFsz=[30],txtCos=[1]
                   ,txts=["よければ もじあて を はじめやう"]
                   ,typs=[Normal]}
   in sumCons++[btCon,noticeCon0,noticeCon1] 

makeSumConsRec :: Size -> Int -> [CRect]
makeSumConsRec (cW,cH) tkn =
  let conW = cW/5; conH = cH/10
      mgnX = cW/9*4; mgnY = cH/60
      spY = cH/60 
   in map (\i -> CRect mgnX (mgnY+(conH+spY)*fromIntegral i) conW conH) [0..tkn]

genLCons :: Size -> Int -> Event -> [Con]
genLCons (cW,cH) oi ev = 
  let conW = cW/2; conH = cH/3 
      mgnX = cW/4; mgnY = cH/8
      spY = cH/10
      tpX = 50; tpY = 120
      fsz = 100
      lConRecs = [CRect mgnX mgnY conW conH,CRect mgnX (mgnY+conH+spY) conW conH]
      och = fromMaybe ' ' $ M.lookup oi ltQuestSrc 
   in zipWith (\(i,cn) rec -> emCon{conID=i,cRec=rec
                   ,border=if i==0 then NoBord else Round,borCol=4,filCol=cn
                   ,txtPos=[(tpX,tpY)],txtFsz=[fsz],txtCos=[1]
                   ,txts=[[och]],typs=[if i==0 then Normal else Osite]
                   ,clEv=if i==0 then NoEvent else ev}) [(0,5),(1,9)] lConRecs

genSCons :: Size -> [Int] -> [Con]
genSCons cvSz clind =
  let tpX = 40; tpY = 60
      fsz = 50
      sConRecs = map (makeSConRec cvSz) [0..7]
      lList = "あいふへもをすし"
      makeClEv n = if n `elem` clind then NoEvent else Learn n 0
   in zipWith (\i rec -> emCon{conID=i,cRec=rec,border=Round,filCol=7
                              ,txtPos=[(tpX,tpY)],txtFsz=[fsz],txtCos=[1]
                              ,txts=[[lList!!i]],typs=[Osite]
                              ,clEv=makeClEv i}) [0..] sConRecs

makeSConRec :: Size -> Int -> CRect 
makeSConRec (cW,cH) i =
  let conW = cW/3; conH = cH/6
      mgX = cW/8; mgY = cH/12
      spX = cW/10; spY = cH/16
      yi = i `div` 2
      xi = i `mod` 2
   in CRect (mgX+(conW+spX)*fromIntegral xi) (mgY+(conH+spY)*fromIntegral yi) conW conH

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
  let rec = makeBtmRec cvSz
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

makeBtmRec :: Size -> CRect
makeBtmRec (cW,cH) = let indX = cW/8; indY = cH/6
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

