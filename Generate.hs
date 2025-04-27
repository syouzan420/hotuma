module Generate(genLtQuest,genCons,genAnsCon,genSCons,genLCons
               ,genSumCons,genMission,genNoticeCon,genStartCons
               ,genBackCon,genMGauges) where

import qualified Data.Map as M
import Data.Maybe (fromMaybe)
import Libs (selectData,getRan)
import Initialize (emCon)
import Define (State(..),Con(..),Question(..),Size,CRect(..),Gauge(..)
              ,Bord(..),Event(..),TxType(..),QSource,Stage(..)
              ,ltQuestSrc,clearScore,mTimeLimit)

stageChars :: Int -> (Int,[(Int,Char)])
stageChars stg =
  let dvTwo = stg `div` 2
      mdTwo = stg `mod` 2
      psi = if mdTwo==0 then dvTwo*12 else dvTwo*12+5
      tkn = if mdTwo==0 then 5 else 7
      taso = take tkn (drop psi (M.toList ltQuestSrc)) -- target associate list
   in (tkn,taso) 

genMission :: Int -> Int -> Int -> IO (Question,Int)
genMission g stg pai = do 
  let (tkn,taso) = stageChars stg
      qs = M.fromList taso
      qs' = if pai==(-1) then qs else M.delete pai qs
          --a list which eliminates the previous answer from the stage char list 
  (an,g') <- selectData 1 g (M.toList qs')            
  let ans = head an
      nqs = M.delete (fst ans) qs'
  (ai,g'') <- getRan 4 g'
  (iqlist,ng) <- selectData 3 g'' (M.toList nqs)
  let iqlist' = insertToList ai ans iqlist
      (auInd,qlist) = unzip iqlist'
  return (Question (map (:[]) qlist) auInd ai,ng) 

genLtQuest :: Int -> Int -> QSource -> IO ((Question,QSource),Int)
genLtQuest g lv qs = do
  let qn = 4 + lv `div` 8 -- question numbers
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
  let (tkn,taso) = stageChars stg
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
                   ,clEv=Mission stg (-1) 0} 
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
      bCon = genBackCon cvSz (tkn+3) Study
   in sumCons++[btCon,noticeCon0,noticeCon1,bCon] 

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

genSCons :: Size -> [Int] -> [Int] -> [Con]
genSCons cvSz clind hscrs =
  let tpX = 40; tpY = 60
      fsz = 50
      fsD = fromIntegral fsz
      sConRecs = map (makeSConRec cvSz) [0..7]
      lList = "あいふへもをすし"
      isclear n = n `elem` clind
      makeFlCol n = if isclear n then 9 else 7
      txps n = if isclear n then [(tpX,tpY),(tpX-fsD/2,tpY)] else [(tpX,tpY)]
      txfs n = if isclear n then [fsz,fsz `div` 2] else [fsz]
      txco n = if isclear n then [1,1] else [1]
      txs n = if isclear n then [[lList!!n],show (hscrs!!n)] else [[lList!!n]]
      typ n = if isclear n then [Osite,Normal] else [Osite]
   in zipWith (\i rec -> emCon{conID=i,cRec=rec,border=Round,filCol=makeFlCol i
                              ,txtPos=txps i,txtFsz=txfs i,txtCos=txco i
                              ,txts=txs i,typs=typ i
                              ,clEv=Learn i 0}) [0..] sConRecs

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

genStartCons :: Size -> [Con]
genStartCons (cW,cH) =
  let mgnX = cW/8; mgnY =cH/12
      conW = cW*3/4; conH = cH*3/8
      fsz = 40
      fsD = fromIntegral fsz
      stRecs = [CRect mgnX mgnY conW conH,CRect mgnX (mgnY*2+conH) conW conH]
      txts n = if n==0 then "ヲシテもじを おぼへやう！"
                       else "チャレンジもんだい！"
      flco n = if n==0 then 7 else 9
      clev n = if n==0 then Study else Quest (StgLetter 0) 
   in zipWith (\i rec -> emCon{conID=i,cRec=rec,border=Round,borCol=1
                          ,filCol=flco i
                          ,txtPos=[(cW*2/3-mgnX-fsD/2,fsD)],txtFsz=[fsz]
                          ,txtCos=[1],txts=[txts i],typs=[Normal],clEv=clev i})
                                                                [0,1] stRecs

genNoticeCon :: Size -> Int -> Int -> String -> Event -> Con
genNoticeCon (cW,cH) i flco tx ev = 
  let mgnX = cW/3; mgnY = cH/6
      fsz = 40
      fsD = fromIntegral fsz
   in emCon{conID=i,cRec=CRect mgnX mgnY (cW-mgnX*2) (cH-mgnY*2)
           ,border=Round, borCol = 5, filCol = flco 
           ,txtPos=[(cW/2-mgnX-fsD/2,fsD*3)],txtFsz=[fsz],txtCos=[3]
           ,txts = [tx], typs=[Normal], clEv=ev}

genBackCon :: Size -> Int -> Event -> Con
genBackCon (cW,cH) i ev =
  let mgnX = cW/25; mgnY = cH/45 
      conW = cW/12
      fsz = 32
      fsD = fromIntegral fsz
   in emCon{conID=i,cRec=CRect mgnX mgnY conW conW,border=Circle
           ,borCol=0,filCol=7,txtPos=[(0,fsD/3*2)],txtFsz=[fsz],txtCos=[1]
           ,txts=["←"],typs=[Normal],clEv=ev}

genMGauges :: Size -> Int -> Int -> [Gauge]
genMGauges (cW,cH) sc tm =
  let mgnX = cW/8; mgnY = cH/20
      spX = cW/5
      gW = cW/4; gH = 10;
      gau0 = Gauge "SCORE" (mgnX,mgnY) (gW,gH) clearScore sc 
      gau1 = Gauge "TIME" (mgnX+gW+spX,mgnY) (gW,gH) mTimeLimit (mTimeLimit-tm)
   in [gau0,gau1]
