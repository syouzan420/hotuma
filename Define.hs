{-# LANGUAGE OverloadedStrings #-}
module Define where

import Haste(JSString)
import qualified Data.Map as M

type Pos = (Double,Double)
type Size = (Double,Double)
type Fsize = Int          --Font Size
type QSource = M.Map Int Char

type CInfo = ((Double,Double),(Double,Double))
  -- canvasWidth, canvasHeight, clientRectWidth, clientRectHeight

data CRect = CRect Double Double Double Double deriving (Eq,Show)

data Bord = NoBord | Rigid | Round | Circle deriving (Eq,Show)

data TxType = Normal | Osite deriving (Eq,Show)

data Stage = StgLetter Int | StgWord Int deriving (Eq,Show)

data MType = NoMission | Mi | Qu deriving (Eq,Show)

data Event = NoEvent | Intro | Explain Int | Start | Quest Stage | Choice Int 
           | Answer Int | Study | Learn Int Int | Summary Int | Mission Int Int Int
           | ChClick Int | MEnd Int Int | IsReset | ScrReset     deriving (Eq,Show)

data Score = Score {miss :: !Int, time :: !Int} deriving (Eq,Show,Read)

data Gauge = Gauge {gti :: !String, gps :: !Pos, gsz :: !Size
                   ,gmx :: !Int, gcu :: !Int} deriving (Eq,Show)
--gti: gauge title, gps: gauge position, gsz: gauge size
--gmx: gauge max num, gcu: gauge current num

data BMode = Ko | Ne Int | NoB deriving (Eq,Show)

data BEvent = NoBEvent | GetNe Int | GetOs Int Int deriving (Eq,Show)

data BKo = BKo !CRect !BEvent deriving (Eq,Show)

data BNe = BNe !CRect !BEvent deriving (Eq,Show)

data Board = Board {bMode :: !BMode
                   ,bPos :: !Pos
                   ,bScale :: !Double} deriving (Eq,Show) 

data Question = Question {quests :: ![String]
                         ,audios :: ![Int]
                         ,aInd :: !Int -- answer index
                         } deriving (Eq,Show)

--container
data Con = Con {conID :: !Int
               ,cRec :: !CRect
               ,border :: !Bord
               ,borCol :: !Int -- border color number
               ,filCol :: !Int -- fill color
               ,txtPos :: ![Pos]
               ,picPos :: ![Pos]
               ,txtFsz :: ![Fsize] -- text font sizes
               ,txtCos :: ![Int] -- text color indexes
               ,txts :: ![String]
               ,typs :: ![TxType] -- text types (normal or osite)
               ,picSize :: ![Size]
               ,picNums :: ![Int] -- picture indexes
               ,audio :: !(Maybe Int) -- audio index when (show or pressed)
               ,clEv :: !Event -- event when clicked
               } deriving (Eq,Show)

data LSA = Save | Load | Remv deriving (Eq,Show)  -- local storage actions 

data State = State {stage :: !(Maybe Stage)
                   ,mtype :: !MType -- mission type (Quest or Mission)
                   ,level :: !Int -- mission level
                   ,score :: !Score
                   ,hiscs :: ![Int] -- high scores
                   ,quest :: !(Maybe Question)
                   ,seAu :: !(Maybe Int) -- sound index
                   ,cons :: ![Con]
                   ,gaus :: ![Gauge] -- gauges
                   ,board :: !Board
                   ,qsrc :: !QSource -- quest source
                   ,cli :: ![Int] -- clear indexes (learning stages)
                   ,rgn :: !Int -- Random Number Generator
                   ,swc :: !Switch
                   ,db :: !String    --for debug
                   } deriving (Eq,Show)

data Switch = Switch { ita:: !Bool,    -- Is timer active?
                       ils:: !Bool,    -- Leave Stage?
                       igc:: !Bool,    -- Game Clear?
                       itc:: !Bool,     -- Touch Is True?
                       ini:: !Bool,     -- No Input?
                       ias:: !Bool      -- audio start?
                     } deriving (Eq, Show)

initBKoW :: Double
initBKoW = 60

initBKoH :: Double
initBKoH = 60

initBNeW :: Double
initBNeW = 50

initBNeH :: Double
initBNeH = 50


miy :: Int -- map initial y
miy = 2

tiy :: Int -- text initial relative y
tiy = 2

wg, hg, wt, ht :: Double 
wg = 16; hg = 20; wt = 28; ht = 24 -- grid width & height , tategaki letters width & height

nfs, rfs :: Int
nfs = 20; rfs = 8 -- normal font size, rubi font size

cvT :: Double
cvT = 10  --trim(yohaku)

mTimeLimit :: Int
mTimeLimit = 30

qTimeLimit :: Int
qTimeLimit = 150

clearScore :: Int
clearScore = 15

imgfile :: String
imgfile = "Images/img"

wstfile :: String
wstfile = "Images/Wst/wst"

wstAuFile :: String
wstAuFile = "Audio/os"

seFile :: String
seFile = "Audio/se"

storeName :: String
storeName = "hotumaSave"

ltQuestSrc :: QSource 
ltQuestSrc = M.fromList $ zip [0..] "あかはなまいきひにみうくふぬむえけへねめおこほのもとろそよをてれせゑつるすゆんちりしゐたらさやわ"

wstIndex :: String
wstIndex = "あいうえおxkhnmtrsy かはなまきひにみくふぬむけへねめこほのもとろそよをてれせゑつるすゆんちりしゐたらさやわ゛阿和宇吾付須被意百雄間波が9穂ぞ話葉ざぐび緒ど3ずばぶぎべ補芽1府場じ個我ご図時曾火日だ座羽4馬部祖炉具語づ後子男でぜ出裳美"

extStages :: [[Int]]
extStages = [[0,1],[0,2],[0,1,2,3],[1,3],[2,4],[2,3,4,5],[3,5],[4,6],[4,5,6,7],[5,7],[6,7]]

expLst :: [String]
expLst = ["ホツマツタヱは\rわたしたちの くに にふるくからある\rもじ で かかれた\rものがたりです","ホツマツタヱ が\rどのくらゐ\rふるくから あるのか\rよくわかって\rゐません","ものがたり は\rごもじ と ななもじ からなる わか の\rリズムで\rかかれてゐます","そこには\rにほん の なりたち\rことば の ゆらい\rれきし など が\rかかれてゐます","にほん かくち の\rじんじゃ に のこる\rいひつたへ や\rひみつ を とく\rてがかりにも なります","ここで\rつかはれてゐる\rもじは\rヲシテ\rと よばれてゐます","まづは\rヲシテ をまなんで\rホツマツタヱ の\rぼうけん を\rはじめましょう"]
