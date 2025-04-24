{-# LANGUAGE OverloadedStrings #-}
module Define where

import Haste(JSString)

type Pos = (Double,Double)
type Size = (Double,Double)
type Fsize = Int          --Font Size

type CInfo = ((Double,Double),(Double,Double))
  -- canvasWidth, canvasHeight, clientRectWidth, clientRectHeight

data CRect = CRect Double Double Double Double deriving (Eq,Show)

data Bord = NoBord | Rigid | Round deriving (Eq,Show)

data TxType = Normal | Osite deriving (Eq,Show)

data Stage = StgLetter Int | StgWord Int deriving (Eq,Show)

data Event = NoEvent | Quest Stage | Choice Int | Answer Int deriving (Eq,Show)

data Score = Score {miss :: !Int, time :: !Int} deriving (Eq,Show)

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

data Button = Button {btnId :: !Int
                     ,btnCon :: !Con
                     ,clicked :: !Bool
                     } deriving (Eq,Show)


data LSA = Save | Load | Remv deriving (Eq,Show)  -- local storage actions 

data State = State {stage :: !(Maybe Stage)
                   ,score :: !Score
                   ,quest :: !(Maybe Question)
                   ,seAu :: !(Maybe Int) -- sound index
                   ,cons :: ![Con]
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

imgfile :: String
imgfile = "Images/img"

wstfile :: String
wstfile = "Images/Wst/wst"

wstAuFile :: String
wstAuFile = "Audio/os"

seFile :: String
seFile = "Audio/se"

ltQuestSrc :: String
ltQuestSrc = "あかはなまいきひにみうくふぬむえけへねめおこほのもとろそよをてれせゑつるすゆんちりしゐたらさやわ"

wstIndex :: String
wstIndex = "あいうえおxkhnmtrsy かはなまきひにみくふぬむけへねめこほのもとろそよをてれせゑつるすゆんちりしゐたらさやわ゛阿和宇吾付須被意百雄間波が9穂ぞ話葉ざぐび緒ど3ずばぶぎべ補芽1府場じ個我ご図時曾火日だ座羽4馬部祖炉具語づ後子男でぜ出裳美"
