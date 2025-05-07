module Initialize where

import qualified Data.Map as M
import Define(State(..),Switch(..),Con(..),CRect(..),Bord(..)
             ,Board(..),BMode(..),BEvent(..)
             ,Event(..),Stage(..),TxType(..),Score(..),MType(..),ltQuestSrc)

initState :: State
initState = State {stage=Nothing
                  ,mtype=NoMission
                  ,level=0
                  ,score=Score 0 0
                  ,hiscs=replicate 19 0
                  ,quest=Nothing
                  ,seAu=Nothing
                  ,cons=[testCon]
                  ,board=initBoard
                  ,gaus=[]
                  ,qsrc=ltQuestSrc
                  ,cli=[]
                  ,rgn=0
                  ,swc=initSwitch
                  ,db=""
                  }

initBoard :: Board
initBoard = Board NoB (0,0) 1 0 NoEvent

initSwitch :: Switch
initSwitch = Switch {ita=False
                    ,ils=False
                    ,igc=False
                    ,itc=False
                    ,ini=False
                    ,ias=False
                    }

testCon :: Con
testCon = Con {conID = 0
              ,cRec = CRect 80 100 200 370 
              ,border = Round
              ,borCol = 0
              ,filCol = 5
              ,txtPos = [(100,30)]
              ,picPos = []
              ,txtFsz = [30]
              ,txtCos = [1]
              ,txts = ["こんにちは\n元氣ですか？"]
              ,typs = [Normal]
              ,picSize = []
              ,picNums = []
              ,audio = Nothing
              ,clEv = Intro 
              ,visible = True
              ,enable = True
              }

emCon :: Con
emCon = Con {conID = 0
            ,cRec = CRect 0 0 10 10
            ,border = NoBord
            ,borCol = 0
            ,filCol = 5
            ,txtPos = []
            ,picPos = []
            ,txtFsz = []
            ,txtCos = []
            ,txts = []
            ,typs = []
            ,picSize = []
            ,picNums = []
            ,audio = Nothing
            ,clEv = NoEvent
            ,visible = True
            ,enable = True
            }
