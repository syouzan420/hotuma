module Initialize where

import qualified Data.Map as M
import Define(State(..),Switch(..),Con(..),CRect(..),Bord(..)
             ,Event(..),Stage(..),TxType(..),Score(..),MType(..),ltQuestSrc)

initState :: State
initState = State {stage=Nothing
                  ,mtype=NoMission
                  ,level=0
                  ,score=Score 0 0
                  ,hiscs=[0,0,0,0,0,0,0,0]
                  ,quest=Nothing
                  ,seAu=Nothing
                  ,cons=[testCon]
                  ,gaus=[]
                  ,qsrc=ltQuestSrc
                  ,cli=[]
                  ,rgn=0
                  ,swc=initSwitch
                  ,db=""
                  }

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
              ,txtFsz = [20]
              ,txtCos = [1]
              ,txts = ["こんにちは\n元氣ですか？"]
              ,typs = [Normal]
              ,picSize = []
              ,picNums = []
              ,audio = Nothing
              ,clEv = Start
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
            }
