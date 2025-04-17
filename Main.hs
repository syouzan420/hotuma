import Haste (setTimer,Interval(Once,Repeat))
import Haste.Events (onEvent,preventDefault,KeyEvent(..),KeyData(..),
                     MouseEvent(..),MouseData(..),TouchEvent(..),TouchData(..))
import Haste.DOM (document,elemById,fromElem)
import Data.IORef(newIORef,readIORef,writeIORef)
import Loop (inputLoop,mouseClick)
import Browser (getCanvasInfo,cvRatio,tcStart,tcEnd,touchIsTrue,setBmps,setAudio)
import Output (startGame)
import Define (State(..))
import Initialize (initState)

main :: IO ()
main = do
  bmps <- setBmps
  aus <- setAudio
  Just ce <- elemById "canvas"
  Just c <- fromElem ce
  ci <- getCanvasInfo c
  state <- newIORef initState 
  startGame c ci bmps initState 
  onEvent ce Click $ \(MouseData xy _ _) -> do
    readIORef state >>= mouseClick c ci bmps aus xy >>= writeIORef state
  onEvent ce TouchStart $ \(TouchData {}) -> do
    readIORef state >>= tcStart >>= writeIORef state
  onEvent ce TouchEnd $ \(TouchData {}) -> do
    readIORef state >>= touchIsTrue >>= writeIORef state
    setTimer (Once 100) $ readIORef state >>= tcEnd >>= writeIORef state
    return ()
--  setTimer (Repeat 50) $
--    readIORef state >>= timerEvent c ci bmps >>= writeIORef state
  return ()
