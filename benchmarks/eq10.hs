{-# LANGUAGE RebindableSyntax #-}
module Main (main) where

import Control.Monad (forM_, liftM, replicateM)
import Control.Monad.FD
import Criterion.Main

import Data.Array
import Data.Traversable (forM)

import Prelude hiding (Num (..), max, min)

eq10 :: IO [Array Int Int]
eq10 = runFDT $ do
  x <- liftM (listArray (1, 7)) $ replicateM 7 freshTerm
  forM_ (elems x) (#>= 0)
  forM_ (elems x) (#<= 10)
  98527*x!1 + 34588*x!2 + 5872*x!3 + 59422*x!5 + 65159*x!7 #=
    1547604 + 30704*x!4 + 29649*x!6
  98957*x!2 + 83634*x!3 + 69966*x!4 + 62038*x!5 + 37164*x!6 + 85413*x!7 #=
    1823553 + 93989*x!1
  900032 + 10949*x!1 + 77761*x!2 + 67052*x!5 #=
    80197*x!3 + 61944*x!4 + 92964*x!6 + 44550*x!7
  73947*x!1 + 84391*x!3 + 81310*x!5 #=
    1164380 + 96253*x!2 + 44247*x!4 + 70582*x!6 + 33054*x!7
  13057*x!3 + 42253*x!4 + 77527*x!5 + 96552*x!7 #=
    1185471 + 60152*x!1 + 21103*x!2 + 97932*x!6
  1394152 + 66920*x!1 + 55679*x!4 #=
    64234*x!2 + 65337*x!3 + 45581*x!5 + 67707*x!6 + 98038*x!7
  68550*x!1 + 27886*x!2 + 31716*x!3 + 73597*x!4 + 38835*x!7 #=
    279091 + 88963*x!5 + 76391*x!6
  76132*x!2 + 71860*x!3 + 22770*x!4 + 68211*x!5 + 78587*x!6 #=
    480923 + 48224*x!1 + 82817*x!7
  519878 + 94198*x!2 + 87234*x!3 + 37498*x!4 #=
    71583*x!1 + 25728*x!5 + 25495*x!6 + 70023*x!7
  361921 + 78693*x!1 + 38592*x!5 + 38478*x!6 #=
    94129*x!2 + 43188*x!3 + 82528*x!4 + 69025*x!7
  forM x label

main :: IO ()
main = defaultMain [bench "eq10" $ nfIO eq10]
