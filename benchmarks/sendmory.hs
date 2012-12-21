{-# LANGUAGE RebindableSyntax #-}
module Main (main) where

import Control.Monad.FD
import Criterion.Main

import Data.Foldable (forM_)
import Data.Traversable (forM)

import Prelude hiding (Num (..), max, min)

sendmory :: IO [[Int]]
sendmory = runFDT $ do
  s <- freshTerm
  e <- freshTerm
  n <- freshTerm
  d <- freshTerm
  m <- freshTerm
  o <- freshTerm
  r <- freshTerm
  y <- freshTerm
  let xs = [s, e, n, d, m, o, r, y]
  forM_ xs $ \ x -> do
    x #>= 0
    x #<= 9
  s #/= 0
  m #/= 0
  distinct xs
  1000 * s + 100 * e + 10 * n + 1 * d +
    1000 * m + 100 * o + 10 * r + 1 * e #=
    10000 * m + 1000 * o + 100 * n + 10 * e + 1 * y
  forM xs label

main :: IO ()
main = defaultMain [bench "sendmory" $ nfIO sendmory]
