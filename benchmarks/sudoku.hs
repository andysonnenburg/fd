{-# LANGUAGE RebindableSyntax #-}
module Main (main) where

import Criterion.Main
import Control.Monad (forM, forM_, sequence)
import Control.Monad.FD

import Data.List (transpose)

import Prelude hiding (Num (..), sequence)

solve :: [Term s] -> FDT s m [Int]
solve xs = do
  forM_ xs $ \ x -> do
    x #>= 1
    x #<= 9
  mapM_ distinct $ rows xs
  mapM_ distinct $ columns xs
  mapM_ distinct $ boxes xs
  forM xs label

rows :: [a] -> [[a]]
rows = chunk 9

columns :: [a] -> [[a]]
columns = transpose . rows

boxes :: [a] -> [[a]]
boxes = concatMap (map concat . transpose) . chunk 3 . chunk 3 . chunk 3

chunk :: Int -> [a] -> [[a]]
chunk _ [] = []
chunk n xs = ys : chunk n zs
  where
    (ys, zs) = splitAt n xs

problem :: FDT s m [Term s]
problem =
  sequence
  [ int 8, var, var, var, var, int 5, var, var, var,
    var, int 1, int 2, int 3, var, var, int 6, var, var,
    var, int 4, int 5, int 6, var, var, var, int 2, var,
    var, int 7, int 8, var, var, var, var, var, int 1,
    var, var, var, var, int 9, var, var, var, var,
    int 9, var, var, var, var, var, int 8, int 7, var,
    var, int 2, var, var, var, int 6, int 5, int 4, var,
    var, var, int 4, var, var, int 3, int 2, int 1, var,
    var, var, var, int 1, var, var, var, var, int 9 ]
  where
    int = return
    var = freshTerm

main :: IO ()
main = defaultMain [bench "sudoku" $ nfIO $ runFDT $ problem >>= solve]
