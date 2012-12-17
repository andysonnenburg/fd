{-# LANGUAGE RebindableSyntax #-}
module Main (main) where

import Criterion.Main
import Control.Monad (liftM)
import Control.Monad.FD

import Data.Array
import Data.Foldable
import Data.Traversable

import Prelude hiding (Num (..), sequence)

solve :: Array (Int, Int) (Term s) -> FDT s m (Array (Int, Int) Int)
solve xs = do
  domains xs
  distinctRows xs
  distinctColumns xs
  distinctBlocks xs
  for xs label

domains :: Foldable f => f (Term s) -> FDT s m ()
domains xs =
  for_ xs $ \ x -> do
    x #>= 1
    x #<= 9

distinctRows :: Array (Int, Int) (Term s) -> FDT s m ()
distinctRows xs =
  for_ (range (1, 9)) $ \ r ->
    distinct $ map (\ c -> xs!(r, c)) $ range (1, 9)

distinctColumns :: Array (Int, Int) (Term s) -> FDT s m ()
distinctColumns xs =
  for_ (range (1, 9)) $ \ c ->
    distinct $ map (\ r -> xs!(r, c)) $ range (1, 9)

distinctBlocks :: Array (Int, Int) (Term s) -> FDT s m ()
distinctBlocks xs = do
  distinct $ map (xs!) $ range ((1, 1), (3, 3))
  distinct $ map (xs!) $ range ((1, 4), (3, 6))
  distinct $ map (xs!) $ range ((1, 7), (3, 9))

  distinct $ map (xs!) $ range ((4, 1), (6, 3))
  distinct $ map (xs!) $ range ((4, 4), (6, 6))
  distinct $ map (xs!) $ range ((4, 7), (6, 9))

  distinct $ map (xs!) $ range ((7, 1), (9, 3))
  distinct $ map (xs!) $ range ((7, 4), (9, 6))
  distinct $ map (xs!) $ range ((7, 7), (9, 9))

problem :: FDT s m (Array (Int, Int) (Term s))
problem =
  liftM (listArray ((1, 1), (9, 9))) $ sequence
  [ i 8, v, v, v, v, i 5, v, v, v,
    v, i 1, i 2, i 3, v, v, i 6, v, v,
    v, i 4, i 5, i 6, v, v, v, i 2, v,
    v, i 7, i 8, v, v, v, v, v, i 1,
    v, v, v, v, i 9, v, v, v, v,
    i 9, v, v, v, v, v, i 8, i 7, v,
    v, i 2, v, v, v, i 6, i 5, i 4, v,
    v, v, i 4, v, v, i 3, i 2, i 1, v,
    v, v, v, i 1, v, v, v, v, i 9 ]
  where
    i = return
    v = freshTerm

main :: IO ()
main = defaultMain [bench "sudoku" $ nfIO $ runFDT $ problem >>= solve]
