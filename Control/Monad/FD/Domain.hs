module Control.Monad.FD.Domain
       ( Domain
       , fromBounds
       , fromIntSet
       , full
       , toList
       , deleteLT
       , deleteGT
       , intersection
       , lookupMin
       , lookupMax
       , singleton
       ) where

import Control.Applicative
import Control.Monad

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Prelude hiding (max, min)
import qualified Prelude

data Domain = Domain (Maybe IntSet) Int Int

fromBounds :: Int -> Int -> Domain
fromBounds = Domain Nothing

fromIntSet :: IntSet -> Domain
fromIntSet xs = Domain (Just xs) (IntSet.findMin xs) (IntSet.findMax xs)

full :: Domain
full = Domain Nothing minBound maxBound

toList :: Domain -> [Int]
toList (Domain (Just xs) _ _) = IntSet.toList xs
toList (Domain Nothing min max) = [min .. max]

deleteLT :: Int -> Domain -> Maybe Domain
deleteLT i (Domain Nothing min max)
  | i > min = Just $ Domain Nothing i max
  | otherwise = Nothing
deleteLT i (Domain (Just xs) _ _) = fromIntSet <$> xs'
  where
    xs' = case IntSet.splitMember i xs of
      (lt, _, _) | IntSet.null lt -> Nothing
      (_, True, gt) -> Just $ IntSet.insert i gt
      (_, False, gt) -> Just gt

deleteGT :: Int -> Domain -> Maybe Domain
deleteGT i (Domain Nothing min max)
  | i < max = Just $ Domain Nothing min i
  | otherwise = Nothing
deleteGT i (Domain (Just xs) _ _) = fromIntSet <$> xs'
  where
    xs' = case IntSet.splitMember i xs of
      (_, _, gt) | IntSet.null gt -> Nothing
      (lt, True, _) -> Just $ IntSet.insert i lt
      (lt, False, _) -> Just $ lt

intersection :: Domain -> Domain -> Maybe Domain
intersection d (Domain Nothing min max) =
  appendBinds (deleteGT max) (deleteLT min) d
intersection (Domain Nothing min max) d@(Domain (Just _) _ _) =
  appendBinds (deleteGT max) (deleteLT min) d <|> pure d
intersection (Domain (Just xs) _ _) (Domain (Just xs') _ _)
  | xs == xs'' = Nothing
  | otherwise = Just $ fromIntSet xs''
  where
    xs'' = IntSet.intersection xs xs'

lookupMin :: Domain -> Maybe Int
lookupMin (Domain (Just xs) _ _) | IntSet.null xs = Nothing
lookupMin (Domain _ min _) = Just min

lookupMax :: Domain -> Maybe Int
lookupMax (Domain (Just xs) _ _) | IntSet.null xs = Nothing
lookupMax (Domain _ _ max) = Just max

singleton :: Int -> Domain
singleton i = Domain (Just (IntSet.singleton i)) i i

appendBinds :: MonadPlus m => (a -> m a) -> (a -> m a) -> a -> m a
appendBinds f g a = (f a `mplus` return a) >>= g
