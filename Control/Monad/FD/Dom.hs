module Control.Monad.FD.Dom
       ( Dom
       , fromBounds
       , fromIntSet
       , full
       , empty
       , null
       , toList
       , deleteLT
       , deleteGT
       , intersection
       , findMin
       , findMax
       , singleton
       , sizeLE
       ) where

import Prelude hiding (max, min, null)
import qualified Prelude

import Control.Monad.FD.IntSet (IntSet)
import qualified Control.Monad.FD.IntSet as IntSet
import Control.Monad.FD.Pruning (Pruning)
import qualified Control.Monad.FD.Pruning as Pruning

data Dom
  = Bounds Int Int
  | IntSet IntSet

fromBounds :: Int -> Int -> Dom
fromBounds = Bounds

fromIntSet :: IntSet -> Dom
fromIntSet = IntSet

full :: Dom
full = Bounds minBound maxBound

empty :: Dom
empty = Bounds maxBound minBound

null :: Dom -> Bool
null (Bounds min max) = min > max
null (IntSet xs) = IntSet.null xs

toList :: Dom -> [Int]
toList (Bounds min max) = [min .. max]
toList (IntSet xs) = IntSet.toList xs

deleteLT :: Int -> Dom -> Maybe (Dom, Pruning)
deleteLT i (Bounds min max)
  | i > max = Just (empty, Pruning.val)
  | i > min = Just (Bounds i max, if i == max then Pruning.val else Pruning.min)
  | otherwise = Nothing

deleteGT :: Int -> Dom -> Maybe (Dom, Pruning)
deleteGT i (Bounds min max)
  | i < min = Just (empty, Pruning.val)
  | i < max = Just (Bounds min i, if i == min then Pruning.val else Pruning.max)
  | otherwise = Nothing

intersection :: Dom -> Dom -> Maybe (Dom, Pruning)
intersection d (Bounds min max) =
  (deleteLT min `then'` deleteGT max) d

findMin :: Dom -> Int
findMin (Bounds min max)
  | min <= max = min
  | otherwise = error "findMin: empty domain has no minimal element"
findMin (IntSet xs) = IntSet.findMin xs

findMax :: Dom -> Int
findMax (Bounds min max)
  | max >= min = max
  | otherwise = error "findMax: empty domain has no maximal element"
findMax (IntSet xs) = IntSet.findMax xs

singleton :: Int -> Dom
singleton i = Bounds i i

sizeLE :: Int -> Dom -> Bool
sizeLE i = Prelude.null . drop i . toList

then' :: (a -> Maybe (a, Pruning)) ->
         (a -> Maybe (a, Pruning)) ->
         a -> Maybe (a, Pruning)
then' f g a =
  case f a of
    Nothing -> g a
    m@(Just (a', p)) -> case g a' of
      Nothing -> m
      Just (a'', p') -> Just (a'', Pruning.join p p')
