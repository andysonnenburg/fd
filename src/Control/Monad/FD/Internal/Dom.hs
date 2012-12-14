module Control.Monad.FD.Internal.Dom
       ( Dom
       , fromBounds
       , full
       , empty
       , null
       , toList
       , deleteLT
       , deleteGT
       , findMin
       , findMax
       , singleton
       , isVal
       ) where

import Data.Ix (range)
import Data.Monoid (mempty)

import Prelude hiding (max, min, null)
import qualified Prelude

import Control.Monad.FD.Internal.Pruning (Pruning)
import qualified Control.Monad.FD.Internal.Pruning as Pruning
import Control.Monad.FD.Internal.IntMap.Lazy (IntMap)
import qualified Control.Monad.FD.Internal.IntMap.Lazy as IntMap

newtype Dom = Dom { getDom :: IntMap Int }

fromBounds :: Int -> Int -> Dom
fromBounds min max = Dom $ IntMap.singleton min max

full :: Dom
full = fromBounds minBound maxBound

empty :: Dom
empty = Dom mempty

null :: Dom -> Bool
null = IntMap.null . getDom

toList :: Dom -> [Int]
toList = concatMap range . IntMap.toList . getDom

deleteLT :: Int -> Dom -> Maybe (Dom, Pruning)
deleteLT i (Dom dom)
  | IntMap.null dom = Nothing
  | otherwise = case IntMap.lookupLT i dom of
    Nothing -> Nothing -- i <= minimum
    Just (min, max) -> case compare i max of -- min < i
      GT -> case IntMap.deleteLE max dom of -- min <= max < i <= min'
        gt | isVal (Dom gt) -> Just (Dom gt, Pruning.val)
           | otherwise -> Just (Dom gt, Pruning.min)
      EQ -> case IntMap.deleteLE min dom of -- min < i == max
        gt | IntMap.null gt -> Just (singleton max, Pruning.val)
           | otherwise -> Just (Dom $ IntMap.insert max max gt, Pruning.min)
      LT -> case IntMap.deleteLE min dom of -- min < i < max
        gt -> Just (Dom $ IntMap.insert i max gt, Pruning.min)

deleteGT :: Int -> Dom -> Maybe (Dom, Pruning)
deleteGT i (Dom dom)
  | IntMap.null dom = Nothing
  | otherwise = case IntMap.lookupLE i dom of
    Nothing -> Just (empty, Pruning.val) -- i < minimum
    Just (min, max) -> case (compare i min, compare i max) of -- min <= i
      (EQ, EQ) -> case IntMap.split min dom of -- min == i == max
        (lt, gt) -> case (IntMap.null lt, IntMap.null gt) of
          (_, True) -> Nothing
          (True, False) -> Just (singleton min, Pruning.val)
          (False, False) -> Just (Dom $ IntMap.insert min min lt, Pruning.max)
      (EQ, _ {- LT -}) -> case IntMap.deleteGE min dom of -- min == i < max
        lt | IntMap.null lt -> Just (singleton min, Pruning.val)
           | otherwise -> Just (Dom $ IntMap.insert min min lt, Pruning.max)
      (_ {- GT -}, LT) -> case IntMap.deleteGE min dom of -- min < i < max
        lt -> Just (Dom $ IntMap.insert min i lt, Pruning.max)
      (_ {- GT -}, _) -> case IntMap.split max dom of -- min < max <= i
        (lt, gt) | IntMap.null gt -> Nothing
                 | otherwise -> Just (Dom lt, Pruning.max)

findMin :: Dom -> Int
findMin = fst . IntMap.findMin . getDom

findMax :: Dom -> Int
findMax = snd . IntMap.findMax . getDom

singleton :: Int -> Dom
singleton i = Dom $ IntMap.singleton i i

isVal :: Dom -> Bool
isVal (Dom dom) = case IntMap.toList dom of
  [] -> True
  [(min, max)] | min == max -> True
  _ -> False
