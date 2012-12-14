module Control.Monad.FD.Internal.Dom
       ( Dom
       , full
       , empty
       , fromBounds
       , singleton
       , findMin
       , findMax
       , null
       , isVal
       , deleteLT
       , deleteGT
       , retainAll
       , toList
       ) where

import Data.Foldable (foldMap)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Semigroup (Option (Option), getOption)

import Control.Monad.FD.Internal.Pruning (Pruning)
import qualified Control.Monad.FD.Internal.Pruning as Pruning

import Prelude hiding (min, max, null)
import qualified Prelude

data Dom = Dom Min Max (Maybe IntSet) deriving Show

type Min = Int
type Max = Int

full :: Dom
full = fromBounds minBound maxBound

empty :: Dom
empty = fromBounds maxBound minBound

fromBounds :: Min -> Max -> Dom
fromBounds min max = Dom min max Nothing

singleton :: Int -> Dom
singleton x = Dom x x Nothing

fromIntSet :: IntSet -> Dom
fromIntSet set =
  Dom
  (maybe maxBound fst $ IntSet.minView set)
  (maybe minBound fst $ IntSet.maxView set)
  (Just set)

findMin :: Dom -> Min
findMin (Dom min _ _) = min

findMax :: Dom -> Max
findMax (Dom _ max _) = max

null :: Dom -> Bool
null (Dom min max _) = min > max

isVal :: Dom -> Bool
isVal dom = case toList dom of
  [] -> True
  [_] -> True
  _ -> False

prunedFromTo :: Dom -> Dom -> Maybe (Dom, Pruning)
prunedFromTo dom1@(Dom min1 max1 _) dom2@(Dom min2 max2 _) =
  fmap ((,) dom2) . getOption . foldMap (Option . Just . snd) $ filter fst
  [ prunedToVal dom1 dom2 --> Pruning.val
  , min1 < min2 --> Pruning.min
  , max1 > max2 --> Pruning.max
  , size dom1 > size dom2 --> Pruning.dom
  ]

infixr 0 -->
(-->) :: a -> b -> (a, b)
(-->) = (,)

prunedToVal :: Dom -> Dom -> Bool
prunedToVal dom1 dom2 = case (toList dom1, toList dom2) of
  ([], []) -> False
  (_, []) -> True
  ([_], [_]) -> False
  (_, [_]) -> True
  _ -> False

size :: Dom -> Int
size (Dom min max set)
  | min > max = 0
  | otherwise = maybe (max - min) IntSet.size set

deleteLT :: Int -> Dom -> Maybe (Dom, Pruning)
deleteLT x dom = prunedFromTo dom $ deleteLT' x dom

deleteLT' :: Int -> Dom -> Dom
deleteLT' x dom@(Dom min max set)
  | x > min = case set of
    Nothing -> Dom (Prelude.max x min) max Nothing
    Just set' -> fromIntSet $ deleteLT'' x set'
  | otherwise = dom

deleteLT'' :: Int -> IntSet -> IntSet
deleteLT'' x set = case IntSet.splitMember x set of
  (_, mem, gt) | mem -> IntSet.insert x gt
               | otherwise -> gt

deleteGT :: Int -> Dom -> Maybe (Dom, Pruning)
deleteGT x dom = prunedFromTo dom (deleteGT' x dom)

deleteGT' :: Int -> Dom -> Dom
deleteGT' x dom@(Dom min max set)
  | x < max = case set of
    Nothing -> Dom min (Prelude.min x max) Nothing
    Just set' -> fromIntSet $ deleteGT'' x set'
  | otherwise = dom

deleteGT'' :: Int -> IntSet -> IntSet
deleteGT'' x set = case IntSet.splitMember x set of
  (lt, mem, _) | mem -> IntSet.insert x lt
               | otherwise -> lt

retainAll :: Dom -> Dom -> Maybe (Dom, Pruning)
retainAll (Dom min max Nothing) dom =
  prunedFromTo dom (deleteGT' max . deleteLT' min $ dom)
retainAll (Dom _ _ (Just set1)) dom@(Dom _ _ (Just set2)) =
  prunedFromTo dom (fromIntSet $ IntSet.intersection set1 set2)
retainAll (Dom min1 max1 (Just set1)) dom@(Dom min2 max2 Nothing) =
  prunedFromTo dom (fromIntSet $ IntSet.intersection set1 set2)
  where
    set2 = IntSet.fromList [Prelude.max min1 min2 .. Prelude.min max1 max2]

toList :: Dom -> [Int]
toList (Dom min max set) = maybe [min .. max] IntSet.toList $ set
