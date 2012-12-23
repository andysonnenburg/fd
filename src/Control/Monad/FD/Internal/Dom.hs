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
       , delete
       , retain
       , toList
       ) where

import Data.Foldable (foldMap)
import Data.IntSet (IntSet, (\\))
import qualified Data.IntSet as IntSet
import Data.Semigroup (Option (Option), (<>), getOption)

import Control.Monad.FD.Internal.Pruning (Pruning)
import qualified Control.Monad.FD.Internal.Pruning as Pruning

import Prelude hiding (min, max, null)
import qualified Prelude

data Dom
  = Bounds {-# UNPACK #-} !Min {-# UNPACK #-} !Max
  | IntSet !IntSet
  | Empty deriving Show

type Min = Int
type Max = Int

full :: Dom
full = fromBounds minBound maxBound

empty :: Dom
empty = Empty

fromBounds :: Min -> Max -> Dom
fromBounds min max
  | min > max = Empty
  | otherwise = Bounds min max

singleton :: Int -> Dom
singleton x = fromBounds x x

fromIntSet :: IntSet -> Dom
fromIntSet set
  | IntSet.null set = empty
  | otherwise = IntSet set

findMin :: Dom -> Min
findMin Empty = error "findMin: empty domain has no minimal element"
findMin (Bounds min _) = min
findMin (IntSet set) = IntSet.findMin set

findMax :: Dom -> Max
findMax Empty = error "findMax: empty domain has no maximal element"
findMax (Bounds _ max) = max
findMax (IntSet set) = IntSet.findMax set

null :: Dom -> Bool
null Empty = True
null _ = False

isVal :: Dom -> Bool
isVal dom = case toList dom of
  [] -> True
  [_] -> True
  _ -> False

prunedFromTo :: Dom -> Dom -> Maybe (Dom, Pruning)
prunedFromTo dom1 dom2 =
  fmap ((,) dom2) . getOption . foldMap (Option . Just . snd) $ filter fst
  [ prunedToVal dom1 dom2 --> Pruning.val
  , min1 < min2 --> Pruning.min
  , max1 > max2 --> Pruning.max
  , size dom1 > size dom2 --> Pruning.dom
  ]
  where
    (min1, max1) = bounds dom1
    (min2, max2) = bounds dom2

bounds :: Dom -> (Min, Max)
bounds dom = case dom of
  Empty -> (maxBound, minBound)
  Bounds min max -> (min, max)
  IntSet set -> (IntSet.findMin set, IntSet.findMax set)

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
size dom = case dom of
  Empty -> 0
  Bounds min max -> max - min + 1
  IntSet set -> IntSet.size set

deleteLT' :: Int -> Dom -> Dom
deleteLT' x dom = case dom of
  Empty -> empty
  Bounds min max
    | x > min -> fromBounds x max
    | otherwise -> dom
  IntSet set -> case IntSet.splitMember x set of
    (_, mem, gt)
      | mem -> fromIntSet $ IntSet.insert x gt
      | otherwise -> fromIntSet gt

deleteGT' :: Int -> Dom -> Dom
deleteGT' x dom = case dom of
  Empty -> empty
  Bounds min max
    | x < max -> fromBounds min x
    | otherwise -> dom
  IntSet set -> case IntSet.splitMember x set of
    (lt, mem, _)
      | mem -> fromIntSet $ IntSet.insert x lt
      | otherwise -> fromIntSet lt

delete :: Dom -> Dom -> Maybe (Dom, Pruning)
delete (Bounds min1 max1) dom@(Bounds min2 max2) =
  prunedFromTo dom dom'
  where
    dom'
      | min1 > min2 && max1 < max2 =
        fromIntSet $
        IntSet.fromList [min2 .. min1 - 1] <>
        IntSet.fromList [max1 + 1 .. max2]
      | max1 < min2 && max1 < max2 =
        dom
      | max1 < max2 =
        fromBounds (max1 + 1) max2
      | min1 > min2 && min1 > max2 =
        dom
      | min1 > min2 =
        fromBounds min2 (min1 - 1)
      | otherwise = empty
delete (Bounds min max) dom@(IntSet set) =
  prunedFromTo dom dom'
  where
    dom' = case IntSet.split min set of
      (lt, gt) -> case IntSet.split max gt of
        (_, gt') -> fromIntSet $ lt <> gt'
delete (IntSet set) dom@(Bounds min max) =
  prunedFromTo dom dom'
  where
    dom' = fromIntSet $ IntSet.fromList [min .. max] \\ set
delete (IntSet set1) dom@(IntSet set2) =
  prunedFromTo dom dom'
  where
    dom' = fromIntSet $ set2 \\ set1
delete Empty _ =
  Nothing
delete _ Empty =
  Nothing

retain :: Dom -> Dom -> Maybe (Dom, Pruning)
retain Empty dom =
  prunedFromTo dom empty
retain (Bounds min max) dom =
  prunedFromTo dom (deleteGT' max . deleteLT' min $ dom)
retain (IntSet set1) dom@(Bounds min2 max2) =
  prunedFromTo dom (fromIntSet $ IntSet.intersection set1 set2)
  where
    set2 = IntSet.fromList [Prelude.max min1 min2 .. Prelude.min max1 max2]
    min1 = IntSet.findMin set1
    max1 = IntSet.findMax set1
retain (IntSet set1) dom@(IntSet set2) =
  prunedFromTo dom (fromIntSet $ IntSet.intersection set1 set2)
retain (IntSet _) Empty =
  Nothing

toList :: Dom -> [Int]
toList dom = case dom of
  Empty -> []
  Bounds min max -> [min .. max]
  IntSet set -> IntSet.toList set
