module Control.Monad.FD.Internal.Dom
       ( Dom
       , full
       , empty
       , fromBounds
       , singleton
       , findMin
       , findMax
       , lookupMin
       , lookupMax
       , null
       , size
       , deleteGT
       , deleteLT
       , deleteBounds
       , difference
       , intersection
       , toList
       ) where

import Data.Functor ((<$>))
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Semigroup ((<>))

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

lookupMin :: Dom -> Maybe Min
lookupMin Empty = Nothing
lookupMin (Bounds min _) = Just min
lookupMin (IntSet set) = fst <$> IntSet.minView set

lookupMax :: Dom -> Maybe Max
lookupMax Empty = Nothing
lookupMax (Bounds _ max) = Just max
lookupMax (IntSet set) = fst <$> IntSet.maxView set

null :: Dom -> Bool
null Empty = True
null _ = False

size :: Dom -> Int
size dom = case dom of
  Empty -> 0
  Bounds min max -> max - min + 1
  IntSet set -> IntSet.size set

deleteLT :: Int -> Dom -> Dom
deleteLT x dom = case dom of
  Empty -> empty
  Bounds min max
    | x > min -> fromBounds x max
    | otherwise -> dom
  IntSet set -> fromIntSet $ deleteLT' x set

deleteLT' :: Int -> IntSet -> IntSet
deleteLT' x set = case IntSet.splitMember x set of
  (_, mem, gt)
    | mem -> IntSet.insert x gt
    | otherwise -> gt

deleteGT :: Int -> Dom -> Dom
deleteGT x dom = case dom of
  Empty -> empty
  Bounds min max
    | x < max -> fromBounds min x
    | otherwise -> dom
  IntSet set -> fromIntSet $ deleteGT' x set

deleteGT' :: Int -> IntSet -> IntSet
deleteGT' x set = case IntSet.splitMember x set of
  (lt, mem, _)
    | mem -> IntSet.insert x lt
    | otherwise -> lt

deleteBounds :: Int -> Int -> Dom -> Dom
deleteBounds min1 max1 dom@(Bounds min2 max2)
  | min1 > min2 && max1 < max2 =
    fromIntSet $
    IntSet.fromList [min2 .. min1 - 1] <>
    IntSet.fromList [max1 + 1 .. max2]
  | min1 > max2 || max1 < min2 =
    dom
  | max1 < max2 =
    fromBounds (max1 + 1) max2
  | min1 > min2 =
    fromBounds min2 (min1 - 1)
  | otherwise =
    empty
deleteBounds min max (IntSet set) =
  case IntSet.split min set of
    (lt, gt) -> case IntSet.split max gt of
      (_, gt') -> fromIntSet $ lt <> gt'
deleteBounds _ _ Empty =
  empty

difference :: Dom -> Dom -> Dom
difference = undefined

intersection :: Dom -> Dom -> Dom
intersection = undefined

toList :: Dom -> [Int]
toList dom = case dom of
  Empty -> []
  Bounds min max -> [min .. max]
  IntSet set -> IntSet.toList set
