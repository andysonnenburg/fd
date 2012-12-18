module Control.Monad.FD.Internal.IntSet
       ( IntSet
       , delete
       , insert
       , member
       , null
       , singleton
       ) where

import Data.Foldable
import Data.Monoid

import Prelude hiding (foldl, foldr, null)

import Control.Monad.FD.Internal.Int
import Control.Monad.FD.Internal.IntMap.Strict (IntMap)
import qualified Control.Monad.FD.Internal.IntMap.Strict as IntMap

newtype IntSet a = IntSet { unIntSet :: IntMap a a }

delete :: IsInt a => a -> IntSet a -> IntSet a
delete x = IntSet . IntMap.delete x . unIntSet

insert :: IsInt a => a -> IntSet a -> IntSet a
insert x = IntSet . IntMap.insert x x . unIntSet

member :: IsInt a => a -> IntSet a -> Bool
member x = IntMap.member x . unIntSet

null :: IntSet a -> Bool
null = IntMap.null . unIntSet
{-# INLINE null #-}

singleton :: IsInt a => a -> IntSet a
singleton x = IntSet $ IntMap.singleton x x
{-# INLINE singleton #-}

instance Monoid (IntSet a) where
  mempty = IntSet mempty
  mappend a b = IntSet $ mappend (unIntSet a) (unIntSet b)
  mconcat = IntSet . mconcat . map unIntSet

instance Foldable IntSet where
  fold = fold . unIntSet
  foldr f b = foldr f b . unIntSet
  foldl f a = foldl f a . unIntSet
  foldMap f = foldMap f . unIntSet
