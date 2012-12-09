module Control.Monad.FD.Internal.DList
       ( DList
       , append
       , empty
       , fromList
       , singleton
       , snoc
       , toList
       , uncons
       ) where

import Data.Foldable (Foldable (fold, foldMap, foldr, foldl, foldr1, foldl1))
import Data.Monoid

import Prelude hiding (foldr, foldr1, foldl, foldl1)

newtype DList a = DList { unDList :: [a] -> [a] }

append :: DList a -> DList a -> DList a
append xs ys = DList $ unDList xs . unDList ys

empty :: DList a
empty = DList id

fromList :: [a] -> DList a
fromList = DList . (++)

singleton :: a -> DList a
singleton = DList . (:)

snoc :: DList a -> a -> DList a
snoc xs x = DList $ unDList xs . (x:)

toList :: DList a -> [a]
toList = ($ []) . unDList

uncons :: DList a -> Maybe (a, DList a)
uncons xs = case toList xs of
  [] -> Nothing
  (x:xs') -> Just (x, fromList xs')

instance Show a => Show (DList a) where
  showsPrec d m = showParen (d > 10) $ showString "fromList " . shows (toList m)

instance Monoid (DList a) where
  mempty = empty
  mappend = append

instance Foldable DList where
  fold = fold . toList
  foldMap f = foldMap f . toList
  foldr f b = foldr f b . toList
  foldl f a = foldl f a . toList
  foldr1 f = foldr1 f . toList
  foldl1 f = foldl1 f . toList
