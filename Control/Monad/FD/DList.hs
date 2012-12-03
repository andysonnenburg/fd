module Control.Monad.FD.DList
       ( DList
       , append
       , empty
       , fromList
       , singleton
       , snoc
       , toList
       , uncons
       ) where

import Data.Monoid

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
