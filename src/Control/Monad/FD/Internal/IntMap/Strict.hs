module Control.Monad.FD.Internal.IntMap.Strict
       ( IntMap
       , (!)
       , adjust
       , delete
       , empty
       , foldlWithKey'
       , foldrWithKey
       , forWithKeyM_
       , insert
       , member
       , null
       , singleton
       , sunion
       , toList
       , unionWith
       ) where

import qualified Data.IntMap.Strict as IntMap
import Data.Foldable (Foldable (foldMap), foldl', foldr)
import Data.Semigroup

import Prelude hiding (foldl, foldr, fst, null, snd)

import Control.Monad.FD.Internal.Int

newtype IntMap k v = IntMap { unIntMap :: IntMap.IntMap (Pair k v) }

data Pair a b = !a :*: !b

instance Semigroup b => Semigroup (Pair a b) where
  k :*: a <> _ :*: b = k :*: (a <> b)

(!) :: IsInt k => IntMap k v -> k -> v
m!k = case unIntMap m IntMap.! toInt k of
  _ :*: b -> b

adjust :: IsInt k => (v -> v) -> k -> IntMap k v -> IntMap k v
adjust f k m =
  IntMap $ IntMap.adjust (\ (a :*: b) -> a :*: f b) (toInt k) (unIntMap m)

delete :: IsInt k => k -> IntMap k v -> IntMap k v
delete k = IntMap . IntMap.delete (toInt k) . unIntMap

empty :: IntMap k v
empty = IntMap IntMap.empty
{-# INLINE empty #-}

foldlWithKey' :: (a -> k -> v -> a) -> a -> IntMap k v -> a
foldlWithKey' f a0 = foldl' f' a0 . unIntMap
  where
    f' a (k :*: v) = f a k v
{-# INLINE foldlWithKey' #-}

foldrWithKey :: (k -> v -> b -> b) -> b -> IntMap k v -> b
foldrWithKey f b0 = foldr f' b0 . unIntMap
  where
    f' (k :*: v) b = f k v b
{-# INLINE foldrWithKey #-}

forWithKeyM_ :: Monad m => IntMap k v -> (k -> v -> m b) -> m ()
forWithKeyM_ xs f = foldrWithKey (\ k v a -> f k v >> a) (return ()) xs

insert :: IsInt k => k -> v -> IntMap k v -> IntMap k v
insert k v m = IntMap $ IntMap.insert (toInt k) (k :*: v) (unIntMap m)

member :: IsInt k => k -> IntMap k v -> Bool
member k = IntMap.member (toInt k) . unIntMap

null :: IntMap k v -> Bool
null = IntMap.null . unIntMap
{-# INLINE null #-}

singleton :: IsInt k => k -> v -> IntMap k v
singleton k = IntMap . IntMap.singleton (toInt k) . (k :*:)
{-# INLINE singleton #-}

sunion :: (IsInt k, Semigroup v) => IntMap k v -> IntMap k v -> IntMap k v
sunion xs ys = IntMap $ IntMap.unionWith (<>) (unIntMap xs) (unIntMap ys)

toList :: IntMap k v -> [(k, v)]
toList = map (\ (a :*: b) -> (a, b)) . IntMap.elems . unIntMap

unionWith :: IsInt k => (v -> v -> v) -> IntMap k v -> IntMap k v -> IntMap k v
unionWith f xs ys = IntMap $ IntMap.unionWith f' (unIntMap xs) (unIntMap ys)
  where
    f' (k :*: a) (_ :*: b) = k :*: f a b

instance Monoid (IntMap k v) where
  mempty = IntMap mempty
  mappend x y = IntMap $ mappend (unIntMap x) (unIntMap y)
  mconcat = IntMap . mconcat . map unIntMap

instance Functor (IntMap k) where
  fmap f = IntMap . fmap (\ (k :*: v) -> k :*: f v) . unIntMap

instance Foldable (IntMap k) where
  foldMap f = foldMap (\ (_ :*: b) -> f b) . unIntMap
