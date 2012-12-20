module Control.Monad.FD.Internal.IntMap.Strict
       ( IntMap
       , (!)
       , adjust
       , alter
       , delete
       , empty
       , filter
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
import Data.Monoid (Monoid (mappend, mconcat, mempty))
import Data.Semigroup (Semigroup ((<>)))

import Prelude hiding (filter, foldl, foldr, fst, null, snd)

import Control.Monad.FD.Internal.Int

newtype IntMap k v = IntMap { unIntMap :: IntMap.IntMap (Pair k v) }

data Pair a b = !a :*: !b

instance Semigroup b => Semigroup (Pair a b) where
  (k :*: a) <> (_ :*: b) = k :*: (a <> b)

(!) :: IsInt k => IntMap k v -> k -> v
m!k = case unIntMap m IntMap.! toInt k of
  _ :*: b -> b

adjust :: IsInt k => (v -> v) -> k -> IntMap k v -> IntMap k v
adjust f k m =
  IntMap $ IntMap.adjust (\ (a :*: b) -> a :*: f b) (toInt k) (unIntMap m)

alter :: IsInt k => (Maybe v -> Maybe v) -> k -> IntMap k v -> IntMap k v
alter f k = IntMap . IntMap.alter f' (toInt k) . unIntMap
  where
    f' Nothing = case f Nothing of
      Nothing -> Nothing
      Just v -> Just $ k :*: v
    f' (Just (k' :*: v)) = case f (Just v) of
      Nothing -> Nothing
      Just v' -> Just $ k' :*: v'

delete :: IsInt k => k -> IntMap k v -> IntMap k v
delete k = IntMap . IntMap.delete (toInt k) . unIntMap

empty :: IntMap k v
empty = IntMap IntMap.empty

filter :: (v -> Bool) -> IntMap k v -> IntMap k v
filter f = IntMap . IntMap.filter (\ (_ :*: v) -> f v) . unIntMap

foldlWithKey' :: (a -> k -> v -> a) -> a -> IntMap k v -> a
foldlWithKey' f a0 = foldl' f' a0 . unIntMap
  where
    f' a (k :*: v) = f a k v

foldrWithKey :: (k -> v -> b -> b) -> b -> IntMap k v -> b
foldrWithKey f b0 = foldr f' b0 . unIntMap
  where
    f' (k :*: v) = f k v

forWithKeyM_ :: Monad m => IntMap k v -> (k -> v -> m b) -> m ()
forWithKeyM_ xs f = foldrWithKey (\ k v a -> f k v >> a) (return ()) xs

insert :: IsInt k => k -> v -> IntMap k v -> IntMap k v
insert k v m = IntMap $ IntMap.insert (toInt k) (k :*: v) (unIntMap m)

member :: IsInt k => k -> IntMap k v -> Bool
member k = IntMap.member (toInt k) . unIntMap

null :: IntMap k v -> Bool
null = IntMap.null . unIntMap

singleton :: IsInt k => k -> v -> IntMap k v
singleton k = IntMap . IntMap.singleton (toInt k) . (k :*:)

sunion :: (IsInt k, Semigroup v) => IntMap k v -> IntMap k v -> IntMap k v
sunion xs ys = IntMap $ IntMap.unionWith (<>) (unIntMap xs) (unIntMap ys)

toList :: IntMap k v -> [(k, v)]
toList = map (\ (a :*: b) -> (a, b)) . IntMap.elems . unIntMap

unionWith :: (v -> v -> v) -> IntMap k v -> IntMap k v -> IntMap k v
unionWith f xs ys = IntMap $ IntMap.unionWith f' (unIntMap xs) (unIntMap ys)
  where
    f' (k :*: a) (_ :*: b) = k :*: f a b

instance Semigroup (IntMap k v) where
  a <> b = IntMap $ unIntMap a <> unIntMap b

instance Monoid (IntMap k v) where
  mempty = IntMap mempty
  mappend x y = IntMap $ mappend (unIntMap x) (unIntMap y)
  mconcat = IntMap . mconcat . map unIntMap

instance Functor (IntMap k) where
  fmap f = IntMap . fmap (\ (k :*: v) -> k :*: f v) . unIntMap

instance Foldable (IntMap k) where
  foldMap f = foldMap (\ (_ :*: b) -> f b) . unIntMap
