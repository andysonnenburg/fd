{-# LANGUAGE CPP #-}
#if defined(LANGUAGE_DataKinds) && defined(LANGUAGE_PolyKinds)
{-# LANGUAGE DataKinds #-}
#else
{-# LANGUAGE EmptyDataDecls #-}
#endif
{-# LANGUAGE
    FlexibleInstances
  , GADTs
  , MultiParamTypeClasses #-}
#if defined(LANGUAGE_DataKinds) && defined(LANGUAGE_PolyKinds)
{-# LANGUAGE PolyKinds #-}
#endif
{-# LANGUAGE
    Rank2Types
  , ScopedTypeVariables
  , TypeFamilies
  , TypeSynonymInstances #-}
module Data.IntSet.Dom
       ( -- * the Dom type
         Dom
         -- * Query
       , null
       , size
       , member
         -- * Construction
       , full
       , empty
       , singleton
       , singletonGE
       , singletonLE
       , fromBounds
       , insert
       , insertGE
       , insertLE
       , deleteGT
       , deleteLT
       , deleteBounds
         -- * Combine
       , difference
       , intersection
         -- * Folds
       , foldr
       , foldl
       , foldl'
         -- * Min\/Max
       , findMin
       , findMax
       , lookupMin
       , lookupMax
         -- * Conversion

         -- ** List
       , toList
       , fromList
       ) where

import Control.Monad ((<=<))
#if !(MIN_VERSION_base(4, 6, 0))
import Control.Monad.Instances ()
#endif

import Data.Functor ((<$>))
import Data.Bits
import Data.Function (on)
import qualified Data.List as List
import Data.Word (Word)

#ifdef __GLASGOW_HASKELL__
import GHC.Exts (build)
#endif

import Prelude hiding (Bool (..),
                       (.),
                       foldl,
                       foldr,
                       id,
                       init,
                       last,
                       max,
                       min,
                       not,
                       null)
import qualified Prelude

-- | $setup
-- >>> import Prelude hiding (foldl, foldr, null)

newtype Dom = Dom (Root C C)

data Tree t a b where
  Signed ::
    !(Subtree a b) ->
    !(Subtree b c) ->
    Root a c
  Unsigned ::
    {-# UNPACK #-} !Prefix ->
    {-# UNPACK #-} !Mask ->
    !(Subtree a b) ->
    !(Subtree b c) ->
    Tree t a c
  Min ::
    {-# UNPACK #-} !Int ->
    Tree t C O
  Max ::
    {-# UNPACK #-} !Int ->
    Tree t O C
  Elem ::
    {-# UNPACK #-} !Int ->
    Tree t C C
  Empty ::
    Root a b

type Root = Tree C

type Subtree = Tree O

#if defined(LANGUAGE_DataKinds) && defined(LANGUAGE_PolyKinds)
data S = C | O
#else
data C
data O
#endif

type Prefix = Int

type Mask = Int

instance Show Dom where
  showsPrec p t =
    showParen (p > 10) $ showString "fromList " . shows (toList t)

instance Eq Dom where
  (==) = (==) `on` toList
  (/=) = (/=) `on` toList

instance Ord Dom where
  compare = compare `on` toList

-- |
-- >>> null empty
-- True
-- >>> null (singleton 1)
-- False
null :: Dom -> Prelude.Bool
null (Dom t) = case t of
  Empty -> Prelude.True
  _ -> Prelude.False
{-# INLINE null #-}

-- |
-- >>> size empty
-- 0
-- >>> size (singleton 1)
-- 1
size :: Dom -> Int
size = foldlWithBounds' (\ a _ -> a + 1) (\ a min max -> a + max - min + 1) 0

-- |
-- >>> member 5 (fromList [5, 3])
-- True
-- >>> member 1 (fromList [5, 3])
-- False
member :: Int -> Dom -> Prelude.Bool
member x = x `seq` \ (Dom t) -> case t of
  Signed l r
    | x < 0 -> go l
    | otherwise -> go r
  Unsigned p m l r
    | mkPrefix x m /= p -> Prelude.False
    | zero x m -> go l
    | otherwise -> go r
  Elem x' -> x == x'
  Empty -> Prelude.False
  where
    go :: Subtree a b -> Prelude.Bool
    go (Unsigned p m l r)
      | mkPrefix x m /= p =
        if x < p then toBool $ hasn'tMin l else toBool $ hasn'tMax r
      | zero x m =
        go l
      | otherwise =
        go r
    go (Min min) = x >= min
    go (Max max) = x <= max
    go (Elem x') = x == x'

hasMin :: Subtree a b -> Bool C O a
hasMin t = case t of
  Unsigned _ _ l _ -> hasMin l
  Min _ -> True
  Max _ -> False
  Elem _ -> True

hasMax :: Subtree a b -> Bool C O b
hasMax t = case t of
  Unsigned _ _ _ r -> hasMax r
  Min _ -> False
  Max _ -> True
  Elem _ -> True

hasn'tMin :: Subtree a b -> Bool O C a
hasn'tMin = not . hasMin

hasn'tMax :: Subtree a b -> Bool O C b
hasn'tMax = not . hasMax

-- |
-- >>> size full == maxBound - minBound + 1
-- True
full :: Dom
full = Dom $ Signed minTree maxTree

-- |
-- >>> size empty
-- 0
empty :: Dom
empty = Dom Empty
{-# INLINE empty #-}

-- |
-- >>> size (singleton 1)
-- 1
singleton :: Int -> Dom
singleton = Dom . Elem
{-# INLINE singleton #-}

singletonGE :: Int -> Dom
singletonGE = Dom . singletonGE'

singletonLE :: Int -> Dom
singletonLE = Dom . singletonLE'

fromBounds :: Int -> Int -> Dom
fromBounds = (Dom .) . fromBounds'

fromBounds' :: Int -> Int -> Root C C
fromBounds' min max
  | min < max = append (Min min) (Max max)
  | min == max = Elem min
  | otherwise = Empty

-- |
-- >>> insert 5 (fromList [5, 3])
-- fromList [3,5]
-- >>> insert 7 (fromList [5, 3])
-- fromList [3,5,7]
-- >>> insert 5 empty == singleton 5
-- True
insert :: Int -> Dom -> Dom
insert x = x `seq` \ (Dom t) -> Dom $ case t of
  Signed l r
    | x < 0 -> Signed (go l) r
    | otherwise -> Signed l (go r)
  Unsigned p m l r
    | mkPrefix x m /= p -> combine (Elem x) (Unsigned p m l r)
    | zero x m -> Unsigned p m (go l) r
    | otherwise -> Unsigned p m l (go r)
  Elem x'
    | x == x' -> t
    | otherwise -> combine (Elem x) (Elem x')
  Empty -> Elem x
  where
    go :: Subtree a b -> Subtree a b
    go t@(Unsigned p m l r)
      | mkPrefix x m /= p =
        if x < p
        then ifThenElse (hasMin l) (Elem x >>> t) t
        else ifThenElse (hasMax r) (t >>> Elem x) t
      | zero x m =
        Unsigned p m (go l) r
      | otherwise =
        Unsigned p m l (go r)
    go t@(Min min)
      | x >= min = t
      | otherwise = Elem x >>> t
    go t@(Max max)
      | x <= max = t
      | otherwise = t >>> Elem x
    go t@(Elem x')
      | x == x' = t
      | zero x m = Unsigned p m (Elem x) t
      | otherwise = Unsigned p m t (Elem x)
      where
        m = mkMask x x'
        p = mkPrefix x m

-- |
-- >>> member 4 $ insertGE 2 $ fromBounds 1 3
-- True
-- >>> member 0 $ insertGE 2 $ fromBounds 1 3
-- False
-- >>> size (insertGE 7 $ fromBounds 5 10) == maxBound - 5 + 1
-- True
-- >>> member (maxBound - 2) $ insertGE (maxBound - 1) $ fromBounds (-1) 1
-- False
-- >>> member (maxBound - 2) $ insertGE (maxBound - 1) $ singleton 1
-- False
insertGE :: Int -> Dom -> Dom
insertGE x
  | x == maxBound = insert x
  | otherwise = \ (Dom t) -> Dom $ case t of
    Signed l r
      | x < 0 -> Signed (unwrap $ unsafeInsertGE x l) maxTree
      | otherwise -> case unsafeInsertGE x r of
        Semigroupoid r' -> Signed l (unsafeInsertMax maxBound r')
        Id -> Signed l maxTree
    Unsigned p m l r
      | x < 0 ->
        if p < 0
        then Signed (unwrap $ unsafeInsertGE x (Unsigned p m l r)) maxTree
        else Signed (Min x) maxTree
      | otherwise ->
        if p < 0
        then Signed (Unsigned p m l r) (unsafeSingletonGE x)
        else unsafeAppend (unwrap $ unsafeInsertGE x (Unsigned p m l r)) maxTree
    Elem x'
      | x < 0 ->
        if x' < 0
        then unsafeAppend (unwrap $ unsafeInsertGE x (Elem x')) maxTree
        else Signed (Min x) maxTree
      | otherwise ->
        if x' < 0
        then Signed (Elem x') (unsafeSingletonGE x)
        else unsafeInsertMax maxBound . unwrap $ unsafeInsertGE x (Elem x')
    Empty -> singletonGE' x

unsafeInsertGE :: Int -> Subtree a b -> WithFull Subtree a O
unsafeInsertGE x = x `seq` go
  where
    go :: Subtree a b -> WithFull Subtree a O
    go t@(Unsigned p m l r)
      | mkPrefix x m /= p =
        if x < p
        then ifThenElse (hasMin l) (wrap $ Min x) id
        else wrap $ ifThenElse (hasMax r) (t >>> Min x) t
      | zero x m =
        go l
      | otherwise =
        case go r of
          Semigroupoid r' -> wrap $ Unsigned p m l r'
          Id -> wrap l
    go t@(Min min)
      | min <= x = wrap t
      | otherwise = wrap $ Min x
    go t@(Max max)
      | x <= max = id
      | otherwise = wrap $ t >>> Min x
    go t@(Elem x')
      | x' >= x = wrap $ Min x
      | otherwise = wrap $ t >>> Min x

singletonGE' :: Int -> Root C C
singletonGE' x = append (Min x) maxTree

unsafeSingletonGE :: Int -> Tree t C C
unsafeSingletonGE x = unsafeAppend (Min x) maxTree

maxTree :: Tree t O C
maxTree = Max maxBound

-- |
-- >>> member 4 $ insertLE 2 $ fromBounds 1 3
-- False
-- >>> member 0 $ insertLE 2 $ fromBounds 1 3
-- True
-- >>> member (minBound + 2) $ insertLE (minBound + 1) $ fromBounds (-1) 2
-- False
-- >>> member (minBound + 2) $ insertLE (minBound + 1) $ singleton (-1)
-- False
insertLE :: Int -> Dom -> Dom
insertLE x
  | x == minBound = insert x
  | otherwise = \ (Dom t) -> Dom $ case t of
    Signed l r
      | x >= 0 -> Signed minTree (unwrap $ unsafeInsertLE x r)
      | otherwise -> case unsafeInsertLE x l of
        Semigroupoid l' -> Signed (unsafeInsertMin minBound l') r
        Id -> Signed minTree r
    Unsigned p m l r
      | x >= 0 ->
        if p >= 0
        then Signed minTree (unwrap $ unsafeInsertLE x (Unsigned p m l r))
        else Signed minTree (Max x)
      | otherwise ->
        if p >= 0
        then Signed (unsafeSingletonLE x) (Unsigned p m l r)
        else unsafeAppend minTree (unwrap $ unsafeInsertLE x (Unsigned p m l r))
    Elem x'
      | x >= 0 ->
        if x' >= 0
        then Signed minTree (unwrap $ unsafeInsertLE x (Elem x'))
        else Signed minTree (Max x)
      | otherwise ->
        if x' >= 0
        then Signed (unsafeSingletonLE x) (Elem x')
        else unsafeInsertMin minBound . unwrap $ unsafeInsertLE x (Elem x')
    Empty -> singletonLE' x

unsafeInsertLE :: Int -> Subtree a b -> WithFull Subtree O b
unsafeInsertLE x = x `seq` go
  where
    go :: Subtree a b -> WithFull Subtree O b
    go t@(Unsigned p m l r)
      | mkPrefix x m /= p =
        if x < p
        then wrap $ ifThenElse (hasMin l) (Max x >>> t) t
        else ifThenElse (hasMax r) (wrap $ Max x) id
      | zero x m =
        case go l of
          Semigroupoid l' -> wrap $ Unsigned p m l' r
          Id -> wrap r
      | otherwise =
        go r
    go t@(Min min)
      | min <= x = id
      | otherwise = wrap $ Max x >>> t
    go t@(Max max)
      | x <= max = wrap t
      | otherwise = wrap $ Max x
    go t@(Elem x')
      | x' <= x = wrap $ Max x
      | otherwise = wrap $ Max x >>> t

singletonLE' :: Int -> Root C C
singletonLE' x = append minTree (Max x)

unsafeSingletonLE :: Int -> Tree t C C
unsafeSingletonLE x = unsafeAppend minTree (Max x)

minTree :: Tree t C O
minTree = Min minBound

-- |
-- >>> deleteGT 4 $ insert 4 $ fromBounds (-2) 3
-- fromList [-2,-1,0,1,2,3,4]
-- >>> deleteGT 4 $ singleton 4
-- fromList [4]
-- >>> deleteGT 4 $ singleton 5
-- fromList []
deleteGT :: Int -> Dom -> Dom
deleteGT x = x `seq` \ (Dom t) -> Dom $ case t of
  Signed l r
    | x >= 0 -> case unsafeDeleteGT x r of
      Semigroupoid r' -> Signed l r'
      Id -> fromSubtree l
    | otherwise -> toRoot $ unsafeDeleteGT x l
  Unsigned p m l r
    | x >= 0 ->
      if p >= 0
      then toRoot $ unsafeDeleteGT x (Unsigned p m l r) 
      else t
    | otherwise ->
      if p >= 0
      then Empty
      else toRoot $ unsafeDeleteGT x (Unsigned p m l r)
  Elem x' -> toRoot $ unsafeDeleteGT x (Elem x')
  Empty -> Empty

unsafeDeleteGT :: Int -> Subtree a b -> WithEmpty Subtree a C
unsafeDeleteGT x = x `seq` go
  where
    go :: Subtree a b -> WithEmpty Subtree a C
    go t@(Unsigned p m l r)
      | mkPrefix x m /= p =
        if x < p
        then ifThenElse (hasMin l) id (wrap $ Max x)
        else ifThenElse (hasMax r) (wrap t) (wrap $ t >>> Max x)
      | zero x m =
        go l
      | otherwise =
        case go r of
          Semigroupoid r' -> wrap $ Unsigned p m l r'
          Id -> wrap l
    go t@(Min min)
      | min > x = id
      | min == x = wrap $ Elem x
      | otherwise = wrap $ t >>> Max x
    go t@(Max max)
      | max > x = wrap $ Max x
      | otherwise = wrap t
    go t@(Elem x')
      | x' > x = id
      | otherwise = wrap t

-- |
-- >>> deleteLT (-2) $ fromBounds (-3) (-2)
-- fromList [-2]
deleteLT :: Int -> Dom -> Dom
deleteLT x = x `seq` \ (Dom t) -> Dom $ case t of
  Signed l r
    | x >= 0 -> toRoot $ unsafeDeleteLT x r
    | otherwise -> case unsafeDeleteLT x l of
      Semigroupoid l' -> Signed l' r
      Id -> fromSubtree r
  Unsigned p m l r
    | x >= 0 ->
      if p >= 0
      then toRoot $ unsafeDeleteLT x (Unsigned p m l r)
      else Empty
    | otherwise ->
      if p >= 0
      then t
      else toRoot $ unsafeDeleteLT x (Unsigned p m l r)
  Elem x' -> toRoot $ unsafeDeleteLT x (Elem x')
  Empty -> Empty

unsafeDeleteLT :: Int -> Subtree a b -> WithEmpty Subtree C b
unsafeDeleteLT x = x `seq` go
  where
    go :: Subtree a b -> WithEmpty Subtree C b
    go t@(Unsigned p m l r)
      | mkPrefix x m /= p =
        if x < p
        then ifThenElse (hasMin l) (wrap t) (wrap $ Min x >>> t)
        else ifThenElse (hasMax r) id (wrap $ Min x)
      | zero x m =
        case go l of
          Semigroupoid l' -> wrap $ Unsigned p m l' r
          Id -> wrap r
      | otherwise =
        go r
    go t@(Min min)
      | min < x = wrap $ Min x
      | otherwise = wrap t
    go t@(Max max)
      | max < x = id
      | max == x = wrap $ Elem x
      | otherwise = wrap $ Min x >>> t
    go t@(Elem x')
      | x' < x = id
      | otherwise = wrap t

-- |
-- >>> deleteBounds (minBound + 1) (maxBound - 1) $ fromBounds 2 9
-- fromList []
-- >>> deleteBounds 8 8 $ fromBounds 1 9
-- fromList [1,2,3,4,5,6,7,9]
-- >>> deleteBounds 1 9 $ fromBounds 1 9
-- fromList []
-- >>> deleteBounds 4 9 $ fromBounds 1 9
-- fromList [1,2,3]
-- >>> deleteBounds 2 9 $ fromBounds 1 9
-- fromList [1]
-- >>> deleteBounds 9 8 $ fromBounds 1 9
-- fromList [1,2,3,4,5,6,7,8,9]
-- >>> deleteBounds 1 9 $ fromBounds 1 9
-- fromList []
deleteBounds :: Int -> Int -> Dom -> Dom
deleteBounds min max
  | max < min =
    id
  | min == minBound =
    if max == maxBound
    then const empty
    else deleteLT max'
  | otherwise =
    if max == maxBound
    then deleteGT min'
    else \ (Dom t) -> Dom $ case t of
      Signed l r
        | m' < 0 -> case unsafeDeleteGT min' l of
          Semigroupoid l' -> case unsafeDeleteLT max' r of
            Semigroupoid r' -> Signed l' r'
            Id -> fromSubtree l'
          Id -> toRoot $ unsafeDeleteLT max' r
        | p' < 0 -> case go l of
          Semigroupoid l' -> Signed l' r
          Id -> fromSubtree r
        | otherwise -> case go r of
          Semigroupoid r' -> Signed l r'
          Id -> Empty
      Unsigned p m l r -> toRoot $ go (Unsigned p m l r)
      Elem x -> toRoot $ go (Elem x)
      Empty -> Empty
  where
    m' = mkMask min' max'
    p' = mkPrefix min' m'
    min' = min - 1
    max' = max + 1
    go :: Subtree a b -> WithEmpty Subtree a b
    go t@(Unsigned p m l r)
      | toWord m' >= toWord m || mkPrefix p' m /= p =
        unsafeDeleteGT min' t >>> unsafeDeleteLT max' t
      | zero p' m = case go l of
        Semigroupoid l' -> wrap $ Unsigned p m l' r
        Id -> wrap r
      | otherwise = case go r of
        Semigroupoid r' -> wrap $ Unsigned p m l r'
        Id -> wrap l
    go t@(Min x)
      | x < min' = wrap $ unsafeInsertMin x (Max min' >>> Min max')
      | x == min' = wrap $ Elem x >>> Min max'
      | x >= max' = wrap t
      | otherwise = wrap $ Min max'
    go t@(Max x)
      | x <= min' = wrap t
      | x > max' = wrap $ unsafeInsertMax x (Max min' >>> Min max')
      | x == max' = wrap $ Max min' >>> Elem x
      | otherwise = wrap $ Max min'
    go t@(Elem x)
      | x > min' && x < max' = id
      | otherwise = wrap t

difference :: Dom -> Dom -> Dom
difference = undefined

intersection :: Dom -> Dom -> Dom
intersection = undefined

-- |
-- >>> foldr (+) 0 (fromList [5, 3])
-- 8
foldr :: (Int -> b -> b) -> b -> Dom -> b
foldr f = foldrWithBounds f (\ min max b -> List.foldr f b [min .. max])

foldrWithBounds :: forall b . (Int -> b -> b) -> (Int -> Int -> b -> b) -> b -> Dom -> b
foldrWithBounds f g b = \ (Dom t) -> case t of
  Signed l r -> go l (go r b)
  Unsigned _ _ l r -> go l (go r b)
  Elem x -> f x b
  Empty -> b
  where
    go :: Subtree e x -> IfC x b (Pair b) -> IfC e b (Pair b)
    go (Unsigned _ _ l r) b' = go l (go r b')
    go (Min min) (max :*: b') = g min max b'
    go (Max max) b' = max :*: b'
    go (Elem x) b' = f x b'
{-# INLINE foldrWithBounds #-}

-- |
-- >>> foldl (+) 0 (fromList [5, 3])
-- 8
foldl :: (a -> Int -> a) -> a -> Dom -> a
foldl f = foldlWithBounds f (\ a min max -> List.foldl f a [min .. max])

foldlWithBounds :: forall a . (a -> Int -> a) -> (a -> Int -> Int -> a) -> a -> Dom -> a
foldlWithBounds f g a = \ (Dom t) -> case t of
  Signed l r -> go r (go l a)
  Unsigned _ _ l r -> go r (go l a)
  Elem x -> f a x
  Empty -> a
  where
    go :: Subtree e x -> IfC e a (Pair a) -> IfC x a (Pair a)
    go (Unsigned _ _ l r) a' = go r (go l a')
    go (Min min) a' = min :*: a'
    go (Max max) (min :*: a') = g a' min max
    go (Elem x) a' = f a' x
{-# INLINE foldlWithBounds #-}

-- |
-- >>> foldl' (+) 0 (fromList [5, 3])
-- 8
foldl' :: (a -> Int -> a) -> a -> Dom -> a
foldl' f = foldlWithBounds' f (\ a min max -> List.foldl' f a [min .. max])

foldlWithBounds' :: forall a . (a -> Int -> a) -> (a -> Int -> Int -> a) -> a -> Dom -> a
foldlWithBounds' f g a = \ (Dom t) -> case t of
  Signed l r -> go r (go l a)
  Unsigned _ _ l r -> go r (go l a)
  Elem x -> a `seq` f a x
  Empty -> a
  where
    go :: Subtree e x -> IfC e a (StrictPair a) -> IfC x a (StrictPair a)
    go (Unsigned _ _ l r) a' = go r (go l a')
    go (Min min) a' = min :*! a'
    go (Max max) (min :*! a') = g a' min max
    go (Elem x) a' = a' `seq` f a' x
{-# INLINE foldlWithBounds' #-}

-- |
-- >>> toList (fromList [5, 3])
-- [3,5]
toList :: Dom -> [Int]
toList = foldr (:) []

#if __GLASGOW_HASKELL__
foldrFB :: (Int -> b -> b) -> (Int -> Int -> b -> b) -> b -> Dom -> b
foldrFB = foldrWithBounds
{-# INLINE[0] foldrFB #-}
{-# NOINLINE[0] toList #-}
{-# RULES
"Dom.toList->build" [~1]
  forall t . toList t = build (\ c n ->
    foldrFB (\ x xs -> c x xs) (\ min max xs -> List.foldr c xs [min .. max]) n t)
"Dom.foldrFB->toList" [1]
  foldrFB (\ x xs -> x:xs) (\ min max xs -> List.foldr (:) xs [min .. max]) [] =
    toList
 #-}
#endif

findMin :: Dom -> Int
findMin (Dom t) = case t of
  Signed l _ -> go l
  Unsigned _ _ l _ -> go l
  Elem x -> go (Elem x)
  Empty -> error "findMin: empty domain has no minimal element"
  where
    go :: Subtree C b -> Int
    go (Unsigned _ _ l _) = go l
    go (Min x) = x
    go (Elem x) = x

findMax :: Dom -> Int
findMax (Dom t) = case t of
  Signed _ r -> go r
  Unsigned _ _ _ r -> go r
  Elem x -> go (Elem x)
  Empty -> error "findMin: empty domain has no maximal element"
  where
    go :: Subtree a C -> Int
    go (Unsigned _ _ _ r) = go r
    go (Max x) = x
    go (Elem x) = x

lookupMin :: Dom -> Maybe Int
lookupMin (Dom t) = case t of
  Signed l _ -> Just $ go l
  Unsigned _ _ l _ -> Just $ go l
  Elem x -> Just $ go (Elem x)
  Empty -> Nothing
  where
    go :: Subtree C b -> Int
    go (Unsigned _ _ l _) = go l
    go (Min x) = x
    go (Elem x) = x

lookupMax :: Dom -> Maybe Int
lookupMax (Dom t) = case t of
  Signed _ r -> Just $ go r
  Unsigned _ _ _ r -> Just $ go r
  Elem x -> Just $ go (Elem x)
  Empty -> Nothing
  where
    go :: Subtree a C -> Int
    go (Unsigned _ _ _ r) = go r
    go (Max x) = x
    go (Elem x) = x

-- |
-- >>> fromList [] == empty
-- True
-- >>> fromList [5, 3, 5] == fromList [5, 3]
-- True
fromList :: [Int] -> Dom
fromList = List.foldl' (flip insert) empty

fromSubtree :: Subtree a b -> Tree t a b
fromSubtree t = case t of
  Unsigned p m l r -> Unsigned p m l r
  Min min -> Min min
  Max max -> Max max
  Elem x -> Elem x

combine :: Subtree a a -> Subtree a a -> Root a a
combine t1 t2
  | m < 0 = if p1 < 0 then Signed t1 t2 else Signed t2 t1
  | zero p1 m = Unsigned p m t1 t2
  | otherwise = Unsigned p m t2 t1
  where
    p1 = getPrefix t1
    m = mkMask p1 (getPrefix t2)
    p = mkPrefix p1 m
{-# INLINE combine #-}

append :: Subtree a b -> Subtree b c -> Root a c
append t1 t2 = mkRoot p m t1 t2
  where
    p1 = getPrefix t1
    m = mkMask p1 (getPrefix t2)
    p = mkPrefix p1 m
{-# INLINE append #-}

unsafeAppend :: Subtree a b -> Subtree b c -> Tree t a c
unsafeAppend t1 t2 = Unsigned p m t1 t2
  where
    p1 = getPrefix t1
    m = mkMask p1 (getPrefix t2)
    p = mkPrefix p1 m
{-# INLINE unsafeAppend #-}

unsafeInsertMin :: Int -> Subtree O b -> Tree t C b
unsafeInsertMin x = x `seq` go
  where
    go :: Subtree O b -> Tree t C b
    go t@(Unsigned p m l r)
      | mkPrefix x m /= p = unsafeAppend (Min x) t
      | otherwise = Unsigned p m (go l) r
    go t@(Max _) = unsafeAppend (Min x) t

unsafeInsertMax :: Int -> Subtree a O -> Tree t a C
unsafeInsertMax x = x `seq` go
  where
    go :: Subtree a O -> Tree t a C
    go t@(Unsigned p m l r)
      | mkPrefix x m /= p = unsafeAppend t (Max x)
      | otherwise = Unsigned p m l (go r)
    go t@(Min _) = unsafeAppend t (Max x)

getPrefix :: Subtree a b -> Prefix
getPrefix (Unsigned p _ _ _) = p
getPrefix (Min min) = min
getPrefix (Max max) = max
getPrefix (Elem x) = x
{-# INLINE getPrefix #-}

mkRoot :: Prefix -> Mask -> Subtree a b -> Subtree b c -> Root a c
mkRoot p m
  | m < 0 = Signed
  | otherwise = Unsigned p m
{-# INLINE mkRoot #-}

zero :: Int -> Mask -> Prelude.Bool
zero i m = toWord i .&. toWord m == 0
{-# INLINE zero #-}

mkMask :: Prefix -> Prefix -> Mask
mkMask =
  curry $ last . next 32 . next 16 . next 8 . next 4 . next 2 . next 1 . init
  where
    init = uncurry (xor `on` toWord)
    next = (.|.) <=< flip (.>>.)
    last = fromWord <$> (xor =<< (.>>. 1))
    (.>>.) = shiftR
{-# INLINE mkMask #-}

mkPrefix :: Int -> Mask -> Prefix
mkPrefix i m = fromWord $ toWord i .&. (complement (m' - 1) `xor` m')
  where
    m' = toWord m
{-# INLINE mkPrefix #-}

toWord :: Int -> Word
toWord = fromIntegral
{-# INLINE toWord #-}

fromWord :: Word -> Int
fromWord = fromIntegral
{-# INLINE fromWord #-}

data Pair a = {-# UNPACK #-} !Int :*: a

data StrictPair a = {-# UNPACK #-} !Int :*! !a

#if defined(LANGUAGE_DataKinds) && defined(LANGUAGE_PolyKinds)
type family IfC (s :: S) a b
#else
type family IfC s a b
#endif
type instance IfC C a b = a
type instance IfC O a b = b

data Bool a b c where
  True :: Bool a b a
  False :: Bool a b b

ifThenElse :: Bool a b c -> (c ~ a => d) -> (c ~ b => d) -> d
ifThenElse x t f = case x of
  True -> t
  False -> f

not :: Bool a b c -> Bool b a c
not x = case x of
  True -> False
  False -> True

toBool :: Bool a b c -> Prelude.Bool
toBool x = case x of
  True -> Prelude.True
  False -> Prelude.False

infixr 9 .
infixr 1 >>>

class Semigroupoid c where
  (.) :: c j k -> c i j -> c i k

(>>>) :: Semigroupoid c => c i j -> c j k -> c i k
f >>> g = g . f

class Semigroupoid c => Object i c where
  id :: c i i

instance Semigroupoid (->) where
  (.) = (Prelude..)
  {-# INLINE (.) #-}

instance Object i (->) where
  id = Prelude.id
  {-# INLINE id #-}

data WithId i c j k where
  Semigroupoid :: !(c j k) -> WithId i c j k
  Id :: WithId i c i i

instance Semigroupoid c => Semigroupoid (WithId i c) where
  f . Id = f
  Id . g = g
  Semigroupoid f . Semigroupoid g = Semigroupoid (f . g)

instance Semigroupoid c => Object i (WithId i c) where
  id = Id

type WithFull = WithId O
type WithEmpty = WithId C

wrap :: c j k -> WithId i c j k
wrap = Semigroupoid

class Unwrap i j k where unwrap :: WithId i c j k -> c j k
instance Unwrap C C O where unwrap (Semigroupoid f) = f
instance Unwrap C O C where unwrap (Semigroupoid f) = f
instance Unwrap O C C where unwrap (Semigroupoid f) = f
instance Unwrap C O O where unwrap (Semigroupoid f) = f
instance Unwrap O C O where unwrap (Semigroupoid f) = f
instance Unwrap O O C where unwrap (Semigroupoid f) = f

toRoot :: WithEmpty Subtree a b -> Root a b
toRoot w = case w of
  Semigroupoid t -> fromSubtree t
  Id -> Empty

instance Semigroupoid Subtree where
  (.) = flip unsafeAppend