{-# LANGUAGE
    FlexibleInstances
  , FunctionalDependencies
  , MultiParamTypeClasses
  , RebindableSyntax
  , RecordWildCards
  , UndecidableInstances #-}
module Control.Monad.FD
       ( FD
       , runFD
       , FDT
       , runFDT
       , Term
       , freshTerm
       , fromVar
       , fromInt
       , Additive (..)
       , subtract
       , fromIntegral
       , Multiplicative (..)
       , Fractional (..)
       , (#=)
       , (#/=)
       , (#<)
       , (#<=)
       , (#>)
       , (#>=)
       , distinct
       , label
       ) where

import Control.Applicative
import Control.Category (Category, id)
import Control.Monad (guard)

import Data.Monoid (mempty)

import Prelude hiding (Fractional (..),
                       Integral (..),
                       Num (..),
                       fromIntegral,
                       id,
                       mapM,
                       max,
                       min,
                       subtract)
import qualified Prelude

import Control.Monad.FD.Internal hiding (Term, fromInt, label, max, min)
import qualified Control.Monad.FD.Internal as Internal
import Control.Monad.FD.Internal.Int
import Control.Monad.FD.Internal.IntMap.Strict (IntMap)
import qualified Control.Monad.FD.Internal.IntMap.Strict as IntMap

data Term s = Term !(IntMap (Var s) Factor) {-# UNPACK #-} !Addend
type Factor = Int
type Addend = Int
type Divisor = Int

freshTerm :: FDT s m (Term s)
freshTerm = fromVar <$> freshVar

fromVar :: Var s -> Term s
fromVar = flip Term 0 . flip IntMap.singleton 1

fromInt :: Int -> Term s
fromInt = Term IntMap.empty

instance Bounded (Term s) where
  minBound = fromInt minBound
  maxBound = fromInt maxBound

instance Additive (Term s) where
  Term xs1 c1 + Term xs2 c2 =
    Term (IntMap.unionWith (+!) xs1 xs2) (c1 +! c2)
  Term xs1 c1 - Term xs2 c2 =
    Term (xs1 `minusIntMap` xs2) (c1 -! c2)
  negate (Term x y) =
    Term (negate <$> x) (negate y)
  fromInteger =
    Term mempty . fromInteger

minusIntMap :: IntMap k Int -> IntMap k Int -> IntMap k Int
minusIntMap = IntMap.mergeWithKey f id (fmap negate)
  where
    f _ x1 x2 = case x1 -! x2 of
      0 -> Nothing
      x -> Just x

instance Multiplicative Int (Term s) (Term s) where
  a * Term x c = Term ((a *!) <$> x) (a *! c)

instance Multiplicative (Term s) Int (Term s) where
  Term x c * a = Term ((*! a) <$> x) (c *! a)

infix 4 #=, #/=, #<, #<=, #>, #>=
(#=), (#/=), (#<), (#<=), (#>), (#>=) :: Term s -> Term s -> FDT s m ()

Term xs1 c1 #= Term xs2 c2
  | IntMap.null xs =
    guard $ c == 0
  | otherwise =
    tell
    [ x `in'` minTerm #.. maxTerm
    | (x, a) <- IntMap.toList xs
    , let Bounds {..} = bounds (IntMap.delete x xs) c a
    ]
  where
    xs = xs1 `minusIntMap` xs2
    c = c1 -! c2

Term xs1 c1 #/= Term xs2 c2
  | IntMap.null xs =
    guard $ c /= 0
  | otherwise =
    tell
    [ x `in'` complement (minTerm #.. maxTerm)
    | (x, a) <- IntMap.toList xs
    , let Bounds {..} = bounds (IntMap.delete x xs) c a
    ]
  where
    xs = xs1 `minusIntMap` xs2
    c = c1 -! c2

Term xs1 c1 #< Term xs2 c2
  | IntMap.null xs =
    guard $ c < 0
  | otherwise =
    tell
    [ x `in'` complement (min #.. max)
    | (x, a) <- IntMap.toList xs
    , let Bounds {..} = bounds (IntMap.delete x xs) c a
          (min, max) | a >= 0 = (minTerm, maxBound)
                     | otherwise = (minBound, maxTerm)
    ]
  where
    xs = xs1 `minusIntMap` xs2
    c = c1 -! c2

Term xs1 c1 #<= Term xs2 c2
  | IntMap.null xs =
    guard $ c <= 0
  | otherwise =
    tell
    [ x `in'` min #.. max
    | (x, a) <- IntMap.toList xs
    , let Bounds {..} = bounds (IntMap.delete x xs) c a
          (min, max) | a >= 0 = (minBound, maxTerm)
                     | otherwise = (minTerm, maxBound)
    ]
  where
    xs = xs1 `minusIntMap` xs2
    c = c1 -! c2

(#>) = flip (#<)

(#>=) = flip (#<=)

distinct :: [Term s] -> FDT s m ()
distinct [] =
  return ()
distinct (x:xs) = do
  mapM_ (x #/=) xs
  distinct xs

data Bounds s =
  Bounds { minTerm :: Internal.Term s
         , maxTerm :: Internal.Term s
         }

bounds :: IntMap (Var s) Factor -> Addend -> Divisor -> Bounds s
bounds xs b0 a = IntMap.foldrWithKey (\ k v b -> b - v * varBounds k) b0' xs / a
  where
    b0' = fromIntegral $ negate b0

varBounds :: Var s -> Bounds s
varBounds x = Bounds (Internal.min x) (Internal.max x)

instance Additive (Bounds s) where
  Bounds min max + Bounds min' max' = Bounds (min + min') (max + max')
  Bounds min max - Bounds min' max' = Bounds (min - max') (max - min')
  fromInteger i = Bounds x x
    where
      x = fromInteger i

instance Multiplicative Int (Bounds s) (Bounds s) where
  x * Bounds {..}
    | x >= 0 = Bounds (x * minTerm) (x * maxTerm)
    | otherwise = Bounds (x * maxTerm) (x * minTerm)

instance Multiplicative (Bounds s) Int (Bounds s) where
  (*) = flip (*)

instance Fractional (Bounds s) Int where
  Bounds {..} / x
    | x >= 0 = Bounds (minTerm `div'` x) (maxTerm `div` x)
    | otherwise = Bounds (maxTerm `div'` x) (minTerm `div` x)

label :: Term s -> FDT s m Int
label (Term x y) =
  IntMap.foldlWithKey' f (return $ fromIntegral y) x
  where
    f a k v = (+) <$> a <*> ((v *) <$> Internal.label k)
