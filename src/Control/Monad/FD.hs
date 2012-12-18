{-# LANGUAGE
    MultiParamTypeClasses
  , RebindableSyntax #-}
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
       , Multiplicative (..)
       , Integral (..)
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
import Control.Arrow
import Control.Monad (guard, liftM, liftM2)

import Data.Monoid (mempty)
import Data.Tuple (swap)

import Prelude hiding (Fractional (..),
                       Num (..),
                       Integral (..),
                       fromIntegral, max, min)
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
freshTerm = liftM fromVar freshVar

fromVar :: Var s -> Term s
fromVar = flip Term 0 . flip IntMap.singleton 1

fromInt :: Int -> Term s
fromInt = Term IntMap.empty

instance Bounded (Term s) where
  minBound = fromInt minBound
  maxBound = fromInt maxBound

instance Additive (Term s) where
  Term x1 y1 + Term x2 y2 =
    Term (IntMap.unionWith (+!) x1 x2) (y1 +! y2)
  Term x1 y1 - Term x2 y2 =
    Term (IntMap.unionWith (+!) x1 (negate <$> x2)) (y1 -! y2)
  negate (Term x y) =
    Term (negate <$> x) (negate y)
  fromInteger =
    Term mempty . fromInteger

instance Multiplicative Int (Term s) (Term s) where
  a * Term x c = Term ((a *!) <$> x) (a *! c)

instance Multiplicative (Term s) Int (Term s) where
  Term x c * a = Term ((*! a) <$> x) (c *! a)

infix 4 #=, #/=, #<, #<=, #>, #>=
(#=), (#/=), (#<), (#<=), (#>), (#>=) :: Term s -> Term s -> FDT s m ()

Term x1 c1 #= Term x2 c2
  | IntMap.null x1 && IntMap.null x2 =
    guard $ c1 == c2
  | otherwise =
    tell $
    [ x `in'` min #.. max
    | let xs = IntMap.unionWith (+) x2 (negate <$> x1)
          c = fromIntegral $ c2 -! c1
    , (x, a) <- IntMap.toList x1
    , let (min, max) = bounds (IntMap.delete x xs) c a
    ] ++
    [ x `in'` min #.. max
    | let xs = IntMap.unionWith (+) x1 (negate <$> x2)
          c = fromIntegral $ c1 -! c2
    , (x, a) <- IntMap.toList x2
    , let (min, max) = bounds (IntMap.delete x xs) c a
    ]

Term x1 c1 #/= Term x2 c2
  | IntMap.null x1 && IntMap.null x2 =
    guard $ c1 /= c2
  | otherwise =
    tell $
    [ x `in'` complement (min #.. max)
    | let xs = IntMap.unionWith (+) x2 (negate <$> x1)
          c = fromIntegral $ c2 -! c1
    , (x, a) <- IntMap.toList x1
    , let (min, max) = bounds (IntMap.delete x xs) c a
    ] ++
    [ x `in'` complement (min #.. max)
    | let xs = IntMap.unionWith (+) x1 (negate <$> x2)
          c = fromIntegral $ c1 -! c2
    , (x, a) <- IntMap.toList x2
    , let (min, max) = bounds (IntMap.delete x xs) c a
    ]

Term x1 c1 #< Term x2 c2
  | IntMap.null x1 && IntMap.null x2 =
    guard $ c1 < c2
  | otherwise =
    tell $
    [ x `in'` complement (min #.. max)
    | let xs = IntMap.unionWith (+) x2 (negate <$> x1)
          c = fromIntegral $ c2 -! c1
    , (x, a) <- IntMap.toList x1
    , let r = bounds (IntMap.delete x xs) c a
          (min, max) | a >= 0 = (fst r, maxBound)
                     | otherwise = (minBound, snd r)
    ] ++
    [ x `in'` complement (min #.. max)
    | let xs = IntMap.unionWith (+) x1 (negate <$> x2)
          c = fromIntegral $ c1 -! c2
    , (x, a) <- IntMap.toList x2
    , let r = bounds (IntMap.delete x xs) c a
          (min, max) | a >= 0 = (minBound, snd r)
                     | otherwise = (fst r, maxBound)
    ]

Term x1 c1 #<= Term x2 c2
  | IntMap.null x1 && IntMap.null x2 =
    guard $ c1 <= c2
  | otherwise =
    tell $
    [ x `in'` min #.. max
    | let xs = IntMap.unionWith (+) x2 (negate <$> x1)
          c = fromIntegral $ c2 -! c1
    , (x, a) <- IntMap.toList x1
    , let r = bounds (IntMap.delete x xs) c a
          (min, max) | a >= 0 = (minBound, snd r)
                     | otherwise = (fst r, maxBound)
    ] ++
    [ x `in'` min #.. max
    | let xs = IntMap.unionWith (+) x1 (negate <$> x2)
          c = fromIntegral $ c1 -! c2
    , (x, a) <- IntMap.toList x2
    , let r = bounds (IntMap.delete x xs) c a
          (min, max) | a >= 0 = (fst r, maxBound)
                     | otherwise = (minBound, snd r)
    ]

(#>) = flip (#<)

(#>=) = flip (#<=)

distinct :: [Term s] -> FDT s m ()
distinct [] =
  return ()
distinct (x:xs) = do
  mapM_ (x #/=) xs
  distinct xs

type Bounds s = (Internal.Term s, Internal.Term s)

bounds :: IntMap (Var s) Factor -> Addend -> Divisor -> Bounds s
bounds xs c a =
  (`div'` a) *** (`div` a) <<<
  whenA (a < 0) swap $
  IntMap.foldrWithKey f (pair $ fromIntegral c) xs
  where
    f x v = case compare v 0 of
      GT -> (+ v * Internal.min x) *** (+ v * Internal.max x)
      EQ -> id
      LT -> (+ v * Internal.max x) *** (+ v * Internal.min x)

label :: Term s -> FDT s m Int
label (Term x y) =
  IntMap.foldlWithKey' f (return $ fromIntegral y) x
  where
    f a k v = liftM2 (+) a $ liftM (v *) $ Internal.label k

infixl 7 `div'`
div' :: Internal.Term s -> Int -> Internal.Term s
div' a b = (a + Internal.fromInt (b - 1)) `div` b

fromIntegral :: (Prelude.Integral a, Additive b) => a -> b
fromIntegral = fromInteger . Prelude.toInteger

whenA :: Arrow a => Bool -> a b b -> a b b
whenA True a = a
whenA False _ = arr id

pair :: a -> (a, a)
pair a = (a, a)
