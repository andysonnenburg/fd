{-# LANGUAGE
    MultiParamTypeClasses
  , RebindableSyntax
  , RecordWildCards #-}
module Control.Monad.FD
       ( FD
       , runFD
       , FDT
       , runFDT
       , Term
       , freshTerm
       , fromVar
       , fromInt
       , IsInteger (fromInteger)
       , Sum ((+), (-), negate)
       , Product ((*))
       , Quotient (quot, div)
       , (#=)
       , (#<)
       , (#<=)
       , (#>)
       , (#>=)
       , label
       ) where

import Control.Applicative
import Control.Monad (liftM, liftM2)

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Monoid (mempty)

import Prelude hiding (Num (..), div, fromIntegral, max, min, quot)

import Control.Monad.FD.Internal hiding (Term, label, max, min)
import qualified Control.Monad.FD.Internal as Internal
import Control.Monad.FD.Internal.Int

data Term s = Term (HashMap (Var s) Int) Int

freshTerm :: Monad m => FDT s m (Term s)
freshTerm = liftM fromVar freshVar

fromVar :: Var s -> Term s
fromVar = flip Term 0 . flip HashMap.singleton 1

fromInt :: Int -> Term s
fromInt = Term HashMap.empty

instance Bounded (Term s) where
  minBound = fromInt minBound
  maxBound = fromInt maxBound

instance IsInteger (Term s) where
  fromInteger = Term mempty . fromInteger

instance Sum (Term s) (Term s) where
  Term x1 y1 + Term x2 y2 =
    Term (HashMap.unionWith (+!) x1 x2) (y1 +! y2)
  Term x1 y1 - Term x2 y2 =
    Term (HashMap.unionWith (+!) x1 (negate <$> x2)) (y1 -! y2)
  negate (Term x y) =
    Term (negate <$> x) (negate y)

instance Product Int (Term s) (Term s) where
  a * Term x c = Term ((a *!) <$> x) (a *! c)

instance Product (Term s) Int (Term s) where
  Term x c * a = Term ((*! a) <$> x) (c *! a)

infix 4 #=, #<, #<=, #>, #>=
(#=), (#<), (#<=), (#>), (#>=) :: Monad m => Term s -> Term s -> FDT s m ()

Term x1 c1 #= Term x2 c2 = tell $ i1 ++ i2
  where
    i1 = [ x `in'` min #.. max
         | let xs = HashMap.unionWith (+) x2 (negate <$> x1)
         , let c = fromIntegral $ c2 -! c1
         , (x, a) <- HashMap.toList x1
         , let (min, max) = interval (HashMap.delete x xs) c a
         ]
    i2 = [ x `in'` min #.. max
         | let xs = HashMap.unionWith (+) x1 (negate <$> x2)
         , let c = fromIntegral $ c1 -! c2
         , (x, a) <- HashMap.toList x2
         , let (min, max) = interval (HashMap.delete x xs) c a
         ]

a #< b = a + 1 #<= b

Term x1 c1 #<= Term x2 c2 = tell $ i1 ++ i2
  where
    i1 = [ x `in'` min' #.. max'
         | let xs = HashMap.unionWith (+) x2 (negate <$> x1)
         , let c = fromIntegral $ c2 -! c1
         , (x, a) <- HashMap.toList x1
         , let (min, max) = interval (HashMap.delete x xs) c a
         , let (min', max') | a >= 0 = (minBound, max)
                            | otherwise = (min, maxBound)
         ]
    i2 = [ x `in'` min' #.. max'
         | let xs = HashMap.unionWith (+) x1 (negate <$> x2)
         , let c = fromIntegral $ c1 -! c2
         , (x, a) <- HashMap.toList x2
         , let (min, max) = interval (HashMap.delete x xs) c a
         , let (min', max') | a >= 0 = (min, maxBound)
                            | otherwise = (minBound, max)
         ]

(#>) = flip (#<)

(#>=) = flip (#<=)

interval :: HashMap (Var s) Int -> Int -> Int ->
            (Internal.Term s, Internal.Term s)
interval x c a
  | a >= 0 = (minTerm', maxTerm')
  | otherwise = (maxTerm', minTerm')
  where
    minTerm' = minTerm `quot` a
    maxTerm' = maxTerm `quot` a
    Interval {..} = HashMap.foldlWithKey' f (Interval c' c') x
    f i@(Interval min max) k v = case compare v 0 of
      GT -> Interval (min + v * Internal.min k) (max + v * Internal.max k)
      EQ -> i
      LT -> Interval (min + v * Internal.max k) (max + v * Internal.min k)
    c' = fromIntegral c

data Interval s =
  Interval { minTerm :: !(Internal.Term s)
           , maxTerm :: !(Internal.Term s)
           }

label :: Monad m => Term s -> FDT s m Int
label (Term x y) =
  HashMap.foldlWithKey' f (return $ fromIntegral y) x
  where
    f a k v = liftM2 (+) a (liftM (v *) $ Internal.label k)

fromIntegral :: (Integral a, IsInteger b) => a -> b
fromIntegral = fromInteger . toInteger
