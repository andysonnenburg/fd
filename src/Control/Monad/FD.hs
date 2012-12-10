{-# LANGUAGE
    MultiParamTypeClasses
  , RecordWildCards #-}
module Control.Monad.FD
       ( FD
       , runFD
       , FDT
       , runFDT
       , Term
       , freshTerm
       , Sum ((+), (-), negate, fromInteger)
       , Product ((*))
       , Quotient (quot, div)
       , (#=)
       , (#>=)
       , label
       ) where

import Control.Applicative
import Control.Monad (liftM, liftM2)

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Monoid (mempty)

import Prelude hiding (Num (..), div, fromIntegral, max, min, quot)
import Prelude (abs)

import Control.Monad.FD.Internal hiding (Term, label, max, min)
import qualified Control.Monad.FD.Internal as Internal

data Term s = Term (HashMap (Var s) Int) Int

freshTerm :: Monad m => FDT s m (Term s)
freshTerm = liftM (flip Term 0 . flip HashMap.singleton 1) freshVar

instance Sum (Term s) where
  Term x1 y1 + Term x2 y2 =
    Term (HashMap.unionWith (+) x1 x2) (y1 + y2)
  Term x1 y1 - Term x2 y2 =
    Term (HashMap.unionWith (+) x1 (negate <$> x2)) (y1 - y2)
  negate (Term x y) =
    Term (negate <$> x) (negate y)
  fromInteger =
    Term mempty . fromInteger

instance Product Int (Term s) where
  a * Term x y = Term ((a *) <$> x) (a * y)

infix 4 #=
(#=) :: Monad m => Term s -> Term s -> FDT s m ()
Term x1 y1 #= Term x2 y2 = tell $ i1 ++ i2
  where
    i1 = for (HashMap.toList x1) $ \ (k, v) ->
      let x' = HashMap.delete k x
          (min, max) = extrema x' y v
      in k `in'` min :.. max
      where
        x = HashMap.unionWith (+) x2 (negate <$> x1)
        y = fromIntegral $ y2 - y1
    i2 = for (HashMap.toList x2) $ \ (k, v) ->
      let x' = HashMap.delete k x
          (min, max) = extrema x' y v
      in k `in'` min :.. max
      where
        x = HashMap.unionWith (+) x1 (negate <$> x2)
        y = fromIntegral $ y1 - y2

(#>=) :: Monad m => Term s -> Term s -> FDT s m ()
Term x1 y1 #>= Term x2 y2 = tell $ i1 ++ i2
  where
    i1 = for (HashMap.toList x1) $ \ (k, v) ->
      let x' = HashMap.delete k x
          (min, max) = extrema x' y v
          (min', max') = case compare v 0 of
            GT -> (min, maxBound)
            EQ -> (fromInteger 0, fromInteger 0)
            LT -> (minBound, max)
      in k `in'` min' :.. max'
      where
        x = HashMap.unionWith (+) x2 (negate <$> x1)
        y = fromIntegral $ y2 - y1
    i2 = for (HashMap.toList x2) $ \ (k, v) ->
      let x' = HashMap.delete k x
          (min, max) = extrema x' y v
          (min', max') = case compare v 0 of
            GT -> (minBound, max)
            EQ -> (fromInteger 0, fromInteger 0)
            LT -> (min, maxBound)
      in k `in'` min' :.. max'
      where
        x = HashMap.unionWith (+) x1 (negate <$> x2)
        y = fromIntegral $ y1 - y2

extrema :: HashMap (Var s) Int -> Int -> Int ->
           (Internal.Term s, Internal.Term s)
extrema x c q
  | q >= 0 = (minTerm', maxTerm')
  | otherwise = (maxTerm', minTerm')
  where
    minTerm' = minTerm `quot` q
    maxTerm' = maxTerm `quot` q
    Interval {..} = HashMap.foldlWithKey' f a x
    f i@(Interval min max) k v = case compare v 0 of
      GT -> Interval (min + v * Internal.min k) (max + v * Internal.max k)
      EQ -> i
      LT -> Interval (min + v * Internal.max k) (max + v * Internal.min k)
    a = Interval { minTerm = c', maxTerm = c' }
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

fromIntegral :: (Integral a, Sum b) => a -> b
fromIntegral = fromInteger . toInteger

for :: [a] -> (a -> b) -> [b]
for = flip map
