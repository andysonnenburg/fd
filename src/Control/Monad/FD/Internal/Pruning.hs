module Control.Monad.FD.Internal.Pruning
       ( Pruning, affectedBy, dom, min, max, val
       ) where

import Data.Semigroup (Semigroup ((<>)))

import Prelude hiding (max, min)

data Pruning
  = Dom
  | Min
  | Max
  | MinMax
  | Val

instance Semigroup Pruning where
  Val <> _ = Val
  _ <> Val = Val
  MinMax <> _ = MinMax
  _ <> MinMax = MinMax
  Min <> Max = MinMax
  Max <> Min = MinMax
  Min <> _ = Min
  _ <> Min = Min
  Max <> _ = Max
  _ <> Max = Max
  Dom <> Dom = Dom

affectedBy :: Pruning -> Pruning -> Bool
_ `affectedBy` Val = True
Dom `affectedBy` _ = True
MinMax `affectedBy` MinMax = True
MinMax `affectedBy` Min = True
MinMax `affectedBy` Max = True
Min `affectedBy` Min = True
Max `affectedBy` Max = True
_ `affectedBy` _ = False

dom :: Pruning
dom = Dom

min :: Pruning
min = Min

max :: Pruning
max = Max

val :: Pruning
val = Val
