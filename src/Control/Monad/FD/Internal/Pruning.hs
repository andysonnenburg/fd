module Control.Monad.FD.Internal.Pruning
       ( Pruning, join, affectedBy, dom, min, max, val
       ) where

import Prelude hiding (max, min)

data Pruning
  = Dom
  | Min
  | Max
  | MinMax
  | Val

join :: Pruning -> Pruning -> Pruning
join Val _ = Val
join _ Val = Val
join MinMax _ = MinMax
join _ MinMax = MinMax
join Min Max = MinMax
join Max Min = MinMax
join Min _ = Min
join _ Min = Min
join Max _ = Max
join _ Max = Max
join Dom Dom = Dom

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
