module Control.Monad.FD.Pruning
       ( Pruning, join, dom, min, max, val
       ) where

import Prelude hiding (max, min)

data Pruning
  = Dom
  | Min
  | Max
  | MinMax
  | Val deriving Eq

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

dom :: Pruning
dom = Dom

min :: Pruning
min = Min

max :: Pruning
max = Max

val :: Pruning
val = Val
