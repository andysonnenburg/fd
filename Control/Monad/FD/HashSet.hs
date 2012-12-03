module Control.Monad.FD.HashSet
       ( module Data.HashSet
       , forM_
       ) where

import Data.HashSet

import Prelude hiding (foldr)

forM_ :: Monad m => HashSet a -> (a -> m b) -> m ()
forM_ xs f = foldr ((>>) . f) (return ()) xs
