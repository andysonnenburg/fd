module Control.Monad.FD.Internal.HashMap
       ( module Data.HashMap.Strict
       , forWithKeyM_
       ) where

import Data.HashMap.Strict

forWithKeyM_ :: Monad m => HashMap k v -> (k -> v -> m b) -> m ()
forWithKeyM_ xs f = foldrWithKey (\ k v a -> f k v >> a) (return ()) xs
