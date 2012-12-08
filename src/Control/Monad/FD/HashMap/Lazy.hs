module Control.Monad.FD.HashMap.Lazy
       ( module Data.HashMap.Lazy
       , forWithKeyM_
       ) where

import Data.HashMap.Lazy

forWithKeyM_ :: Monad m => HashMap k v -> (k -> v -> m b) -> m ()
forWithKeyM_ xs f = foldrWithKey (\ k v a -> f k v >> a) (return ()) xs
