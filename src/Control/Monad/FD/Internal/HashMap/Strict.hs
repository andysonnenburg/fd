{-# LANGUAGE CPP #-}
#ifdef LANGUAGE_Trustworthy
{-# LANGUAGE Trustworthy #-}
#endif
module Control.Monad.FD.Internal.HashMap.Strict
       ( module Data.HashMap.Strict
       , forWithKeyM_
       , sunion
       ) where

import Data.Hashable (Hashable)
import Data.HashMap.Strict
import Data.Semigroup (Semigroup, (<>))

forWithKeyM_ :: Monad m => HashMap k v -> (k -> v -> m b) -> m ()
forWithKeyM_ xs f = foldrWithKey (\ k v a -> f k v >> a) (return ()) xs

sunion :: ( Eq k
          , Hashable k
          , Semigroup v
          ) => HashMap k v -> HashMap k v -> HashMap k v
sunion = unionWith (<>)
