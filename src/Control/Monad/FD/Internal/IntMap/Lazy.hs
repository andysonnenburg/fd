module Control.Monad.FD.Internal.IntMap.Lazy
       ( module Data.IntMap.Lazy
       , deleteGE
       , deleteLE
       ) where

import Data.IntMap.Lazy

import Prelude
import qualified Prelude

deleteGE :: Key -> IntMap a -> IntMap a
deleteGE k = fst . split k

deleteLE :: Key -> IntMap a -> IntMap a
deleteLE k = snd . split k
