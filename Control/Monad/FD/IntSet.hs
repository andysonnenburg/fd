module Control.Monad.FD.IntSet
       ( module Data.IntSet
       , sizeLE
       ) where

import Data.IntSet

import Prelude (Bool, Int, (.))
import qualified Prelude

sizeLE :: Int -> IntSet -> Bool
sizeLE i = Prelude.null . Prelude.take i . toList
