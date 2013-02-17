module Data.Int.Dom.Common
       ( Mask
       , mkMask
       , negative
       , zero
       , Depth
       , depth
       , Prefix
       , mkPrefix
       ) where

import Control.Monad ((<=<))

import Data.Bits
import Data.Function (on)
import Data.Functor ((<$>))
import Data.Word (Word)

import Prelude hiding (init, last)

newtype Mask = Mask Int

mkMask :: Prefix -> Prefix -> Mask
mkMask =
  curry $ last . next 32 . next 16 . next 8 . next 4 . next 2 . next 1 . init
  where
    init = uncurry (xor `on` toWord)
    next = (.|.) <=< flip (.>>.)
    last = Mask . fromWord <$> (xor =<< (.>>. 1))
    (.>>.) = shiftR
{-# INLINE mkMask #-}

negative :: Mask -> Bool
negative (Mask m) = m < 0
{-# INLINE negative #-}

zero :: Int -> Mask -> Bool
zero i (Mask m) = toWord i .&. toWord m == 0
{-# INLINE zero #-}

newtype Depth = Depth Mask

instance Eq Depth where
  Depth (Mask m1) == Depth (Mask m2) = m1 == m2
  Depth (Mask m1) /= Depth (Mask m2) = m1 /= m2

depth :: Mask -> Depth
depth = Depth
{-# INLINE depth #-}

instance Ord Depth where
  Depth (Mask m1) <= Depth (Mask m2) = toWord m1 >= toWord m2
  {-# INLINE (<=) #-}

type Prefix = Int

mkPrefix :: Int -> Mask -> Prefix
mkPrefix i (Mask m) = fromWord $ toWord i .&. (complement (m' - 1) `xor` m')
  where
    m' = toWord m
{-# INLINE mkPrefix #-}

toWord :: Int -> Word
toWord = fromIntegral
{-# INLINE toWord #-}

fromWord :: Word -> Int
fromWord = fromIntegral
{-# INLINE fromWord #-}