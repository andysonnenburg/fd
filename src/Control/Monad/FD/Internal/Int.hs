{-# LANGUAGE CPP #-}
#ifdef __GLASGOW_HASKELL__
{-# LANGUAGE MagicHash, UnboxedTuples #-}
#endif
module Control.Monad.FD.Internal.Int ((+!), (-!), (*!)) where

#ifdef __GLASGOW_HASKELL__
import GHC.Exts (Int (I#),
                 (*#),
#ifdef PACKAGE_integer_gmp
                 (>#),
#endif
                 (==#),
                 (<#),
                 addIntC#,
                 mulIntMayOflo#,
                 subIntC#)
#endif
#ifdef PACKAGE_integer_gmp
import GHC.Integer.GMP.Prim (cmpIntegerInt#,
                             int2Integer#,
                             integer2Int#,
                             timesInteger#)
#endif

infixl 6 +!
(+!) :: Int -> Int -> Int
#ifdef __GLASGOW_HASKELL__
I# i +! I# j =
  case addIntC# i j of
    (# r, c #)
      | c ==# 0# -> I# r
      | r <# 0# -> maxBound
      | otherwise -> minBound
#else
a +! b =
  case toInteger a + toInteger b of
    r | r < toInteger (minBound :: Int) -> minBound
      | r > toInteger (maxBound :: Int) -> maxBound
      | otherwise -> fromInteger r
#endif

infixl 6 -!
(-!) :: Int -> Int -> Int
#ifdef __GLASGOW_HASKELL__
I# a -! I# b =
  case subIntC# a b of
    (# r, c #)
      | c ==# 0# -> I# r
      | r <# 0# -> maxBound
      | otherwise -> minBound
#else
a -! b =
  case toInteger a - toInteger b of
    r | r < toInteger (minBound :: Int) -> minBound
      | r > toInteger (maxBound :: Int) -> maxBound
      | otherwise -> fromInteger r
#endif

infixl 7 *!
(*!) :: Int -> Int -> Int
#ifdef __GLASGOW_HASKELL__
#ifdef PACKAGE_integer_gmp
{-# NOINLINE (*!) #-}
I# i *! I# j =
  if mulIntMayOflo# i j ==# 0#
  then I# (i *# j)
  else case int2Integer# i of
    (# s1, d1 #) -> case int2Integer# j of
      (# s2, d2 #) -> case timesInteger# s1 d1 s2 d2 of
        (# s, d #) -> case minBound of
          I# minBound# ->
            if cmpIntegerInt# s d minBound# <# 0#
            then minBound
            else case maxBound of
              I# maxBound# ->
                if cmpIntegerInt# s d maxBound# ># 0#
                then maxBound
                else I# (integer2Int# s d)
#else
a@(I# i) *! b@(I# j) =
  if mulIntMayOflo# i j ==# 0#
  then I# (i *# j)
  else case toInteger a * toInteger b of
    r | r < toInteger (minBound :: Int) -> minBound
      | r > toInteger (maxBound :: Int) -> maxBound
      | otherwise -> fromInteger r
#endif
#else
a *! b =
  case toInteger a * toInteger b of
    r | r < toInteger (minBound :: Int) -> minBound
      | r > toInteger (maxBound :: Int) -> maxBound
      | otherwise -> fromInteger r
#endif
