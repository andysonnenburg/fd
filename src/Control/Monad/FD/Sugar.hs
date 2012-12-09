{-# LANGUAGE FunctionalDependencies, MultiParamTypeClasses #-}
module Control.Monad.FD.Sugar
       ( FD
       , runFD
       , FDT
       , runFDT
       , Var
       , freshVar
       , Term
       , Sum ((+), (-), negate, fromInteger)
       , Product ((*))
       , Quotient (quot, div)
       , min
       , max
       , Range ((:..))
       , dom
       , Indexical
       , in'
       , tell
       , label
       ) where

import Control.Monad.FD

import Prelude hiding ((+), (-), (*), fromInteger, max, min)
import qualified Prelude

infixl 6 +, -
class Sum a where
  (+) :: a -> a -> a
  (-) :: a -> a -> a
  negate :: a -> a
  negate = (fromInteger 0 -)
  fromInteger :: Integer -> a

infixl 7 *
class (Sum a, Sum b, Sum c) => Product a b c | a b -> c where
  (*) :: a -> b -> c

class (Sum a, Sum b) => Quotient a b | a -> b where
  quot :: a -> b -> a
  div :: a -> b -> a

instance Sum Int where
  (+) = (Prelude.+)
  (-) = (Prelude.-)
  negate = Prelude.negate
  fromInteger = Prelude.fromInteger

instance Product Int Int Int where
  (*) = (Prelude.*)

instance Quotient Int Int where
  quot = Prelude.quot
  div = Prelude.div

instance Sum (Term s) where
  (+) = (:+)
  (-) = (:-)
  fromInteger = Int . fromInteger

instance Product Int (Term s) (Term s) where
  (*) = (:*)

instance Product (Term s) Int (Term s) where
  (*) = flip (:*)

instance Quotient (Term s) Int where
  quot = Quot
  div = Div

min :: Var s -> Term s
min = Min

max :: Var s -> Term s
max = Max

dom :: Var s -> Range s
dom = Dom

infixr 1 `in'`
in' :: Var s -> Range s -> Indexical s
in' = In
