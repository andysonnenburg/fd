{-# LANGUAGE
    DataKinds
  , EmptyDataDecls
  , FlexibleInstances
  , FunctionalDependencies
  , KindSignatures
  , LambdaCase
  , MultiParamTypeClasses
  , Rank2Types
  , RecordWildCards #-}
module Control.Monad.FD
       ( FD
       , runFD
       , FDT
       , runFDT
       , Var
       , freshVar
       , Term
       , fromVar
       , min
       , max
       , Range ((:..))
       , from
       , to
       , dom
       , in'
       , label
       ) where

import Control.Applicative
import Control.Monad
import Control.Monad.List (ListT (..))
import Control.Monad.State (StateT, evalStateT)
import qualified Control.Monad.State as State
import Control.Monad.Trans.Class (MonadTrans (lift))

import Data.Functor.Identity
import Data.Hashable
import Data.HashMap.Lazy (HashMap, (!))
import qualified Data.HashMap.Lazy as HashMap

import Prelude hiding (max, min)

import Control.Monad.FD.Domain (Domain)
import qualified Control.Monad.FD.Domain as Domain

type FD s = FDT s Identity

runFD :: (forall s . FD s a) -> [a]
runFD = runIdentity . runFDT

newtype FDT (s :: Region) m a =
  FDT { unFDT :: StateT (S s) (ListT m) a
      }

instance Monad m => Monad (FDT s m) where
  return = FDT . return
  m >>= k = FDT $ unFDT m >>= (unFDT . k)
  m >> n = FDT $ unFDT m >> unFDT n
  fail = FDT . fail

instance Monad m => MonadPlus (FDT s m) where
  mzero = FDT mzero
  mplus m n = FDT $ mplus (unFDT m) (unFDT n)

instance MonadTrans (FDT s) where
  lift = FDT . lift . lift

runFDT :: Monad m => (forall s . FDT s m a) -> m [a]
runFDT m = runListT . flip evalStateT initS $ unFDT m

newtype Var (s :: Region) = WrapInteger { unwrapVar :: Integer } deriving Eq

instance Hashable (Var s) where
  hash = hash . unwrapVar
  hashWithSalt salt = hashWithSalt salt . unwrapVar

data Term s
  = Var (Var s)
  | Int Int
  | Term s :+ Term s
  | Term s :- Term s
  | Term s :* Term s
  | Min (Range s)
  | Max (Range s)

fromVar :: Var s -> Term s
fromVar = Var

min :: Range s -> Term s
min = Min

max :: Range s -> Term s
max = Max

instance Num (Term s) where
  (+) = (:+)
  (*) = (:*)
  (-) = (:-)
  fromInteger = Int . fromInteger

infix 5 :..
data Range s
  = Term s :.. Term s
  | From (Term s)
  | To (Term s)
  | Dom (Var s)

from :: Term s -> Range s
from = From

to :: Term s -> Range s
to = To

dom :: Var s -> Range s
dom = Dom

pruneDomain :: Monad m => Domain -> Range s -> FDT s m (Maybe Domain)
pruneDomain d (t1 :.. t2) =
  liftM2 (,) (val t1) (val t2) >>= \ case
    (Nothing, Nothing) ->
      return Nothing
    (Just i, Nothing) ->
      return $ Domain.deleteLT i d
    (Nothing, Just i) ->
      return $ Domain.deleteGT i d
    (Just i1, Just i2) ->
      return $ Domain.intersection d (Domain.fromBounds i1 i2)
pruneDomain d (From t) =
  liftM (>>= flip Domain.deleteLT d) $ val t
pruneDomain d (To t) =
  liftM (>>= flip Domain.deleteGT d) $ val t
pruneDomain d (Dom x) =
  liftM (Domain.intersection d) $ getDomain x

val :: Monad m => Term s -> FDT s m (Maybe Int)
val (Var x) = ifDetermined x return
val (Int i) = return $ Just i
val (t1 :+ t2) = liftM2 (liftA2 (+)) (val t1) (val t2)
val (t1 :- t2) = liftM2 (liftA2 (-)) (val t1) (val t2)
val (t1 :* t2) = liftM2 (liftA2 (*)) (val t1) (val t2)
val (Min r) = minVal r
val (Max r) = maxVal r

minVal :: Monad m => Range s -> FDT s m (Maybe Int)
minVal (t :.. _) = val t
minVal (From t) = val t
minVal (To _) = return $ Just minBound
minVal (Dom x) = maybe mzero (return . Just) . Domain.lookupMin =<< getDomain x

maxVal :: Monad m => Range s -> FDT s m (Maybe Int)
maxVal (_ :.. t) = val t
maxVal (From _) = return $ Just maxBound
maxVal (To t) = val t
maxVal (Dom x) = maybe mzero (return . Just) . Domain.lookupMax =<< getDomain x

ifDetermined :: Monad m => Var s -> (Int -> FDT s m a) -> FDT s m (Maybe a)
ifDetermined x f = do
  d <- getDomain x
  case Domain.toList d of
    [i] -> liftM Just $ f i
    _ -> return Nothing

class Vars s a | a -> s where
  vars :: a -> [Var s]

instance Vars s (Term s) where
  vars (Var x) = [x]
  vars (Int _) = []
  vars (t1 :+ t2) = vars t1 ++ vars t2
  vars (t1 :- t2) = vars t1 ++ vars t2
  vars (t1 :* t2) = vars t1 ++ vars t2
  vars (Min r) = vars r
  vars (Max r) = vars r

instance Vars s (Range s) where
  vars (t1 :.. t2) = vars t1 ++ vars t2
  vars (From t) = vars t
  vars (To t) = vars t
  vars (Dom x) = [x]

data Constraint s = Var s `In` Range s

data Region

data S s = S { varCount :: Integer
             , domains :: HashMap (Var s) Domain
             , constraints :: HashMap (Var s) [Constraint s]
             }

initS :: S s
initS = S { varCount = 0
          , domains = HashMap.empty
          , constraints = HashMap.empty
          }

in' :: Monad m => Var s -> Range s -> FDT s m ()
n `in'` r = do
  let c = n `In` r
  addConstraint c
  propagateConstraint c

getDomain :: Monad m => Var s -> FDT s m Domain
getDomain x = liftM (!x) $ gets domains

putDomain :: Monad m => Var s -> Domain -> FDT s m ()
putDomain x d = modify $ \ s@S {..} ->
  s { domains = HashMap.insert x d domains }

getConstraints :: Monad m => Var s -> FDT s m [Constraint s]
getConstraints x = liftM (!x) $ gets constraints

addConstraint :: Monad m => Constraint s -> FDT s m ()
addConstraint c@(_ `In` r) = forM_ (vars r) $ \ x ->
  modify $ \ s@S {..} -> s { constraints = HashMap.adjust (c:) x constraints }

propagateConstraint :: Monad m => Constraint s -> FDT s m ()
propagateConstraint (x `In` r) = do
  s@S {..} <- get
  pruneDomain (domains!x) r >>= flip whenJust (\ d' -> do
    put s { domains = HashMap.insert x d' domains }
    mapM_ propagateConstraint (constraints!x))

label :: Monad m => Var s -> FDT s m Int
label x = do
  d <- getDomain x
  msum $ for (Domain.toList d) $ \ i -> do
    putDomain x (Domain.singleton i)
    mapM_ propagateConstraint =<< getConstraints x
    return i

freshVar :: Monad m => FDT s m (Var s)
freshVar = do
  s@S {..} <- get
  let x = WrapInteger varCount
  put s { varCount = varCount + 1
        , domains = HashMap.insert x Domain.full domains
        , constraints = HashMap.insert x [] constraints
        }
  return x

get :: Monad m => FDT s m (S s)
get = FDT State.get

put :: Monad m => S s -> FDT s m ()
put = FDT . State.put

modify :: Monad m => (S s -> S s) -> FDT s m ()
modify = FDT . State.modify

gets :: Monad m => (S s -> a) -> FDT s m a
gets = FDT . State.gets

whenJust :: Monad m => Maybe a -> (a -> m ()) -> m ()
whenJust = flip (maybe (return ()))

for :: [a] -> (a -> b) -> [b]
for = flip map
