{-# LANGUAGE
    DataKinds
  , EmptyDataDecls
  , FunctionalDependencies
  , KindSignatures
  , MultiParamTypeClasses
  , Rank2Types
  , RecordWildCards #-}
module Control.Monad.FD.Internal
       ( FD
       , runFD
       , FDT
       , runFDT
       , Additive (..)
       , Multiplicative (..)
       , Integral (..)
       , Fractional (..)
       , Var
       , freshVar
       , Term
       , fromInt
       , min
       , max
       , Range
       , (#..)
       , dom
       , Indexical
       , in'
       , tell
       , label
       ) where

import Control.Applicative
import Control.Monad (MonadPlus (mplus, mzero),
                      liftM,
                      liftM2,
                      msum,
                      unless,
                      when)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.Logic (LogicT, observeAllT)
import Control.Monad.Trans.Class (MonadTrans (lift))

import Data.Foldable (forM_, toList)
import Data.Function (on)
import Data.Functor.Identity
import Data.Hashable (Hashable (hashWithSalt))
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Monoid (mappend, mempty)
import Data.Semigroup ((<>))
import Data.Sequence (Seq, (|>))
import Data.Tuple (swap)

import Prelude hiding (Fractional (..), Integral (..), Num (..), min, max)
import Prelude (toInteger)
import qualified Prelude

import Control.Monad.FD.Internal.Dom (Dom)
import qualified Control.Monad.FD.Internal.Dom as Dom
import Control.Monad.FD.Internal.HashMap (HashMap, (!))
import qualified Control.Monad.FD.Internal.HashMap as HashMap
import Control.Monad.FD.Internal.Int
import Control.Monad.FD.Internal.Pruning (Pruning, affectedBy)
import qualified Control.Monad.FD.Internal.Pruning as Pruning

type FD s = FDT s Identity

runFD :: (forall s . FD s a) -> [a]
runFD = runIdentity . runFDT

newtype FDT s m a =
  FDT { unFDT :: S s m -> LogicT m (PairS s m a)
      }

runFDT :: Monad m => (forall s . FDT s m a) -> m [a]
runFDT m = observeAllT $ liftM fst' $ unFDT m initS

instance Functor m => Functor (FDT s m) where
  fmap f m = FDT $ \ s -> fmap (\ (a :+: s') -> f a :+: s') $ unFDT m s

instance Applicative m => Applicative (FDT s m) where
  pure a = FDT $ \ s -> pure $ a :+: s
  f <*> a = FDT $ \ s -> do
    f' :+: s' <- unFDT f s
    a' :+: s'' <- unFDT a s'
    pure $ f' a' :+: s''

instance Applicative m => Alternative (FDT s m) where
  empty = FDT $ \ _ -> empty
  m <|> n = FDT $ \ s -> unFDT m s <|> unFDT n s

instance Monad m => Monad (FDT s m) where
  return a = FDT $ \ s -> return $ a :+: s
  m >>= k = FDT $ \ s -> do
    a :+: s' <- unFDT m s
    unFDT (k a) s'
  m >> n = FDT $ \ s -> do
    _ :+: s' <- unFDT m s
    unFDT n s'
  fail str = FDT $ \ _ -> fail str

instance Monad m => MonadPlus (FDT s m) where
  mzero = FDT $ \ _ -> mzero
  m `mplus` n = FDT $ \ s -> unFDT m s `mplus` unFDT n s

instance MonadTrans (FDT s) where
  lift m = FDT $ \ s -> do
    a <- lift m
    return $ a :+: s

instance MonadIO m => MonadIO (FDT s m) where
  liftIO = lift . liftIO

infixl 6 +, -
infixl 7 *, `quot`, `div`

class Additive a where
  (+) :: a -> a -> a
  (-) :: a -> a -> a
  a - b = a + negate b
  negate :: a -> a
  negate = (fromInteger 0 -)
  fromInteger :: Integer -> a

class Multiplicative a b c | a b -> c, a c -> b, b c -> a where
  (*) :: a -> b -> c

class ( Multiplicative a b a
      , Multiplicative b a a
      ) => Integral a b where
  quot :: a -> b -> a
  div :: a -> b -> a

class Multiplicative a b c => Fractional a b c where
  (/) :: a -> b -> c

instance Additive Int where
  (+) = (Prelude.+)
  (-) = (Prelude.-)
  negate = Prelude.negate
  fromInteger = Prelude.fromInteger

instance Multiplicative Int Int Int where
  (*) = (Prelude.*)

instance Integral Int Int where
  quot = Prelude.quot
  div = Prelude.div

newtype Var (s :: Region) = Var { unwrapVar :: Int } deriving Eq

instance Hashable (Var s) where
  hashWithSalt salt = hashWithSalt salt . unwrapVar

freshVar :: Monad m => FDT s m (Var s)
freshVar = do
  s@S {..} <- get
  let x = Var varCount
  put s { varCount = varCount + 1
        , vars = HashMap.insert x initVarS vars
        }
  return x

infixl 6 :+, :-
infixl 7 :*, `Quot`, `Div`
data Term s
  = !(Term s) :+ !(Term s)
  | !(Term s) :- !(Term s)
  | {-# UNPACK #-} !Int :* !(Term s)
  | !(Term s) `Quot` {-# UNPACK #-} !Int
  | !(Term s) `Div` {-# UNPACK #-} !Int
  | Int {-# UNPACK #-} !Int
  | Min !(Var s)
  | Max !(Var s)

instance Bounded (Term s) where
  minBound = Int minBound
  maxBound = Int maxBound

instance Additive (Term s) where
  (+) = (:+)
  (-) = (:-)
  negate = ((-1) :*)
  fromInteger = Int . fromInteger

instance Multiplicative Int (Term s) (Term s) where
  (*) = (:*)

instance Multiplicative (Term s) Int (Term s) where
  (*) = flip (:*)

instance Integral (Term s) Int where
  quot = Quot
  div = Div

fromInt :: Int -> Term s
fromInt = Int

min :: Var s -> Term s
min = Min

max :: Var s -> Term s
max = Max

infix 5 :..
data Range s
  = !(Term s) :.. !(Term s)
  | Dom !(Var s)

(#..) :: Term s -> Term s -> Range s
(#..) = (:..)

dom :: Var s -> Range s
dom = Dom

infixr 1 `In`
data Indexical s = Var s `In` Range s

infixr 1 `in'`
in' :: Var s -> Range s -> Indexical s
in' = In

tell :: Monad m => [Indexical s] -> FDT s m ()
tell is = do
  entailed <- newFlag
  forM_ is $ \ (x `In` r) -> do
    (m, a) <- getConditionalRangeVars r
    case (HashSet.null m, HashSet.null a) of
      (True, antimonotone) ->
        readDomain x >>= pruneDom r >>= maybe
        (unless antimonotone $ addPropagator x r m a entailed)
        (\ (dom', pruning) -> do
            when (Dom.null dom') mzero
            addPropagator x r m a entailed
            writeDomain x dom'
            pruned x pruning)
      (False, True) ->
        readDomain x >>= pruneDom r >>=
        flip unlessNothing (addPropagator x r m a entailed)
      (False, False) ->
        addPropagator x r m a entailed

addPropagator :: Monad m =>
                 Var s -> Range s ->
                 MonotoneVars s -> AntimonotoneVars s ->
                 Flag s ->
                 FDT s m ()
addPropagator x r m a entailed = do
  propagator <- newPropagator m a
  forM_ m $ \ x' ->
    whenPruned x' $ \ pruning ->
      when (Pruning.val `affectedBy` pruning) $
        modifyMonotoneVars propagator $ HashSet.delete x'
  forM_ a $ \ x' ->
    whenPruned x' $ \ pruning ->
      when (Pruning.val `affectedBy` pruning) $
        modifyAntimonotoneVars propagator $ HashSet.delete x'
  HashMap.forWithKeyM_ (rangeVars r) $ \ x' dependentPruning ->
    whenPruned x' $ \ pruning ->
      when (dependentPruning `affectedBy` pruning) $
        unlessMarked entailed $ do
          PropagatorS {..} <- readPropagator propagator
          case (HashSet.null monotoneVars, HashSet.null antimonotoneVars) of
            (True, antimonotone) ->
              readDomain x >>= pruneDom r >>= maybe
              (when antimonotone $ mark entailed)
              (\ (dom', pruning') -> do
                  when (Dom.null dom') mzero
                  writeDomain x dom'
                  pruned x pruning')
            (False, True) ->
              readDomain x >>= pruneDom r >>=
              flip whenNothing (mark entailed)
            (False, False) ->
              return ()

label :: Monad m => Var s -> FDT s m Int
label x = do
  dom' <- readDomain x
  case Dom.toList dom' of
    [] -> mzero
    [i] -> return i
    (i:j:is) -> assignTo i `mplus` assignTo j `mplus` msum (map assignTo is)
  where
    assignTo i = do
      writeDomain x $ Dom.singleton i
      pruned x Pruning.val
      return i

type ConditionalVars s = (HashSet (Var s), HashSet (Var s))

getConditionalTermVars :: Monad m => Term s -> FDT s m (ConditionalVars s)
getConditionalTermVars t = case t of
  Int _ ->
    return mempty
  t1 :+ t2 -> do
    (s1, g1) <- getConditionalTermVars t1
    (s2, g2) <- getConditionalTermVars t2
    return (s1 `mappend` s2, g1 `mappend` g2)
  t1 :- t2 -> do
    (s1, g1) <- getConditionalTermVars t1
    (s2, g2) <- getConditionalTermVars t2
    return (s1 `mappend` g2, g1 `mappend` s2)
  x :* t'
    | x >= 0 -> getConditionalTermVars t'
    | otherwise -> liftM swap $ getConditionalTermVars t'
  t' `Quot` x
    | x >= 0 -> getConditionalTermVars t'
    | otherwise -> liftM swap $ getConditionalTermVars t'
  t' `Div` x
    | x >= 0 -> getConditionalTermVars t'
    | otherwise -> liftM swap $ getConditionalTermVars t'
  Min x -> do
    determined <- isDetermined x
    return (if determined then mempty else HashSet.singleton x, mempty)
  Max x -> do
    determined <- isDetermined x
    return (mempty, if determined then mempty else HashSet.singleton x)

getConditionalRangeVars :: Monad m => Range s -> FDT s m (ConditionalVars s)
getConditionalRangeVars r = case r of
  t1 :.. t2 -> do
    (s1, g1) <- getConditionalTermVars t1
    (s2, g2) <- getConditionalTermVars t2
    return (g1 `mappend` s2, s1 `mappend` g2)
  Dom x -> do
    determined <- isDetermined x
    return (mempty, if determined then mempty else HashSet.singleton x)

isDetermined :: Monad m => Var s -> FDT s m Bool
isDetermined = liftM Dom.isVal . readDomain

termVars :: Term s -> HashMap (Var s) Pruning
termVars t = case t of
  Int _ -> HashMap.empty
  t1 :+ t2 -> (HashMap.unionWith (<>) `on` termVars) t1 t2
  t1 :- t2 -> (HashMap.unionWith (<>) `on` termVars) t1 t2
  _ :* t' -> termVars t'
  t' `Quot` _ -> termVars t'
  t' `Div` _ -> termVars t'
  Min x -> HashMap.singleton x Pruning.min
  Max x -> HashMap.singleton x Pruning.max

rangeVars :: Range s -> HashMap (Var s) Pruning
rangeVars r = case r of
  t1 :.. t2 -> (HashMap.unionWith (<>) `on` termVars) t1 t2
  Dom x -> HashMap.singleton x Pruning.dom

pruneDom :: Monad m => Range s -> Dom -> FDT s m (Maybe (Dom, Pruning))
pruneDom (t1 :.. t2) dom' = do
  i1 <- getVal t1
  i2 <- getVal t2
  return $! Dom.retainAll (Dom.fromBounds i1 i2) dom'
pruneDom (Dom x) dom' = do
  dom'' <- readDomain x
  return $! Dom.retainAll dom'' dom'

pruned :: Monad m => Var s -> Pruning -> FDT s m ()
pruned x pruning = readListeners x >>= mapM_ ($ pruning) . toList

getVal :: Monad m => Term s -> FDT s m Int
getVal t = case t of
  Int i -> return i
  t1 :+ t2 -> liftM2 (+!) (getVal t1) (getVal t2)
  t1 :- t2 -> liftM2 (-!) (getVal t1) (getVal t2)
  x :* t' -> liftM (x *!) $ getVal t'
  _ `Quot` 0 -> mzero
  t' `Quot` x -> liftM (`quot` x) $ getVal t'
  _ `Div` 0 -> mzero
  t' `Div` x -> liftM (`div` x) $ getVal t'
  Min x -> liftM Dom.findMin $ readDomain x
  Max x -> liftM Dom.findMax $ readDomain x

data VarS s m =
  VarS { domain :: {-# UNPACK #-} !Dom
       , listeners :: !(Seq (Listener s m))
       }

type Listener s m = Pruning -> FDT s m ()

initVarS :: VarS s m
initVarS = VarS { domain = Dom.full
                , listeners = mempty
                }

readVar :: Monad m => Var s -> FDT s m (VarS s m)
readVar x = liftM (!x) $ gets vars

readDomain :: Monad m => Var s -> FDT s m Dom
readDomain = liftM domain . readVar

modifyVar :: Monad m => Var s -> (VarS s m -> VarS s m) -> FDT s m ()
modifyVar x f = modify $ \ s@S {..} ->
  s { vars = HashMap.adjust f x vars }

writeDomain :: Monad m => Var s -> Dom -> FDT s m ()
writeDomain x d = modifyVar x $ \ s@VarS {..} -> s { domain = d }

readListeners :: Monad m => Var s -> FDT s m (Seq (Listener s m))
readListeners = liftM listeners . readVar

whenPruned :: Monad m => Var s -> (Pruning -> FDT s m ()) -> FDT s m ()
whenPruned x listener = modifyVar x $ \ s@VarS {..} ->
  s { listeners = listeners |> listener }

newtype Propagator (s :: Region) =
  Propagator { unwrapPropagator :: Int
             } deriving Eq

instance Hashable (Propagator s) where
  hashWithSalt salt = hashWithSalt salt . unwrapPropagator

data PropagatorS s =
  PropagatorS { monotoneVars :: !(MonotoneVars s)
              , antimonotoneVars :: !(AntimonotoneVars s)
              }

type MonotoneVars s = HashSet (Var s)
type AntimonotoneVars s = HashSet (Var s)

newPropagator :: Monad m =>
                 MonotoneVars s ->
                 AntimonotoneVars s ->
                 FDT s m (Propagator s)
newPropagator m a = do
  s@S {..} <- get
  let x = Propagator propagatorCount
  put s { propagatorCount = propagatorCount + 1
        , propagators = HashMap.insert x PropagatorS { monotoneVars = m
                                                     , antimonotoneVars = a
                                                     } propagators
        }
  return x

readPropagator :: Monad m => Propagator s -> FDT s m (PropagatorS s)
readPropagator x = liftM (!x) $ gets propagators

modifyMonotoneVars :: Monad m =>
                      Propagator s ->
                      (MonotoneVars s -> MonotoneVars s) ->
                      FDT s m ()
modifyMonotoneVars x f = modifyPropagator x $ \ s@PropagatorS {..} ->
   s { monotoneVars = f monotoneVars }

modifyAntimonotoneVars :: Monad m =>
                          Propagator s ->
                          (AntimonotoneVars s -> AntimonotoneVars s) ->
                          FDT s m ()
modifyAntimonotoneVars x f = modifyPropagator x $ \ s@PropagatorS {..} ->
  s { antimonotoneVars = f antimonotoneVars }

modifyPropagator :: Monad m =>
                    Propagator s ->
                    (PropagatorS s -> PropagatorS s) ->
                    FDT s m ()
modifyPropagator x f = modify $ \ s@S {..} ->
  s { propagators = HashMap.adjust f x propagators }

newtype Flag (s :: Region) = Flag { unwrapFlag :: Int } deriving Eq

instance Hashable (Flag s) where
  hashWithSalt salt = hashWithSalt salt . unwrapFlag

newFlag :: Monad m => FDT s m (Flag s)
newFlag = do
  s@S {..} <- get
  let flag = Flag flagCount
  put s { flagCount = flagCount + 1
        , unmarkedFlags = HashSet.insert flag unmarkedFlags
        }
  return flag

unlessMarked :: Monad m => Flag s -> FDT s m () -> FDT s m ()
unlessMarked flag m = do
  unmarked <- liftM (HashSet.member flag) (gets unmarkedFlags)
  when unmarked m

mark :: Monad m => Flag s -> FDT s m ()
mark flag = modify $ \ s@S {..} ->
  s { unmarkedFlags = HashSet.delete flag unmarkedFlags }

data Region

data S s m =
  S { varCount :: {-# UNPACK #-} !Int
    , vars :: !(HashMap (Var s) (VarS s m))
    , propagatorCount :: {-# UNPACK #-} !Int
    , propagators :: !(HashMap (Propagator s) (PropagatorS s))
    , flagCount :: {-# UNPACK #-} !Int
    , unmarkedFlags :: !(HashSet (Flag s))
    }

initS :: Monad m => S s m
initS =
  S { varCount = 0
    , vars = mempty
    , propagatorCount = 0
    , propagators = mempty
    , flagCount = 0
    , unmarkedFlags = mempty
    }

data PairS s m a = a :+: !(S s m)

fst' :: PairS s m a -> a
fst' (a :+: _) = a

get :: Monad m => FDT s m (S s m)
get = FDT $ \ s -> return $ s :+: s

put :: Monad m => S s m -> FDT s m ()
put s = s `seq` FDT $ \ _ -> return $ () :+: s

modify :: Monad m => (S s m -> S s m) -> FDT s m ()
modify f = FDT $ \ s -> return $! () :+: f s

gets :: Monad m => (S s m -> a) -> FDT s m a
gets f = FDT $ \ s -> return $ f s :+: s

whenNothing :: Monad m => Maybe a -> m () -> m ()
whenNothing p m = maybe m (const $ return ()) p

unlessNothing :: Monad m => Maybe a -> m () -> m ()
unlessNothing p m = maybe (return ()) (const m) p
