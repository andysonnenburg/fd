{-# LANGUAGE
    DataKinds
  , EmptyDataDecls
  , KindSignatures
  , NamedFieldPuns
  , Rank2Types
  , RecordWildCards #-}
module Control.Monad.FD
       ( FD
       , runFD
       , FDT
       , runFDT
       , Var
       , freshVar
       , Term ((:+), (:-), (:*))
       , int
       , min
       , max
       , Range ((:..))
       , from
       , to
       , dom
       , tell
       , Indexical
       , in'
       , label
       ) where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.Logic (LogicT, observeAllT)
import Control.Monad.State (StateT, evalStateT)
import qualified Control.Monad.State as State
import Control.Monad.Trans.Class (MonadTrans (lift))

import Data.Function (on)
import Data.Functor.Identity
import Data.Hashable
import Data.Monoid
import Data.Tuple (swap)

import Prelude hiding (max, min)

import Control.Monad.FD.DList (DList)
import qualified Control.Monad.FD.DList as DList
import Control.Monad.FD.Dom (Dom)
import qualified Control.Monad.FD.Dom as Dom
import Control.Monad.FD.HashMap.Lazy (HashMap, (!))
import qualified Control.Monad.FD.HashMap.Lazy as HashMap
import Control.Monad.FD.HashSet (HashSet)
import qualified Control.Monad.FD.HashSet as HashSet
import Control.Monad.FD.Pruning (Pruning)
import qualified Control.Monad.FD.Pruning as Pruning

type FD s = FDT s Identity

runFD :: (forall s . FD s a) -> [a]
runFD = runIdentity . runFDT

newtype FDT s m a =
  FDT { unFDT :: StateT (S s m) (LogicT m) a
      }

runFDT :: Monad m => (forall s . FDT s m a) -> m [a]
runFDT m = observeAllT . flip evalStateT initS $ unFDT m

instance Functor m => Functor (FDT s m) where
  fmap f = FDT . fmap f . unFDT

instance Applicative m => Applicative (FDT s m) where
  pure = FDT . pure
  f <*> a = FDT $ unFDT f <*> unFDT a

instance Applicative m => Alternative (FDT s m) where
  empty = FDT empty
  m <|> n = FDT $ unFDT m <|> unFDT n

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

instance MonadIO m => MonadIO (FDT s m) where
  liftIO = lift . liftIO

newtype Var (s :: Region) = Var { unwrapVar :: Integer } deriving Eq

instance Hashable (Var s) where
  hash = hash . unwrapVar
  hashWithSalt salt = hashWithSalt salt . unwrapVar

freshVar :: Monad m => FDT s m (Var s)
freshVar = do
  s@S {..} <- get
  let x = Var varCount
  put s { varCount = varCount + 1
        , varMap = HashMap.insert x initVarS varMap
        }
  return x

infixl 6 :+, :-
infixl 7 :*
data Term s
  = Term s :+ Term s
  | Term s :- Term s
  | Int :* Term s
  | Int Int
  | Min (Var s)
  | Max (Var s)

int :: Int -> Term s
int = Int

min :: Var s -> Term s
min = Min

max :: Var s -> Term s
max = Max

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

tell :: Monad m => [Indexical s] -> FDT s m ()
tell is = do
  entailed <- newFlag
  forM_ is $ \ (x `In` r) -> do
    (m, a) <- getConditionalRangeVars r
    readDomain x >>= pruneDom r >>= \ pruned -> case pruned of
      Just (d, pruning) -> do
        when (HashSet.null m && Dom.null d)
          mzero
        addPropagator x r m a entailed
        when (HashSet.null m) $ do
          writeDomain x d
          firePruning x pruning
      Nothing ->
        unless (HashSet.null a) $
          addPropagator x r m a entailed
  where
    addPropagator x r monotoneVars antimonotoneVars entailed = do
      propagator <- newPropagator x r PropagatorS { monotoneVars, antimonotoneVars }
      HashSet.forM_ monotoneVars $ \ x' ->
        addListener x' $ \ pruning ->
          when (Pruning.member Pruning.val pruning) $
            modifyMonotoneVars propagator $ HashSet.delete x'
      HashSet.forM_ antimonotoneVars $ \ x' ->
        addListener x' $ \ pruning ->
          when (Pruning.member Pruning.val pruning) $
            modifyAntimonotoneVars propagator $ HashSet.delete x'
      HashMap.forWithKeyM_ (rangeVars r) $ \ x' expectedPruning ->
        addListener x' $ \ actualPruning ->
          when (Pruning.member actualPruning expectedPruning) $
            unlessMarked entailed $
              readDomain x >>= pruneDom r >>= \ pruned -> case pruned of
                Just (d, pruning) ->
                  whenMonotone propagator $ do
                    when (Dom.null d)
                      mzero
                    writeDomain x d
                    firePruning x pruning
                Nothing ->
                  whenAntimonotone propagator $
                    mark entailed

data Indexical s = Var s `In` Range s

infixr 1 `in'`
in' :: Var s -> Range s -> Indexical s
in' = In

label :: Monad m => Var s -> FDT s m Int
label x = do
  d <- readDomain x
  msum $ for (Dom.toList d) $ \ i -> do
    writeDomain x $ Dom.singleton i
    firePruning x Pruning.val
    return i

type ConditionalVars s = (HashSet (Var s), HashSet (Var s))

getConditionalTermVars :: Monad m => Term s -> FDT s m (ConditionalVars s)
getConditionalTermVars t = case t of
  Int _ ->
    return mempty
  t1 :+ t2 -> do
    (s1, g1) <- getConditionalTermVars t1
    (s2, g2) <- getConditionalTermVars t2
    return (s1 <> s2, g1 <> g2)
  t1 :- t2 -> do
    (s1, g1) <- getConditionalTermVars t1
    (s2, g2) <- getConditionalTermVars t2
    return (s1 <> g2, g1 <> s2)
  x :* t'
    | x >= 0 -> getConditionalTermVars t'
    | otherwise -> liftM swap $ getConditionalTermVars t'
  Min x ->
    return (HashSet.singleton x, mempty)
  Max x ->
    return (mempty, HashSet.singleton x)

getConditionalRangeVars :: Monad m => Range s -> FDT s m (ConditionalVars s)
getConditionalRangeVars r = case r of
  t1 :.. t2 -> do
    (s1, g1) <- getConditionalTermVars t1
    (s2, g2) <- getConditionalTermVars t2
    return (g1 <> s2, s1 <> g2)
  From t ->
    liftM swap $ getConditionalTermVars t
  To t ->
    getConditionalTermVars t
  Dom x -> do
    determined <- liftM (Dom.sizeLE 1) $ readDomain x
    return (mempty, if determined then mempty else HashSet.singleton x)

termVars :: Term s -> HashMap (Var s) Pruning
termVars t = case t of
  Int _ -> HashMap.empty
  t1 :+ t2 -> (HashMap.unionWith Pruning.join `on` termVars) t1 t2
  t1 :- t2 -> (HashMap.unionWith Pruning.join `on` termVars) t1 t2
  _ :* t' -> termVars t'
  Min x -> HashMap.singleton x Pruning.min
  Max x -> HashMap.singleton x Pruning.max

rangeVars :: Range s -> HashMap (Var s) Pruning
rangeVars r = case r of
  t1 :.. t2 -> (HashMap.unionWith Pruning.join `on` termVars) t1 t2
  From t -> termVars t
  To t -> termVars t
  Dom x -> HashMap.singleton x Pruning.dom

firePruning :: Monad m => Var s -> Pruning -> FDT s m ()
firePruning x pruning = readListeners x >>= mapM_ ($ pruning) . DList.toList

pruneDom :: Monad m => Range s -> Dom -> FDT s m (Maybe (Dom, Pruning))
pruneDom (t1 :.. t2) d = do
  i1 <- getVal t1
  i2 <- getVal t2
  return $ Dom.intersection d (Dom.fromBounds i1 i2)
pruneDom (From t) d = do
   i <- getVal t
   return $ Dom.deleteLT i d
pruneDom (To t) d = do
  i <- getVal t
  return $ Dom.deleteGT i d
pruneDom (Dom x) d =
  liftM (Dom.intersection d) $ readDomain x

getVal :: Monad m => Term s -> FDT s m Int
getVal t = case t of
  Int i -> return i
  t1 :+ t2 -> liftM2 (+) (getVal t1) (getVal t2)
  t1 :- t2 -> liftM2 (-) (getVal t1) (getVal t2)
  x :* t' -> liftM (x *) $ getVal t'
  Min x -> liftM Dom.findMin $ readDomain x
  Max x -> liftM Dom.findMax $ readDomain x

data VarS s m =
  VarS { domain :: Dom
       , listeners :: DList (Listener s m)
       }

readVar :: Monad m => Var s -> FDT s m (VarS s m)
readVar x = liftM (!x) $ gets varMap

readDomain :: Monad m => Var s -> FDT s m Dom
readDomain = liftM domain . readVar

modifyVar :: Monad m => Var s -> (VarS s m -> VarS s m) -> FDT s m ()
modifyVar x f = modify $ \ s@S {..} -> s { varMap = HashMap.adjust f x varMap }

writeDomain :: Monad m => Var s -> Dom -> FDT s m ()
writeDomain x d = modifyVar x $ \ s@VarS {..} -> s { domain = d }

readListeners :: Monad m => Var s -> FDT s m (DList (Listener s m))
readListeners = liftM listeners . readVar

addListener :: Monad m => Var s -> (Pruning -> FDT s m ()) -> FDT s m ()
addListener x listener = modifyVar x $ \ s@VarS {..} ->
  s { listeners = DList.snoc listeners listener }

type Listener s m = Pruning -> FDT s m ()

initVarS :: VarS s m
initVarS = VarS { domain = Dom.full
                , listeners = mempty
                }

data Propagator (s :: Region) =
  Propagator { var :: Var s
             , range :: Range s
             , propagatorS :: Integer
             }

instance Eq (Propagator s) where
  (==) = (==) `on` propagatorS
  (/=) = (/=) `on` propagatorS

instance Hashable (Propagator s) where
  hash = hash . propagatorS
  hashWithSalt salt = hashWithSalt salt . propagatorS

newPropagator :: Monad m => Var s -> Range s -> PropagatorS s -> FDT s m (Propagator s)
newPropagator var range propagatorS = do
  s@S {..} <- get
  let propagator = Propagator { var, range, propagatorS = propagatorCount }
  put s { propagatorCount = propagatorCount + 1
        , propagatorMap = HashMap.insert propagator propagatorS propagatorMap
        }
  return propagator

data PropagatorS s =
  PropagatorS { monotoneVars :: MonotoneVars s
              , antimonotoneVars :: AntimonotoneVars s
              }

type MonotoneVars s = HashSet (Var s)
type AntimonotoneVars s = HashSet (Var s)

readPropagator :: Monad m => Propagator s -> FDT s m (PropagatorS s)
readPropagator x = liftM (!x) $ gets propagatorMap

modifyPropagator :: Monad m => Propagator s -> (PropagatorS s -> PropagatorS s) -> FDT s m ()
modifyPropagator x f = modify $ \ s@S {..} ->
  s { propagatorMap = HashMap.adjust f x propagatorMap }

whenMonotone :: Monad m => Propagator s -> FDT s m () -> FDT s m ()
whenMonotone propagator m = do
  monotone <- liftM HashSet.null $ readMonotoneVars propagator
  when monotone m

readMonotoneVars :: Monad m => Propagator s -> FDT s m (AntimonotoneVars s)
readMonotoneVars = liftM monotoneVars . readPropagator

modifyMonotoneVars :: Monad m =>
                      Propagator s ->
                      (MonotoneVars s -> MonotoneVars s) ->
                      FDT s m ()
modifyMonotoneVars x f = modifyPropagator x $ \ s@PropagatorS {..} ->
  s { monotoneVars = f monotoneVars }

whenAntimonotone :: Monad m => Propagator s -> FDT s m () -> FDT s m ()
whenAntimonotone propagator m = do
  antimonotone <- liftM HashSet.null $ readAntimonotoneVars propagator
  when antimonotone m

readAntimonotoneVars :: Monad m => Propagator s -> FDT s m (AntimonotoneVars s)
readAntimonotoneVars = liftM antimonotoneVars . readPropagator

modifyAntimonotoneVars :: Monad m =>
                          Propagator s ->
                          (AntimonotoneVars s -> AntimonotoneVars s) ->
                          FDT s m ()
modifyAntimonotoneVars x f = modifyPropagator x $ \ s@PropagatorS {..} ->
  s { antimonotoneVars = f antimonotoneVars }

newtype Flag (s :: Region) = Flag { unwrapFlag :: Integer }

newFlag :: Monad m => FDT s m (Flag s)
newFlag = do
  s@S {..} <- get
  put s { flagCount = flagCount + 1
        , flagSet = HashSet.insert flagCount flagSet
        }
  return $ Flag flagCount

unlessMarked :: Monad m => Flag s -> FDT s m () -> FDT s m ()
unlessMarked flag m = do
  S {..} <- get
  when (HashSet.member (unwrapFlag flag) flagSet) m

mark :: Monad m => Flag s -> FDT s m ()
mark flag = modify $ \ s@S {..} ->
  s { flagSet = HashSet.delete (unwrapFlag flag) flagSet }

data Region

data S s m = S { varCount :: Integer
               , varMap :: HashMap (Var s) (VarS s m)
               , propagatorCount :: Integer
               , propagatorMap :: HashMap (Propagator s) (PropagatorS s)
               , flagCount :: Integer
               , flagSet :: HashSet Integer
               }

initS :: Monad m => S s m
initS = S { varCount = toInteger (minBound :: Int)
          , varMap = HashMap.empty
          , propagatorCount = toInteger (minBound :: Int)
          , propagatorMap = HashMap.empty
          , flagCount = toInteger (minBound :: Int)
          , flagSet = mempty
          }

get :: Monad m => FDT s m (S s m)
get = FDT State.get

put :: Monad m => S s m -> FDT s m ()
put = FDT . State.put

modify :: Monad m => (S s m -> S s m) -> FDT s m ()
modify = FDT . State.modify

gets :: Monad m => (S s m -> a) -> FDT s m a
gets = FDT . State.gets

for :: [a] -> (a -> b) -> [b]
for = flip map
