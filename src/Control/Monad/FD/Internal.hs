{-# LANGUAGE CPP #-}
#if defined(LANGUAGE_DataKinds) && defined(LANGUAGE_KindSignatures)
{-# LANGUAGE
    DataKinds
  , EmptyDataDecls
  , KindSignatures #-}
#endif
{-# LANGUAGE
    FunctionalDependencies
  , MultiParamTypeClasses
  , NamedFieldPuns
  , Rank2Types
  , RebindableSyntax
  , RecordWildCards #-}
module Control.Monad.FD.Internal
       ( FD
       , runFD
       , FDT
       , runFDT
       , Additive (..)
       , subtract
       , fromIntegral
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
       , complement
       , Indexical
       , in'
       , tell
       , label
       ) where

import Control.Applicative
import Control.Monad (MonadPlus (mplus, mzero),
                      msum,
                      unless,
                      when)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Control.Monad.Logic (LogicT, MonadLogic (msplit), observeAllT)
import Control.Monad.Trans.Class (MonadTrans (lift))

import Data.Foldable (foldMap, forM_, mapM_)
import Data.Function (on)
import Data.Functor.Identity
import Data.Monoid (mempty)
import Data.Semigroup (Option (Option), (<>), getOption)
import Data.Sequence (Seq, (|>))
import Data.Tuple (swap)

import Prelude hiding (Fractional (..),
                       Integral (..),
                       Num (..),
                       fromIntegral,
                       mapM_,
                       max,
                       min,
                       sequence_,
                       subtract)
import qualified Prelude

import Control.Monad.FD.Internal.Int
import Control.Monad.FD.Internal.IntMap.Strict (IntMap, (!))
import qualified Control.Monad.FD.Internal.IntMap.Strict as IntMap
import Control.Monad.FD.Internal.IntSet (IntSet)
import qualified Control.Monad.FD.Internal.IntSet as IntSet
import Control.Monad.FD.Internal.Pruning (Pruning, affectedBy)
import qualified Control.Monad.FD.Internal.Pruning as Pruning
import Control.Monad.FD.Internal.State (StateT, evalStateT)
import qualified Control.Monad.FD.Internal.State as State

import Data.IntSet.Dom (Dom)
import qualified Data.IntSet.Dom as Dom

type FD s = FDT s Identity

runFD :: (forall s . FD s a) -> [a]
runFD = runIdentity . runFDT

newtype FDT s m a =
  FDT { unFDT :: StateT (S s m) (LogicT m) a
      }

runFDT :: Monad m => (forall s . FDT s m a) -> m [a]
runFDT m = observeAllT $ evalStateT (unFDT m) initS

instance Functor (FDT s m) where
  fmap f = FDT . fmap f . unFDT

instance Applicative (FDT s m) where
  pure = FDT . pure
  f <*> a = FDT $ unFDT f <*> unFDT a

instance Alternative (FDT s m) where
  empty = FDT empty
  m <|> n = FDT $ unFDT m <|> unFDT n

instance Monad (FDT s m) where
  return = FDT . return
  m >>= k = FDT $ unFDT m >>= (unFDT . k)
  {-# INLINE (>>=) #-}
  fail = FDT . fail

instance MonadPlus (FDT s m) where
  mzero = FDT mzero
  m `mplus` n = FDT $ unFDT m `mplus` unFDT n

instance MonadTrans (FDT s) where
  lift = FDT . lift . lift

instance MonadIO m => MonadIO (FDT s m) where
  liftIO = FDT . liftIO

instance Monad m => MonadLogic (FDT s m) where
  msplit = FDT . fmap (fmap (fmap FDT)) . msplit . unFDT

infixl 6 +, -
infixl 7 *, `quot`, `div`, /

class Additive a where
  (+) :: a -> a -> a
  (-) :: a -> a -> a
  a - b = a + negate b
  negate :: a -> a
  negate = (0 -)
  fromInteger :: Integer -> a

subtract :: Additive a => a -> a -> a
subtract = flip (-)

fromIntegral :: (Prelude.Integral a, Additive b) => a -> b
fromIntegral = fromInteger . Prelude.toInteger

class Multiplicative a b c | a b -> c, a c -> b, b c -> a where
  (*) :: a -> b -> c

class ( Multiplicative a b a
      , Multiplicative b a a
      ) => Integral a b where
  quot :: a -> b -> a
  div :: a -> b -> a
  div' :: a -> b -> a

class ( Multiplicative a b a
      , Multiplicative b a a
      ) => Fractional a b where
  (/) :: a -> b -> a

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
  n `div'` d = if Prelude.signum r == Prelude.signum d then q + 1 else q
    where
      (q, r) = Prelude.quotRem n d

#if defined(LANGUAGE_DataKinds) && defined(LANGUAGE_KindSignatures)
newtype Var (s :: Region) = Var { unwrapVar :: Int } deriving Eq
#else
newtype Var s = Var { unwrapVar :: Int } deriving Eq
#endif

instance IsInt (Var s) where
  toInt = unwrapVar

freshVar :: FDT s m (Var s)
freshVar = do
  s@S {..} <- get
  let x = Var varCount
  put s { varCount = varCount + 1
        , vars = IntMap.insert x initVarS vars
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
  | !(Term s) `Div'` {-# UNPACK #-} !Int
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
  div' = Div'

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
  | Complement !(Range s)

(#..) :: Term s -> Term s -> Range s
(#..) = (:..)

dom :: Var s -> Range s
dom = Dom

complement :: Range s -> Range s
complement = Complement

infixr 1 `In`
data Indexical s = !(Var s) `In` !(Range s)

infixr 1 `in'`
in' :: Var s -> Range s -> Indexical s
in' = In

tell :: [Indexical s] -> FDT s m ()
tell indexicals = do
  entailed <- newFlag
  forM_ indexicals $ \ (x `In` r) ->
    unlessMarked entailed $ do
      (m, a) <- getMonotonicityRangeVars r
      case (IntSet.null m, IntSet.null a) of
        (True, antimonotone) ->
          readDomain x >>= retainRange r >>= maybe
          (bool (mark entailed) (addPropagator x r m a entailed) antimonotone)
          (\ (dom', pruning) -> do
              when (Dom.null dom') empty
              addPropagator x r m a entailed
              writeDomain x dom'
              pruned x pruning
              propagatePrunings)
        (False, True) ->
          readDomain x >>= retainRange r >>=
          maybe (mark entailed) (const $ addPropagator x r m a entailed)
        (False, False) ->
          addPropagator x r m a entailed

addPropagator :: Var s -> Range s ->
                 MonotoneVars s -> AntimonotoneVars s ->
                 Flag s ->
                 FDT s m ()
addPropagator x r m a entailed = do
  propagator <- newPropagator m a
  forM_ m $ \ x' ->
    whenPruned x' $ \ pruning ->
      when (Pruning.val `affectedBy` pruning) $
        modifyMonotoneVars propagator $ IntSet.delete x'
  forM_ a $ \ x' ->
    whenPruned x' $ \ pruning ->
      when (Pruning.val `affectedBy` pruning) $
        modifyAntimonotoneVars propagator $ IntSet.delete x'
  IntMap.forWithKeyM_ (rangeVars r) $ \ x' dependentPruning ->
    whenPruned x' $ \ pruning ->
      when (dependentPruning `affectedBy` pruning) $
        unlessMarked entailed $ do
          PropagatorS {..} <- readPropagator propagator
          case (IntSet.null monotoneVars, IntSet.null antimonotoneVars) of
            (True, antimonotone) ->
              readDomain x >>= retainRange r >>= maybe
              (when antimonotone $ mark entailed)
              (\ (dom', pruning') -> do
                  when (Dom.null dom') empty
                  writeDomain x dom'
                  pruned x pruning')
            (False, True) ->
              readDomain x >>= retainRange r >>=
              flip whenNothing (mark entailed)
            (False, False) ->
              return ()

label :: Var s -> FDT s m Int
label x = do
  dom' <- readDomain x
  case Dom.toList dom' of
    [] -> empty
    [i] -> return i
    (i:j:is) -> assignTo i <|> assignTo j <|> msum (map assignTo is)
  where
    assignTo i = do
      writeDomain x $ Dom.singleton i
      pruned x Pruning.val
      propagatePrunings
      return i

type MonotonicityVars s = (MonotoneVars s, AntimonotoneVars s)

getMonotonicityTermVars :: Term s -> FDT s m (MonotonicityVars s)
getMonotonicityTermVars t = case t of
  Int _ ->
    return mempty
  t1 :+ t2 -> do
    (s1, g1) <- getMonotonicityTermVars t1
    (s2, g2) <- getMonotonicityTermVars t2
    return (s1 <> s2, g1 <> g2)
  t1 :- t2 -> do
    (s1, g1) <- getMonotonicityTermVars t1
    (s2, g2) <- getMonotonicityTermVars t2
    return (s1 <> g2, g1 <> s2)
  x :* t'
    | x >= 0 -> getMonotonicityTermVars t'
    | otherwise -> swap <$> getMonotonicityTermVars t'
  t' `Quot` x
    | x >= 0 -> getMonotonicityTermVars t'
    | otherwise -> swap <$> getMonotonicityTermVars t'
  t' `Div` x
    | x >= 0 -> getMonotonicityTermVars t'
    | otherwise -> swap <$> getMonotonicityTermVars t'
  t' `Div'` x
    | x >= 0 -> getMonotonicityTermVars t'
    | otherwise -> swap <$> getMonotonicityTermVars t'
  Min x -> do
    assigned <- isAssigned x
    return (if assigned then mempty else IntSet.singleton x, mempty)
  Max x -> do
    assigned <- isAssigned x
    return (mempty, if assigned then mempty else IntSet.singleton x)

getMonotonicityRangeVars :: Range s -> FDT s m (MonotonicityVars s)
getMonotonicityRangeVars r = case r of
  t1 :.. t2 -> do
    (s1, g1) <- getMonotonicityTermVars t1
    (s2, g2) <- getMonotonicityTermVars t2
    return (g1 <> s2, s1 <> g2)
  Dom x -> do
    assigned <- isAssigned x
    return (mempty, if assigned then mempty else IntSet.singleton x)
  Complement r' ->
    swap <$> getMonotonicityRangeVars r'

isAssigned :: Var s -> FDT s m Bool
isAssigned x = do
  dom' <- readDomain x
  return $! case Dom.toList dom' of
    [] -> True
    [_] -> True
    _ -> False

termVars :: Term s -> IntMap (Var s) Pruning
termVars t = case t of
  Int _ -> IntMap.empty
  t1 :+ t2 -> (IntMap.sunion `on` termVars) t1 t2
  t1 :- t2 -> (IntMap.sunion `on` termVars) t1 t2
  _ :* t' -> termVars t'
  t' `Quot` _ -> termVars t'
  t' `Div` _ -> termVars t'
  t' `Div'` _ -> termVars t'
  Min x -> IntMap.singleton x Pruning.min
  Max x -> IntMap.singleton x Pruning.max

rangeVars :: Range s -> IntMap (Var s) Pruning
rangeVars r = case r of
  t1 :.. t2 -> (IntMap.sunion `on` termVars) t1 t2
  Dom x -> IntMap.singleton x Pruning.dom
  Complement r' -> rangeVars r'

retainRange :: Range s -> Dom -> FDT s m (Maybe (Dom, Pruning))
retainRange (t1 :.. t2) dom' = do
  i1 <- getVal t1
  i2 <- getVal t2
  return $! prunedFromTo dom' $ Dom.deleteLT i1 $ Dom.deleteGT i2 dom'
retainRange (Dom x) dom' = do
  dom'' <- readDomain x
  return $! prunedFromTo dom' $ Dom.intersection dom' dom''
retainRange (Complement r) dom' =
  deleteRange r dom'

deleteRange :: Range s -> Dom -> FDT s m (Maybe (Dom, Pruning))
deleteRange (t1 :.. t2) dom' = do
  i1 <- getVal t1
  i2 <- getVal t2
  return $! prunedFromTo dom' $ Dom.deleteBounds i1 i2 dom'
deleteRange (Dom x) dom' = do
  dom'' <- readDomain x
  return $! prunedFromTo dom' $ Dom.difference dom' dom''
deleteRange (Complement r) dom' =
  retainRange r dom'

pruned :: Var s -> Pruning -> FDT s m ()
pruned x pruning = modify $ \ s@S {..} ->
  s { prunings = IntMap.alter f x prunings }
  where
    f Nothing = Just pruning
    f (Just pruning') = Just $ pruning <> pruning'

propagatePrunings :: FDT s m ()
propagatePrunings = do
  s <- get
  put s { prunings = mempty }
  IntMap.forWithKeyM_ (prunings s) $ \ x pruning ->
    readPruningListeners x >>= mapM_ ($ pruning)
  IntMap.null <$> gets prunings >>= flip unless propagatePrunings

getVal :: Term s -> FDT s m Int
getVal t = case t of
  Int i -> return i
  t1 :+ t2 -> (+!) <$> getVal t1 <*> getVal t2
  t1 :- t2 -> (-!) <$> getVal t1 <*> getVal t2
  x :* t' -> (x *!) <$> getVal t'
  _ `Quot` 0 -> empty
  t' `Quot` x -> (`quot` x) <$> getVal t'
  _ `Div` 0 -> empty
  t' `Div` x -> (`div` x) <$> getVal t'
  _ `Div'` 0 -> empty
  t' `Div'` x -> (`div'` x) <$> getVal t'
  Min x -> Dom.findMin <$> readDomain x
  Max x -> Dom.findMax <$> readDomain x

data VarS s m =
  VarS { domain :: !Dom
       , pruningListeners :: !(Seq (PruningListener s m))
       }

type PruningListener s m = Pruning -> FDT s m ()

initVarS :: VarS s m
initVarS = VarS { domain = Dom.full
                , pruningListeners = mempty
                }

readVar :: Var s -> FDT s m (VarS s m)
readVar x = (!x) <$> gets vars

readDomain :: Var s -> FDT s m Dom
readDomain = fmap domain . readVar

modifyVar :: Var s -> (VarS s m -> VarS s m) -> FDT s m ()
modifyVar x f = modify $ \ s@S {..} ->
  s { vars = IntMap.adjust f x vars }

writeDomain :: Var s -> Dom -> FDT s m ()
writeDomain x domain = modifyVar x $ \ s -> s { domain }

readPruningListeners :: Var s -> FDT s m (Seq (PruningListener s m))
readPruningListeners = fmap pruningListeners . readVar

whenPruned :: Var s -> PruningListener s m -> FDT s m ()
whenPruned x pruningListener = modifyVar x $ \ s@VarS {..} ->
  s { pruningListeners = pruningListeners |> pruningListener }

#if defined(LANGUAGE_DataKinds) && defined(LANGUAGE_KindSignatures)
newtype Propagator (s :: Region) =
  Propagator { unwrapPropagator :: Int
             } deriving Eq
#else
newtype Propagator s =
  Propagator { unwrapPropagator :: Int
             } deriving Eq
#endif

instance IsInt (Propagator s) where
  toInt = unwrapPropagator

data PropagatorS s =
  PropagatorS { monotoneVars :: !(MonotoneVars s)
              , antimonotoneVars :: !(AntimonotoneVars s)
              }

type MonotoneVars s = IntSet (Var s)
type AntimonotoneVars s = IntSet (Var s)

newPropagator :: MonotoneVars s ->
                 AntimonotoneVars s ->
                 FDT s m (Propagator s)
newPropagator m a = do
  s@S {..} <- get
  let x = Propagator propagatorCount
  put s { propagatorCount = propagatorCount + 1
        , propagators = IntMap.insert x PropagatorS { monotoneVars = m
                                                    , antimonotoneVars = a
                                                    } propagators
        }
  return x

readPropagator :: Propagator s -> FDT s m (PropagatorS s)
readPropagator x = (!x) <$> gets propagators

modifyMonotoneVars :: Propagator s ->
                      (MonotoneVars s -> MonotoneVars s) ->
                      FDT s m ()
modifyMonotoneVars x f = modifyPropagator x $ \ s@PropagatorS {..} ->
  s { monotoneVars = f monotoneVars }

modifyAntimonotoneVars :: Propagator s ->
                          (AntimonotoneVars s -> AntimonotoneVars s) ->
                          FDT s m ()
modifyAntimonotoneVars x f = modifyPropagator x $ \ s@PropagatorS {..} ->
  s { antimonotoneVars = f antimonotoneVars }

modifyPropagator :: Propagator s ->
                    (PropagatorS s -> PropagatorS s) ->
                    FDT s m ()
modifyPropagator x f = modify $ \ s@S {..} ->
  s { propagators = IntMap.adjust f x propagators }

#if defined(LANGUAGE_DataKinds) && defined(LANGUAGE_KindSignatures)
newtype Flag (s :: Region) = Flag { unwrapFlag :: Int } deriving Eq
#else
newtype Flag s = Flag { unwrapFlag :: Int } deriving Eq
#endif

instance IsInt (Flag s) where
  toInt = unwrapFlag

newFlag :: FDT s m (Flag s)
newFlag = do
  s@S {..} <- get
  let flag = Flag flagCount
  put s { flagCount = flagCount + 1
        , unmarkedFlags = IntSet.insert flag unmarkedFlags
        }
  return flag

unlessMarked :: Flag s -> FDT s m () -> FDT s m ()
unlessMarked flag m = do
  unmarked <- IntSet.member flag <$> gets unmarkedFlags
  when unmarked m

mark :: Flag s -> FDT s m ()
mark flag = modify $ \ s@S {..} ->
  s { unmarkedFlags = IntSet.delete flag unmarkedFlags }

#if defined(LANGUAGE_DataKinds) && defined(LANGUAGE_KindSignatures)
data Region
#endif

data S s m =
  S { varCount :: {-# UNPACK #-} !Int
    , vars :: !(IntMap (Var s) (VarS s m))
    , propagatorCount :: {-# UNPACK #-} !Int
    , propagators :: !(IntMap (Propagator s) (PropagatorS s))
    , flagCount :: {-# UNPACK #-} !Int
    , unmarkedFlags :: !(IntSet (Flag s))
    , prunings :: !(IntMap (Var s) Pruning)
    }

initS :: S s m
initS =
  S { varCount = 0
    , vars = mempty
    , propagatorCount = 0
    , propagators = mempty
    , flagCount = 0
    , unmarkedFlags = mempty
    , prunings = mempty
    }

whenNothing :: Monad m => Maybe a -> m () -> m ()
whenNothing p m = maybe m (const $ return ()) p

get :: FDT s m (S s m)
get = FDT State.get

put :: S s m -> FDT s m ()
put = FDT . State.put

modify :: (S s m -> S s m) -> FDT s m ()
modify = FDT . State.modify

gets :: (S s m -> a) -> FDT s m a
gets = FDT . State.gets

bool :: a -> a -> Bool -> a
bool t _ True = t
bool _ e False = e

ifThenElse :: Bool -> a -> a -> a
ifThenElse True t _ = t
ifThenElse False _ e = e

prunedFromTo :: Dom -> Dom -> Maybe (Dom, Pruning)
prunedFromTo dom1 dom2 =
  fmap ((,) dom2) . getOption . foldMap (Option . Just . snd) $ filter fst
  [ prunedToVal dom1 dom2 --> Pruning.val
  , min1 < min2 --> Pruning.min
  , max1 > max2 --> Pruning.max
  , Dom.size dom1 > Dom.size dom2 --> Pruning.dom
  ]
  where
    (min1, max1) = bounds dom1
    (min2, max2) = bounds dom2

bounds :: Dom -> (Maybe Int, Maybe Int)
bounds dom' = (Dom.minView dom', Dom.maxView dom')

infixr 0 -->
(-->) :: a -> b -> (a, b)
(-->) = (,)

prunedToVal :: Dom -> Dom -> Bool
prunedToVal dom1 dom2 = case (Dom.toList dom1, Dom.toList dom2) of
  ([], []) -> False
  (_, []) -> True
  ([_], [_]) -> False
  (_, [_]) -> True
  _ -> False
