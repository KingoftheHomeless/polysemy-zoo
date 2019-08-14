{-# LANGUAGE BangPatterns, TemplateHaskell #-}
module Polysemy.AtomicState where

import Data.Functor.Const
import Polysemy
import Polysemy.State
import GHC.Conc

import Data.IORef

data AtomicState s m a where
  AtomicState :: {-# UNPACK #-} !(s -> (s, a)) -> AtomicState s m a
  AtomicGet   :: AtomicState s m s

makeSem ''AtomicState


data Box a = Box a

atomicState' :: Member (AtomicState s) r
              => (s -> (s, a))
              -> Sem r a
atomicState' f = do
    -- This is to address 'atomicModifyIORef' being stupid!
    -- The provided function (and hence the new state)
    -- is never actually FORCED until the
    -- returned value is!
    -- But we don't WANT to be strict in the returned value,
    -- only the state. Hence, we need a wrapper which can be forced
    -- without the contained value being forced; the box.
    Box a <- atomicState $ \s ->
      case f s of
        (!s', a) -> (s', Box a)
    return a

atomicPut :: Member (AtomicState s) r
          => s
          -> Sem r ()
atomicPut s = do
  !_ <- atomicState $ \_ -> (s, ()) -- strict put with atomicModifyIORef
  return ()

atomicModify :: Member (AtomicState s) r
             => (s -> s)
             -> Sem r ()
atomicModify f = atomicState $ \s -> (f s, ())

atomicModify' :: Member (AtomicState s) r
              => (s -> s)
              -> Sem r ()
atomicModify' f = do
  !_ <- atomicState $ \s -> let !s' = f s in (s', ()) 
  return ()

atomicStateToState :: Member (State s) r
                   => Sem (AtomicState s ': r) a
                   -> Sem r a
atomicStateToState = interpret $ \case
  AtomicState f -> do
    (s', a) <- f <$> get
    put s'
    return a
  AtomicGet -> get

runAtomicStateIORef :: Member (Embed IO) r
                    => IORef s
                    -> Sem (AtomicState s ': r) a
                    -> Sem r a
runAtomicStateIORef ref = interpret $ \case
  AtomicState f -> embed $ atomicModifyIORef ref f
  AtomicGet     -> embed $ readIORef ref

runAtomicStateTVar :: Member (Embed IO) r
                   => TVar s
                   -> Sem (AtomicState s ': r) a
                   -> Sem r a
runAtomicStateTVar tvar = interpret $ \case
  AtomicState f -> embed $ atomically $ do
    (s', a) <- f <$> readTVar tvar
    writeTVar tvar s'
    return a
  AtomicGet -> embed $ readTVarIO tvar

mapAtomicState :: forall s s' a r
                . Member (AtomicState s') r
               => (forall f. Functor f => (s -> f s) -> s' -> f s')
               -> Sem (AtomicState s ': r) a
               -> Sem r a
mapAtomicState lens = interpret $ \case
  AtomicState f -> atomicState $ \s ->
    case lens (\t -> let (t', a) = f t in (a, t')) s of
      (a, s') -> (s', a)
  AtomicGet -> do
    s <- atomicGet
    return (getConst (lens Const s))
