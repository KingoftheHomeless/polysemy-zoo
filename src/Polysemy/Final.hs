{-# LANGUAGE TemplateHaskell #-}
module Polysemy.Final
  (
    -- * Effect
    Final(..)

    -- * Actions
  , withWeaving
  , withStrategic
  , embedFinal

    -- * Combinators for Interpreting to the Final Monad
  , interpretFinal

    -- * Strategy
    -- | Strategy is a domain-specific language very similar to @Tactics@
    -- (see 'Tactical'), and is used to describe how higher-order effects
    -- are threaded down to the final monad.
    --
    -- Much like @Tactics@, computations can be run and threaded
    -- through the use of 'runS' and 'bindS', and first-order constructors
    -- may use 'pureS'. In addition, 'liftS' may be used to
    -- lift actions of the final monad.
    --
    -- Unlike @Tactics@, the final return value within a 'Strategic'
    -- must be a monadic value of the target monad
    -- with the functorial state wrapped inside of it.
  , Strategic
  , WithStrategy
  , pureS
  , liftS
  , runS
  , bindS
  , getInspectorS
  , getInitialStateS

  -- * Interpretations to Final
  , embedToFinal

    -- * Interpretations
  , runFinal
  , finalToFinal
  , runFinalSem
  , lowerFinal
  ) where

import Data.Functor.Compose

import Polysemy
import Polysemy.Final.Internal
import Polysemy.Internal
import Polysemy.Internal.Union
import Control.Monad

-----------------------------------------------------------------------------
-- | 'withWeaving' admits an implementation of 'embed'.
--
-- Just like 'embed', you are discouraged from using this in application code.
embedFinal :: (Member (Final m) r, Functor m) => m a -> Sem r a
embedFinal m = withWeaving $ \s _ _ -> (<$ s) <$> m
{-# INLINE embedFinal #-}

-----------------------------------------------------------------------------
-- | Allows for embedding higher-order actions of the final monad
-- by providing the means of explicitly threading effects through @'Sem' r@
-- to the final monad. This is done through the use of the 'Strategic'
-- environment, which provides 'runSemS' and 'bindSemS'.
--
-- You are discouraged from using 'withStrategic' in application code,
-- as it ties your application code directly to the final monad.
withStrategic :: (Member (Final m) r, Applicative m) => Strategic m (Sem r) a -> Sem r a
withStrategic strat = withWeaving $ \s wv ins ->
  runStrategy
    s
    wv
    ins
    strat
{-# INLINE withStrategic #-}

------------------------------------------------------------------------------
-- | Like 'interpretH', but may be used to
-- interpret higher-order effects in terms of the final monad.
--
-- 'interpretFinal' requires less boilerplate than using 'interpretH'
-- together with 'withStrategic', but is also less powerful.
-- Notably, 'interpretFinal' does not provide any means of
-- executing actions of @'Sem' r@ as you interpret each action.
-- If you need to do so, use 'interpretH' and 'withStrategic' instead.
--
-- /Beware/: Any interpreters built using this (or 'Final' in general)
-- will /not/ respect local/global state semantics based on the order of
-- interpreters run. You should signal interpreters that make use of
-- 'Final' by adding a "-Final" suffix to the names of these.
--
-- State semantics of effects that are /not/
-- interpreted in terms of the final monad will always
-- appear local to effects that are interpreted in terms of the final monad.
--
-- State semantics between effects that are interpreted in terms of the final monad
-- depend on the final monad. E.g. if the final monad is a monad transformer stack,
-- then state semantics will depend on the order monad transformers are stacked.
interpretFinal
    :: forall e m a r
     . (Member (Final m) r, Functor m)
    => (forall x n. e n x -> Strategic m n x)
    -> Sem (e ': r) a
    -> Sem r a
interpretFinal n =
  let
    go :: Sem (e ': r) x -> Sem r x
    go = usingSem $ \u -> case decomp u of
      Right (Weaving e s wv ex ins) ->
        fmap ex $ withWeaving $ \s' wv' ins'
          -> fmap getCompose $
                runStrategy
                  (Compose (s <$ s'))
                  (fmap Compose . wv' . fmap (go . wv) . getCompose)
                  (ins' . getCompose >=> ins)
                  (n e)
      Left g -> liftSem (hoist go g)
    {-# INLINE go #-}
  in
    go
{-# INLINE interpretFinal #-}

------------------------------------------------------------------------------
-- | 'Strategic' is an environment in which you're capable of explicitly
-- threading higher-order effect states to the final monad.
-- This is a variant of @Tactics@ (see 'Tactical'), and usage
-- is extremely similar.
type Strategic m n a = forall f. Functor f => Sem (WithStrategy m f n) (m (f a))

type WithStrategy m f n = '[Strategy m f n]

------------------------------------------------------------------------------
-- | Get a natural transformation capable of potentially inspecting values
-- inside of @f@. Binding the result of 'getInspectorS' produces a function that
-- can sometimes peek inside values returned by 'bindS'.
--
-- This is often useful for running callback functions that are not managed by
-- polysemy code.
--
-- See also 'getInspectorT'
getInspectorS :: Sem (WithStrategy m f n) (Inspector f)
getInspectorS = send GetInspector
{-# INLINE getInspectorS #-}

------------------------------------------------------------------------------
-- | Get the stateful environment of the world at the moment the
-- target monad is to be run.
-- Prefer 'pureS', 'liftS', 'runS', or 'bindS' instead of using this function
-- directly.
getInitialStateS :: Sem (WithStrategy m f n) (f ())
getInitialStateS = send GetInitialState
{-# INLINE getInitialStateS #-}

------------------------------------------------------------------------------
-- | Embed a value into 'Strategic'.
pureS :: Applicative m => a -> Strategic m n a
pureS a = pure . (a <$) <$> getInitialStateS
{-# INLINE pureS #-}

------------------------------------------------------------------------------
-- | Lifts an action of the final monad into 'Strategic'.
--
-- Note: you don't need to use this function if you already have a monadic
-- action with the functorial state woven into it, by the use of
-- 'runS' or 'bindS'.
-- In these cases, you need only use 'pure' to embed the action into the
-- 'Strategic' environment.
liftS :: Functor m => m a -> Strategic m n a
liftS m = do
  s <- getInitialStateS
  pure $ fmap (<$ s) m
{-# INLINE liftS #-}

------------------------------------------------------------------------------
-- | Lifts a monadic action into the stateful environment, in terms
-- of the final monad.
-- The stateful environment will be the same as the one that the target monad
-- is initially run in.
-- Use 'bindS'  if you'd prefer to explicitly manage your stateful environment.
runS :: n a -> Sem (WithStrategy m f n) (m (f a))
runS na = bindS (const na) <*> getInitialStateS
{-# INLINE runS #-}

------------------------------------------------------------------------------
-- | Embed a kleisli action into the stateful environment, in terms of the final
-- monad. You can use 'bindS' to get an effect parameter of the form @a -> n b@
-- into something that can be used after calling 'runS' on an effect parameter
-- @n a@.
bindS :: (a -> n b) -> Sem (WithStrategy m f n) (f a -> m (f b))
bindS = send . HoistInterpretation
{-# INLINE bindS #-}

------------------------------------------------------------------------------
-- | Lower a 'Sem' containing only a single lifted, final 'Monad' into that
-- monad.
runFinal :: Monad m => Sem '[Final m] a -> m a
runFinal = usingSem $ \u -> case extract u of
  Weaving (WithWeaving wav) s wv ex ins ->
    ex <$> wav s (runFinal . wv) ins
{-# INLINE runFinal #-}

------------------------------------------------------------------------------
-- | Transform an @'Embed' m@ effect into a @'Final' m@ effect
embedToFinal :: (Member (Final m) r, Functor m)
             => Sem (Embed m ': r) a
             -> Sem r a
embedToFinal = interpret $ \(Embed m) -> embedFinal m
{-# INLINE embedToFinal #-}

------------------------------------------------------------------------------
-- | Given natural transformations between @m1@ and @m2@, run a @'Final' m1@
-- effect by transforming it into a @'Final' m2@ effect.
finalToFinal :: forall m1 m2 a r
              . (Member (Final m2) r, Functor m2)
             => (forall x. m1 x -> m2 x)
             -> (forall x. m2 x -> m1 x)
             -> Sem (Final m1 ': r) a
             -> Sem r a
finalToFinal to from =
  let
    go :: Sem (Final m1 ': r) x -> Sem r x
    go = usingSem $ \u -> case decomp u of
      Right (Weaving (WithWeaving wav) s wv ex ins) ->
        fmap ex $ withWeaving $ \s' wv' ins'
          -> fmap getCompose $ to $
                wav
                  (Compose (s <$ s'))
                  (from . fmap Compose . wv' . fmap (go . wv) . getCompose)
                  (ins' . getCompose >=> ins)
      Left g -> liftSem (hoist go g)
    {-# INLINE go #-}
  in
    go
{-# INLINE finalToFinal #-}

------------------------------------------------------------------------------
-- | Run a @'Final' ('Sem' r)@ effect if the remaining effect stack is @r@.
--
-- This is sometimes useful for interpreters that make use of
-- 'reinterpret', 'raiseUnder', or any of their friends.
runFinalSem :: Sem (Final (Sem r) ': r) a -> Sem r a
runFinalSem = usingSem $ \u -> case decomp u of
  Right (Weaving (WithWeaving wav) s wv ex ins) ->
    ex <$> wav s (runFinalSem . wv) ins
  Left g -> liftSem (hoist runFinalSem g)
{-# INLINE runFinalSem #-}

------------------------------------------------------------------------------
-- | Run a @'Final' m@ effect by providing an explicit lowering function.
lowerFinal :: Member (Embed m) r
           => (forall x. Sem r x -> m x)
           -> Sem (Final m ': r) a
           -> Sem r a
lowerFinal f = runFinalSem . finalToFinal embed f . raiseUnder
{-# INLINE lowerFinal #-}
