{-# LANGUAGE TemplateHaskell, Trustworthy #-}

module Polysemy.Cont
  (-- * Effect
    Cont(..)

    -- * Actions
  , jump
  , subst
  , callCC

    -- * Interpretations
  , runContPure
  , runContM
  , contToFinal
  , runContViaCapture

    -- * Unsafe Interpretations
  , runContUnsafe

  -- * Prompt types
  , Ref(..)
  , ExitRef(..)
  ) where

import Data.Void

import Control.Monad

import Polysemy
import Polysemy.Final

import Polysemy.Cont.Internal

import Polysemy.Capture
import Polysemy.Error
import Polysemy.UniqueGen

import GHC.Exts (Any)
import Unsafe.Coerce

import Control.Monad.Cont (MonadCont())
import qualified Control.Monad.Cont as C (callCC)

-----------------------------------------------------------------------------
-- | Call with current continuation.
-- Executing the provided continuation will abort execution.
--
-- Using the provided continuation
-- will rollback all effectful state back to the point where 'callCC' was invoked,
-- unless such state is interpreted in terms of the final
-- monad, /or/ the associated interpreter of the effectful state
-- is run after 'runContUnsafe', which may be done if the effect isn't
-- higher-order.
--
-- Higher-order effects do not interact with the continuation in any meaningful
-- way; i.e. 'Polysemy.Reader.local' or 'Polysemy.Writer.censor' does not affect
-- it, and 'Polysemy.Error.catch' will fail to catch any of its exceptions.
-- The only exception to this is if you interpret such effects /and/ 'Cont'
-- in terms of the final monad, and the final monad can perform such interactions
-- in a meaningful manner.
callCC :: forall ref a r
       .  Member (Cont ref) r
       => ((forall b. a -> Sem r b) -> Sem r a)
       -> Sem r a
callCC cc = subst (\ref -> cc (jump ref)) pure
{-# INLINE callCC #-}

-----------------------------------------------------------------------------
-- | Runs a 'Cont' effect by providing 'pure' as the final continuation.
--
-- This is a safe variant of 'runContUnsafe', as this may only be used
-- as the final interpreter before 'run'.
runContPure :: Sem '[Cont (Ref (Sem '[]) a)] a -> Sem '[] a
runContPure = runContUnsafe
{-# INLINE runContPure #-}

-----------------------------------------------------------------------------
-- | Runs a 'Cont' effect by providing 'pure' as the final continuation.
--
-- This is a safe variant of 'runContUnsafe', as this may only be used
-- as the final interpreter before 'runM'.
runContM :: Sem '[Cont (Ref (Sem '[Embed m]) a), Embed m] a -> Sem '[Embed m] a
runContM = runContUnsafe
{-# INLINE runContM #-}

-----------------------------------------------------------------------------
-- | Runs a 'Cont' effect in terms of a final 'MonadCont'
--
-- /Beware/: Effects that aren't interpreted in terms of the final monad
-- will have local state semantics in regards to 'Cont' effects
-- interpreted this way. See 'interpretFinal'.
contToFinal :: (Member (Final m) r, MonadCont m)
            => Sem (Cont (ExitRef m) ': r) a
            -> Sem r a
contToFinal = interpretFinal $ \case
  Jump ref a    -> pure $ enterExit ref a
  Subst main cb -> do
    main' <- bindS main
    cb'   <- bindS cb
    s     <- getInitialStateS
    pure $ C.callCC $ \exit ->
      main' (ExitRef (\a -> cb' (a <$ s) >>= vacuous . exit) <$ s)
{-# INLINE contToFinal #-}

-----------------------------------------------------------------------------
-- | Runs a 'Cont' effect by providing 'pure' as the final continuation.
--
-- __Beware__: This interpreter will invalidate all higher-order effects of any
-- interpreter run after it; i.e. 'Polysemy.Reader.local' and
-- 'Polysemy.Writer.censor' will be no-ops, 'Polysemy.Error.catch' will fail
-- to catch exceptions, and 'Polysemy.Writer.listen' will always return 'mempty'.
--
-- __You should therefore use 'runContUnsafe' /after/ running all__
-- __interpreters for your higher-order effects.__
--
-- Note that 'Final' is a higher-order effect, and thus 'runContUnsafe' can't
-- safely be used together with 'runFinal'.
runContUnsafe :: Sem (Cont (Ref (Sem r) a) ': r) a -> Sem r a
runContUnsafe = runContWithCUnsafe pure
{-# INLINE runContUnsafe #-}

type ContExcRef ref r = ExitRef (
    Sem (Capture (Ref (Sem (Error (ref, Any) ': r))) ': Error (ref, Any) ': r)
    )

-----------------------------------------------------------------------------
-- | A flaky, but functional 'Cont' interpreter that functions through a
-- combination of 'Capture', 'Error', and 'UniqueGen'. This may be used
-- anywhere in the effect stack.
--
-- This interpreter has the caveat that you must not use a higher-order
-- action on any action which /produces/ a reified continuation.
-- For example, you must not do this:
-- @
-- (ref :: Sem r a) <- 'Polysemy.Reader.local' 'id'
--                       $ 'callCC' $ \c -> let b = c b in 'pure' b
-- @
-- Invoking @ref@ after this point will cause the program to fail, which is why
-- the result of 'runContViaCapture' is wrapped in a 'Maybe'.
runContViaCapture :: forall uniq a r
                   . (Member (UniqueGen uniq) r, Eq uniq)
                  => Sem (Cont (ContExcRef uniq r) ': r) a
                  -> Sem r (Maybe a)
runContViaCapture =
  let
    hush :: Either e x -> Maybe x
    hush (Right a) = Just a
    hush _         = Nothing

    go :: Cont (ContExcRef uniq r) m x
       -> Tactical (Cont (ContExcRef uniq r)) m (
             Capture (Ref (Sem (Error (uniq, Any) ': r)))
          ': Error (uniq, Any)
          ': r
         ) x
    go = \case
      (Subst main cn) -> do
        s     <- getInitialStateT
        main' <- (interpretH go .) <$> bindT main
        cn'   <- (interpretH go .) <$> bindT cn
        ref   <- newUnique
        raise $ capture $ \c ->
          let
            loop act =
              (act >>= c) `catch` \ e@(ref', a') -> do
                if ref == ref' then
                  loop (cn' (unsafeCoerce a' <$ s))
                else
                  throw e
          in
            loop $ main' (ExitRef (\a -> throw (ref, unsafeCoerce a)) <$ s)
      (Jump ref a) -> raise (enterExit ref a)
  in
      fmap (join . hush)
    . runError
    . runCapture
    . reinterpret2H go
{-# INLINE runContViaCapture #-}
