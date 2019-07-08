module Polysemy.Final.MTL
  (
    module Polysemy.Final
  , runErrorFinal
  , runReaderFinal
  , runStateFinal
  , runWriterFinal
  ) where

import Control.Monad.Error.Class hiding (Error)
import Control.Monad.Reader.Class
import Control.Monad.State.Class
import Control.Monad.Writer.Class

import Polysemy
import Polysemy.Final
import Polysemy.Error hiding (throw, catch)
import Polysemy.Reader hiding (ask, local)
import Polysemy.State hiding (get, put)
import Polysemy.Writer hiding (tell, listen, censor)

-----------------------------------------------------------------------------
-- | Run an 'Error' effect through a final 'MonadError'
--
-- /Beware/: Effects that aren't interpreted in terms of the final
-- monad will have local state semantics in regards to 'Error' effects
-- interpreted this way. See 'interpretFinal'.
runErrorFinal :: (Member (Final m) r, MonadError e m)
              => Sem (Error e ': r) a
              -> Sem r a
runErrorFinal = interpretFinal $ \case
  Throw e   -> pure $ throwError e
  Catch m h -> do
    m' <- runS m
    h' <- bindS h
    s <- getInitialStateS
    pure $ m' `catchError` (h' . (<$ s))


-----------------------------------------------------------------------------
-- | Run a 'Reader' effect through a final 'MonadReader'
--
-- /Beware/: Effects that aren't interpreted in terms of the final
-- monad will have local state semantics in regards to 'Reader' effects
-- interpreted this way. See 'interpretFinal'.
runReaderFinal :: (Member (Final m) r, MonadReader i m)
               => Sem (Reader i ': r) a
               -> Sem r a
runReaderFinal = interpretFinal $ \case
  Ask       -> liftS ask
  Local f m -> do
    m' <- runS m
    pure $ local f m'

-----------------------------------------------------------------------------
-- | Run a 'State' effect through a 'MonadState'
--
-- Despite the name, the target monad need not actually be the final
-- monad. The "-Final" suffix reflects that this interpreter
-- has the unusual semantics of interpreters that runs
-- effects by embedding them into another monad.
--
-- /Beware/: Effects that aren't interpreted in terms of the final
-- monad will have local state semantics in regards to 'State' effects
-- interpreted this way. See 'interpretFinal'.
runStateFinal :: (Member (Lift m) r, MonadState s m)
               => Sem (State s ': r) a
               -> Sem r a
runStateFinal = interpret $ \case
  Get   -> sendM get
  Put s -> sendM (put s)

-----------------------------------------------------------------------------
-- | Run a 'Writer' effect through a final 'MonadWriter'
--
-- /Beware/: Effects that aren't interpreted in terms of the final
-- monad will have local state semantics in regards to 'Writer' effects
-- interpreted this way. See 'interpretFinal'.
runWriterFinal :: (Member (Final m) r, MonadWriter o m)
               => Sem (Writer o ': r) a
               -> Sem r a
runWriterFinal = interpretFinal $ \case
  Tell s    -> liftS (tell s)
  Listen m -> do
    m' <- runS m
    pure $
      (\ ~(s, o) -> (,) o <$> s) <$> listen m'
  Censor f m -> do
    m' <- runS m
    pure $ censor f m'
