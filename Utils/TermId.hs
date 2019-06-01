{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Utils.TermId (
  TermId, invalidTmId, isTmIdInvalid, TermTable, SourceRegion(..), initialTermId, HasTermId(..),
  GenTmIdMonad(..), GenTmIdT, GenTab, getNewTermId, getTermTable, runGenTmIdT, runGenTmIdTExt
) where

import Utils.Unique
import Utils.PrettyPrint

import qualified Data.Map as M
import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Control.Applicative
import Text.Megaparsec

import Debug.Trace

-- * Term Identifiers
newtype TermId = TermId Integer
                 deriving (Eq, Ord)

instance Show TermId where
  show tId@(TermId n)
    | isTmIdInvalid tId = "NA"
    | otherwise         = show n

invalidTmId :: TermId
invalidTmId = TermId (-1)

isTmIdInvalid :: TermId -> Bool
isTmIdInvalid (TermId n) = n < 0

initialTermId :: TermId
initialTermId = TermId 0

-- * Term Tables
type TermTable = M.Map TermId

-- * Term Identifier Container Class
class HasTermId a where
  termId :: a -> TermId
  updateTermId :: TermId -> a -> a

-- * Source Region of a Term
data SourceRegion = SrcReg { sourceFile :: String
                           , sourceStartLine :: Int
                           , sourceStartCol :: Int
                           , sourceEndLine :: Int
                           , sourceEndCol :: Int }
                           deriving Show

instance PrettyPrint SourceRegion where
  ppr reg =  text "File:" <+> doubleQuotes (text (sourceFile reg))
         <+> text "; from ( line " <+> int (sourceStartLine reg)
         <+> text ", col " <+> int (sourceStartCol reg)
         <+> text ") to ( line " <+> int (sourceEndLine reg)
         <+> text ", col " <+> int (sourceEndCol reg) <+> text ")"
  needsParens _ = False

-- * Term Identifier Generating Monad
class Monad m => GenTmIdMonad c m where
  genTerm :: c -> m TermId
  updateTermInfo :: (c -> c) -> TermId -> m ()
  getTermInfo :: TermId -> m c

-- * Propagating Term Identifier Generating Monad properties over Other Monad Transformers
instance GenTmIdMonad c m => GenTmIdMonad c (StateT s m) where
  genTerm = lift . genTerm
  updateTermInfo f = lift . updateTermInfo f
  getTermInfo = lift . getTermInfo

instance GenTmIdMonad c m => GenTmIdMonad c (ReaderT r m) where
  genTerm = lift . genTerm
  updateTermInfo f = lift . updateTermInfo f
  getTermInfo = lift . getTermInfo

instance GenTmIdMonad c m => GenTmIdMonad c (ExceptT e m) where
  genTerm = lift . genTerm
  updateTermInfo f = lift . updateTermInfo f
  getTermInfo = lift . getTermInfo

-- * Term Identifier Generating Monad Transformer
newtype GenTmIdT c m a = GenTmIdT {unGenTmIdT :: StateT (GenTab c) m a}
                         deriving (Alternative, MonadPlus)

data GenTab a = GenTab { getNewTermId :: TermId
                       , getTermTable :: TermTable a }

runGenTmIdT :: GenTmIdT c m a -> TermId -> m (a, GenTab c)
runGenTmIdT m tId = runGenTmIdTExt m tId M.empty

runGenTmIdTExt :: GenTmIdT c m a -> TermId -> TermTable c -> m (a, GenTab c)
runGenTmIdTExt (GenTmIdT m) tId initTable = runStateT m (GenTab tId initTable)

instance MonadTrans (GenTmIdT c) where
  lift = GenTmIdT . lift

instance Functor m => Functor (GenTmIdT c m) where
  fmap f = GenTmIdT . fmap f . unGenTmIdT

instance Monad m => Applicative (GenTmIdT c m) where
  pure = return
  GenTmIdT m1 <*> GenTmIdT m2 = GenTmIdT $ m1 <*> m2

instance Monad m => Monad (GenTmIdT c m) where
  return = GenTmIdT . return
  GenTmIdT m >>= f = GenTmIdT $ m >>= unGenTmIdT . f
  fail = lift . fail

instance (Show c,Monad m) => GenTmIdMonad c (GenTmIdT c m) where
  genTerm c = GenTmIdT $ do
    GenTab tId@(TermId n) tab <- get
    put $ GenTab (TermId $ n + 1) (M.insert tId c tab)
    return tId
  updateTermInfo f tId = GenTmIdT $ do
    GenTab tId' tab <- get
    put $ GenTab tId' (M.adjust f tId tab)
  getTermInfo tId = GenTmIdT $ (!!! tId) . getTermTable <$> get

(!!!) :: (Ord k,Show k,Show a) => M.Map k a -> k -> a
(!!!) m k = flip (M.findWithDefault (undefined)) m k

-- * Propagating Monad Properties over Term Identifier Generating Monads
instance MonadState s m => MonadState s (GenTmIdT c m) where
  state = lift . state

instance MonadReader r m => MonadReader r (GenTmIdT c m) where
  ask = lift ask
  local f = GenTmIdT . local f . unGenTmIdT

instance MonadError e m => MonadError e (GenTmIdT c m) where
  throwError = lift . throwError
  catchError m f = GenTmIdT $ catchError (unGenTmIdT m) (unGenTmIdT . f)

instance MonadUnique m => MonadUnique (GenTmIdT c m) where
  getUniqueSupplyM = lift $ getUniqueSupplyM
  getUniqueM       = lift $ getUniqueM
  getUniquesM      = lift $ getUniquesM

instance (MonadPlus m, MonadParsec e s m) => MonadParsec e s (GenTmIdT c m) where
  failure us ps               = lift (failure us ps)
  fancyFailure xs             = lift (fancyFailure xs)
  label n       (GenTmIdT m)  = GenTmIdT $ label n m
  try                         = GenTmIdT . try . unGenTmIdT
  lookAhead     (GenTmIdT m)  = GenTmIdT $ lookAhead m
  notFollowedBy (GenTmIdT m)  = GenTmIdT $ notFollowedBy m
  withRecovery r (GenTmIdT m) = GenTmIdT $ withRecovery (unGenTmIdT . r) m
  observing     (GenTmIdT m)  = GenTmIdT $ observing m
  eof                         = lift eof
  token test mt               = lift (token test mt)
  tokens e ts                 = lift $ tokens e ts
  takeWhileP l f              = lift (takeWhileP l f)
  takeWhile1P l f             = lift (takeWhile1P l f)
  takeP l n                   = lift (takeP l n)
  getParserState              = lift getParserState
  updateParserState f         = lift $ updateParserState f
  