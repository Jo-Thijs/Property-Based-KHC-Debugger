{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Backend.FcEvaluator where

import Backend.FcTypes
import Backend.Debugger

import Frontend.HsTypes

import Utils.Kind
import Utils.SnocList
import Utils.Substitution
import Utils.Unique
import Utils.Var
import Utils.PrettyPrint
import Utils.TermId
import Utils.FreeVars

import Data.Maybe
import qualified Data.Map as M

import Control.Monad
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Trans

import Debug.Trace

-- * Tracks
-- ----------------------------------------------------------------------------

data Track a = Track [a] a [a] deriving Show

initialTrack :: Monoid a => Track a
initialTrack = Track [] mempty []

trackGet :: Track a -> a
trackGet (Track _ result _ ) = result

trackBack :: Track a -> Track a
trackBack (Track (b:befs) c afts) = Track befs b (c:afts)

trackNext :: Track a -> Track a
trackNext (Track befs c (a:afts)) = Track (c:befs) a afts
trackNext (Track befs c []      ) = Track (c:befs) c []

trackUpdate :: (a -> a) -> Track a -> Track a
trackUpdate f (Track befs c afts) = Track befs (f c) afts

trackReset :: [a] -> Track a -> Track a
trackReset xs (Track befs c _) = Track befs c xs

trackBranch :: Track a -> Track a
trackBranch (Track befs c _) = Track befs c []

trackPropagate :: Track a -> Track a
trackPropagate (Track (_:befs) c afts) = Track befs c afts

trackFresh :: Track a -> Track a
trackFresh (Track _ c afts) = Track [] c afts

trackMerge :: Show a => Track a -> Track a -> Track a
trackMerge (Track befs _ []) (Track [] c afts) = Track befs c afts

-- * Evaluation Monad
-- ----------------------------------------------------------------------------

newtype FcET m a = FcET { unFcET :: ( ReaderT (EvalHook m , SrcCtx , TyCtx)
                                    ( GenTmIdT RnTerm
                                    ( StateT Store
                                    ( UniqueSupplyT m) ) ) a )
                        } deriving ( Functor, Applicative, Monad,
                                     MonadReader (EvalHook m , SrcCtx , TyCtx),
                                     GenTmIdMonad RnTerm,
                                     MonadState Store,
                                     MonadUnique )

instance MonadTrans FcET where
  lift = FcET . lift . lift . lift . lift

type EvalHook m = FcTermInterp -> FcET m FcTermInterp -> FcET m FcTermInterp

type SrcCtx = Track [(RnTmVar,ChunkId)]

type TyCtx = Track [(RnTyVar,RnMonoTy)]

hook :: Monad m => FcTermInterp -> FcET m FcTermInterp -> FcET m FcTermInterp
hook tm evaluation = do
  (myHook,_,_) <- ask
  myHook tm evaluation

withExtendedCtxs :: Monad m => FcTmVar -> FcTermInterp -> ChunkId -> FcET m a -> FcET m a
withExtendedCtxs x fcTm cId m = do
  let tId = termId fcTm
  let f = if isTmIdInvalid tId
          then id
          else ((fcTmVarToRnTmVar x , cId):)
  local (\(hook,srcctx,tyctx) -> ( hook
                                 , trackUpdate f srcctx
                                 , tyctx))
        m

withExtendedTyCtx :: Monad m => FcTyVar -> FcType -> FcET m a -> FcET m a
withExtendedTyCtx a ty =
  local (\(hook,srcctx,tyctx) ->
          (hook, srcctx, trackUpdate ((fcTyVarToRnTyVar a,fcTypeToRnType ty):) tyctx))

fcTypeToRnType :: FcType -> RnMonoTy
fcTypeToRnType (FcTyVar a)       = TyVar (fcTyVarToRnTyVar a)
fcTypeToRnType (FcTyAbs a ty)    = fcTypeToRnType $ substVar a (FcTyCon fcTestResultTyCon) ty
fcTypeToRnType (FcTyApp ty1 ty2) = TyApp (fcTypeToRnType ty1) (fcTypeToRnType ty2)
fcTypeToRnType (FcTyCon tc)      = TyCon (HsTC $ unFcTC tc)

withCtxs :: Monad m => SrcCtx -> TyCtx -> FcET m a -> FcET m a
withCtxs srcctx tyctx = local (\(hook,_,_) -> (hook,srcctx,tyctx))

withInnerCtxs :: Monad m => FcET m a -> FcET m a
withInnerCtxs = local (\(hook,srcctx,tyctx) -> (hook, trackNext srcctx, trackNext tyctx))

withOuterCtxs :: Monad m => FcET m a -> FcET m a
withOuterCtxs = local (\(hook,srcctx,tyctx) -> (hook, trackBack srcctx, trackBack tyctx))

withPropCtxs :: Monad m => FcET m a -> FcET m a
withPropCtxs = local (\(hook,srcctx,tyctx) -> (hook, trackPropagate srcctx, trackPropagate tyctx))

withBranchCtxs :: Monad m => FcET m a -> FcET m a
withBranchCtxs = local (\(hook,srcctx,tyctx) -> (hook, trackBranch srcctx, trackBranch tyctx))

askBranch :: Monad m => FcET m (SrcCtx , TyCtx)
askBranch = (\(_,srcctx,tyctx) -> (trackBranch srcctx , trackBranch tyctx)) <$> ask

-- * Storage
-- ----------------------------------------------------------------------------

type ChunkStorage a = M.Map ChunkId a

csAt :: ChunkStorage a -> ChunkId -> a
csAt = (M.!)

csAppend :: ChunkId -> a -> ChunkStorage a -> ChunkStorage a
csAppend = M.insert

csAdjust :: (a -> a) -> ChunkId -> ChunkStorage a -> ChunkStorage a
csAdjust = M.adjust

data Store = Store { getNewChunkId  :: ChunkId
                   , getChunkTable  :: ChunkStorage (FcTermInterp, Bool)
                   , getSrcCtxTable :: ChunkStorage SrcCtx
                   , getTyCtxTable  :: ChunkStorage TyCtx }

storeLookup :: Store -> ChunkId -> ((FcTermInterp , Bool) , SrcCtx , TyCtx )
storeLookup store cId = ( csAt (getChunkTable store) cId
                        , csAt (getSrcCtxTable store) cId
                        , csAt (getTyCtxTable store) cId )

storeNew :: Maybe FcTmVar -> SrcCtx -> TyCtx -> FcTermInterp -> Store -> Store
storeNew recur srcctx tyctx tm store@(Store new@(ChunkId k) chunkTab srcctxTab tyctxTab) =
  store { getNewChunkId  = ChunkId $ k + 1
        , getChunkTable  = csAppend new (tm,False) chunkTab
        , getSrcCtxTable = csAppend new (trackFresh srcctx) srcctxTab
        , getTyCtxTable  = csAppend new (trackFresh tyctx) tyctxTab }

storeUpdate :: ChunkId -> FcTermInterp -> Bool -> SrcCtx -> TyCtx -> Store -> Store
storeUpdate cId tm final srcctx tyctx store =
  store { getChunkTable  = csAdjust (const (tm,final)) cId (getChunkTable store)
        , getSrcCtxTable = csAdjust (const srcctx) cId (getSrcCtxTable store)
        , getTyCtxTable  = csAdjust (const tyctx) cId (getTyCtxTable store) }

initialStore :: Store
initialStore = Store (ChunkId 0) mempty mempty mempty

instance PrettyPrint Store where
  ppr (Store cId table _ _) = ppr (cId, table)
  needsParens _ = True

instance PrettyPrint ChunkId where
  ppr (ChunkId n) = text "Chunk_" <> ppr n
  needsParens _ = False

newChunk :: Monad m => SrcCtx -> TyCtx -> Maybe FcTmVar -> FcTermInterp -> FcET m ChunkId
newChunk srcctx tyctx recur tm = do
  store <- get
  let cId = getNewChunkId store
  modify $ storeNew recur srcctx tyctx tm
  return cId

-- * Term Evaluation
-- ----------------------------------------------------------------------------

type Cont m = FcTermInterp -> FcET m FcTermInterp

fcEvalTm :: Monad m => Cont m -> FcTermInterp -> FcET m FcTermInterp
fcEvalTm cont (FcTmApp tId tm1 tm2) = hook (FcTmApp tId tm1 tm2) $ do
  (srcctx,tyctx) <- askBranch
  withInnerCtxs $ flip fcEvalTm tm1 $ \tm1' -> do
    let me = FcTmApp tId tm1' tm2
    case tm1' of
      FcTmAbs _ x ty tm3 ->
        withPropCtxs $ substituteChunked srcctx tyctx x ty tm2 tm3 $ fcEvalTm cont
      _                  -> do
        cId <- newChunk srcctx tyctx Nothing tm2
        withOuterCtxs $ cont $ FcTmApp tId tm1' $ FcTmChunk (termId tm2) cId
fcEvalTm cont (FcTmTyApp tId tm1 ty) = do
  withInnerCtxs $ flip fcEvalTm tm1 $ \tm1' -> do
    let me = FcTmTyApp tId tm1' ty
    case tm1' of
      FcTmTyAbs _ a tm2 -> withPropCtxs $ withExtendedTyCtx a ty $
        fcEvalTm cont (substFcTyInTm (a |-> ty) tm2)
      _                 -> withOuterCtxs $ cont me
fcEvalTm cont (FcTmLet tId x ty tm1 tm2) = do
  (_,srcctx,tyctx) <- ask
  substituteChunkedRec (isTmIdInvalid tId) srcctx tyctx x ty tm1 tm2 $ fcEvalTm cont
fcEvalTm cont (FcTmCase tId tm1 alts) = hook (FcTmCase tId tm1 alts) $ do
  (_,srcctx,tyctx) <- ask
  withInnerCtxs $ flip fcEvalTm tm1 $ \tm1' -> do
    (_,srcctx',tyctx') <- ask
    let me = FcTmCase tId tm1' alts
    case getFcTmConAndArgs tm1' of
      Just (con, args) -> case getMatchingAlt con alts of
        Just alt -> withCtxs srcctx tyctx
                  $ fcEvalAltStep (foldr (const trackNext) (trackBack srcctx') args)
                                  (foldr (const trackNext) (trackBack  tyctx') args)
                                  cont alt args
        Nothing  -> withOuterCtxs $ cont me
      Nothing          -> withOuterCtxs $ cont me
fcEvalTm cont (FcTmChunk _ chunk) = do
  (_,srcctx,tyctx) <- ask
  ((tm,final),srcctx',tyctx') <- flip storeLookup chunk <$> get
  if final
  then withCtxs (trackMerge srcctx srcctx') (trackMerge tyctx tyctx') $ cont tm
  else withCtxs srcctx' tyctx' $
         flip fcEvalTm tm $ \tm' -> do
           (_,srcctx'',tyctx'') <- ask
           modify (storeUpdate chunk tm' True srcctx'' tyctx'')
           withCtxs (trackMerge srcctx srcctx'') (trackMerge tyctx tyctx'') $ cont tm'
fcEvalTm cont tm = cont tm

getFcTmConAndArgs :: FcTermInterp -> Maybe (FcDataCon, [FcTermInterp])
getFcTmConAndArgs = acc []
  where
    acc args (FcTmTyApp _ tm _ ) = acc args tm
    acc args (FcTmDataCon _ con) = Just (con, args)
    acc args (FcTmApp _ tm1 tm2) = acc (tm2 : args) tm1
    acc _     _                  = Nothing

getMatchingAlt :: FcDataCon -> [FcAlt a] -> Maybe (FcAlt a)
getMatchingAlt con alts =
  listToMaybe [alt | alt@(FcAlt (FcConPat altCon _) _) <- alts, con == altCon]

fcEvalAltStep :: Monad m => SrcCtx -> TyCtx -> Cont m
              -> FcAlt FcTermInterpreter -> [FcTermInterp] -> FcET m FcTermInterp
fcEvalAltStep srcctx tyctx cont (FcAlt (FcConPat con (var:vars)) tm) (arg:args) = do
    substituteChunked (trackBranch srcctx) (trackBranch tyctx) var undefined arg tm $ \tm' ->
      fcEvalAltStep (trackBack srcctx) (trackBack tyctx) cont (FcAlt (FcConPat con vars) tm') args
fcEvalAltStep srcctx tyctx cont (FcAlt (FcConPat con []        ) tm) []         =
  fcEvalTm cont tm

substituteChunked :: Monad m
                  => SrcCtx -> TyCtx -> FcTmVar -> FcType -> FcTermInterp -> FcTermInterp
                  -> (FcTermInterp -> FcET m FcTermInterp) -> FcET m FcTermInterp
substituteChunked srcctx tyctx var ty newSubTm oldTm m = do
  cId <- newChunk srcctx tyctx Nothing newSubTm
  withExtendedCtxs var newSubTm cId $ m $ substVar var (FcTmChunk (termId newSubTm) cId) oldTm

substituteChunkedRec :: Monad m
                  => Bool -> SrcCtx -> TyCtx -> FcTmVar -> FcType -> FcTermInterp -> FcTermInterp
                  -> (FcTermInterp -> FcET m FcTermInterp) -> FcET m FcTermInterp
substituteChunkedRec invalid srcctx tyctx var ty newSubTm oldTm m = do
  cId <- newChunk srcctx tyctx (Just var) newSubTm
  let (f,g) = if invalid
              then (id,id)
              else ( trackUpdate ((fcTmVarToRnTmVar var , cId):)
                   , withExtendedCtxs var newSubTm cId )
  let srcctx' = f $ trackFresh srcctx
  let tyctx'  =     trackFresh  tyctx
  modify (storeUpdate cId (substVar var (FcTmChunk (termId newSubTm) cId) newSubTm) False srcctx' tyctx')
  g $ m $ substVar var (FcTmChunk (termId newSubTm) cId) oldTm

fcEvalTmEntirely :: Monad m => FcTermInterp -> FcET m FcTermInterp
fcEvalTmEntirely tm = flip fcEvalTm tm $ \tm' -> case tm' of
  FcTmAbs tId x ty tm''  -> FcTmAbs tId x ty <$> fillChunksIn tm''
  FcTmApp tId tm1 tm2    -> FcTmApp tId <$> withInnerCtxs (fcEvalTmEntirely tm1) <*> withBranchCtxs (fcEvalTmEntirely tm2)
  FcTmTyAbs tId a tm''   -> FcTmTyAbs tId a <$> fillChunksIn tm''
  FcTmTyApp tId tm'' ty  -> FcTmTyApp tId <$> withInnerCtxs (fcEvalTmEntirely tm'') <*> return ty
  FcTmCase tId tm'' alts -> FcTmCase tId <$> withInnerCtxs (fcEvalTmEntirely tm'') <*> withBranchCtxs (mapM fillChunksInAlt alts)
  tm''                   -> return tm''

fillChunksIn :: Monad m => FcTermInterp -> FcET m FcTermInterp
fillChunksIn (FcTmVar tId x)            = return $ FcTmVar tId x
fillChunksIn (FcTmDataCon tId dc)       = return $ FcTmDataCon tId dc
fillChunksIn (FcTmAbs tId x ty tm)      = FcTmAbs tId x ty <$> fillChunksIn tm
fillChunksIn (FcTmApp tId tm1 tm2)      = FcTmApp tId <$> fillChunksIn tm1 <*> fillChunksIn tm2
fillChunksIn (FcTmTyAbs tId a tm)       = FcTmTyAbs tId a <$> fillChunksIn tm
fillChunksIn (FcTmTyApp tId tm ty)      = FcTmTyApp tId <$> fillChunksIn tm <*> return ty
fillChunksIn (FcTmLet tId x ty tm1 tm2) = FcTmLet tId x ty <$> fillChunksIn tm1 <*> fillChunksIn tm2
fillChunksIn (FcTmCase tId tm alts)     = FcTmCase tId <$> fillChunksIn tm <*> mapM fillChunksInAlt alts
fillChunksIn (FcTmChunk tId cId)        = do
  store <- get
  let ((tm,_),_,_) = storeLookup store cId
  fillChunksIn tm

fillChunksInAlt :: Monad m => FcAltInterp -> FcET m FcAltInterp
fillChunksInAlt (FcAlt pat tm) = FcAlt pat <$> fillChunksIn tm

-- * Program Evaluation
-- ----------------------------------------------------------------------------

fcValBindToTm :: Monad m => FcValBnd a -> FcTm a -> FcET m (FcTm a)
fcValBindToTm (FcValBind var ty tm) body =
  return $ FcTmLet invalidTmId var ty tm body

fcPgmToFcTm :: Monad m => FcPgm a -> FcET m (FcTm a)
fcPgmToFcTm (FcPgmDataDecl _    p) = fcPgmToFcTm p
fcPgmToFcTm (FcPgmValDecl  decl p) = fcPgmToFcTm p >>= fcValBindToTm decl
fcPgmToFcTm (FcPgmTerm tm)         = return tm

fcEvalPgm :: Monad m => FcPgm a -> FcET m FcTermInterp
fcEvalPgm = (>>= fcEvalTmEntirely) . fcPgmToFcTm . fcPgmToInterp

-- * Invoke the complete System F evaluator
-- ----------------------------------------------------------------------------

type Unwrapped a = (((a, GenTab RnTerm), Store), UniqueSupply)

fcEvaluate :: TermId -> UniqueSupply -> FcPgm a -> Unwrapped FcTermInterp
fcEvaluate tId us = runIdentity . unpackEvaluation (const id) tId mempty us . fcEvalPgm

fcEvaluateDebug :: Monad m
                => TermMetaTable -> TermTable RnTerm -> Tests
                -> TermId -> UniqueSupply -> FcPgm a
                -> (ShrinkTrace -> FcET m FcTermInterp -> FcET m FcTermInterp)
                -> m (Unwrapped FcTermInterp)
fcEvaluateDebug metaTab fcTable tests tId us pgm handler = unpackEvaluation myHook
                                                                            tId
                                                                            fcTable
                                                                            us
                                                         $ fcEvalPgm pgm
  where myHook = debugHook handler
                           evalDec
                           (skipTab M.!)
                           tests
                           (constructRepr Nothing [] ((\(_,r,_) -> r) <$> ask))
                           constructTy
        
        evalDec False = evalTest tId us pgm
        evalDec True  = evalTest' pgm
        
        constructRepr :: Monad m => Maybe ChunkId -> [ChunkId]
                      -> FcET m SrcCtx -> FcTermInterp -> FcET m SrcRepr
        constructRepr ccid cids srcctx tm = do
          let tId = termId tm
          store <- get
          core <- getTermInfo tId
          let f cId ((tm',_),r,_) = constructRepr (Just cId)
                                                  (maybe id (:) ccid cids)
                                                  (return r)
                                                  tm'
          case tm of
            FcTmChunk _ cId -> f cId (storeLookup store cId)
            _               -> do
              let fvs = ftmvsOf core
              assocs <- filter (flip elem fvs . fst) . trackGet <$> srcctx
              Rep core <$> mapM (\(x,cId) -> (,) x <$> f cId (storeLookup store cId))
                                (filter (not . flip elem cids . snd) assocs)
        
        constructTy :: Monad m => TermId -> FcET m RnMonoTy
        constructTy tId = do
          let rnTm = fcTable M.! tId
          let baseTy = getRnType $ metaTab M.! termId rnTm
          (_,srcctx,tyctx) <- ask
          return $ foldl (flip $ uncurry substVar) baseTy (trackGet tyctx)
        
        skipTab :: TermTable Bool
        skipTab = flip fmap fcTable $ \rnTm ->
                    let prelim = map isJust
                               $ tests $ Left (getRnType $ metaTab M.! termId rnTm, undefined)
                    in  all not prelim

unpackEvaluation :: Monad m
                 => EvalHook m -> TermId -> TermTable RnTerm -> UniqueSupply -> FcET m a
                 -> m (Unwrapped a)
unpackEvaluation hook tId initTable us = flip runUniqueSupplyT us
                                       . flip runStateT initialStore
                                       . flip (flip runGenTmIdTExt tId) initTable
                                       . flip runReaderT (hook , initialTrack , initialTrack)
                                       . unFcET

evalTest :: Monad m => TermId -> UniqueSupply -> FcPgm a -> FcTermInterp -> FcET m FcTermInterp
evalTest tId us pgm tm = return
                       $ flip evalState 10000
                       $ fmap (\(((r,_),_),_) -> r)
                       $ unpackEvaluation myHook tId undefined us
                       $ fcEvalPgm $ coveredBy pgm tm
  where myHook :: EvalHook (State Integer)
        myHook tm cont = do
          k <- lift get
          let n = k - 1
          lift $ put n
          if n == 0
          then return tm
          else cont

coveredBy :: FcPgm a -> FcTermInterp -> FcProgramInterp
coveredBy (FcPgmTerm _)          tm = FcPgmTerm tm
coveredBy (FcPgmDataDecl decl p) tm = FcPgmDataDecl                    decl  $ coveredBy p tm
coveredBy (FcPgmValDecl  decl p) tm = FcPgmValDecl  (fcValBindToInterp decl) $ coveredBy p tm

evalTest' :: Monad m
          => FcPgm a -> FcTermInterp -> FcET m FcTermInterp
evalTest' pgm tm = do
  us <- getUniqueSupplyM
  store <- get
  (((result,_),_),_) <- flip runUniqueSupplyT us
                      $ flip runStateT store
                      $ flip (flip runGenTmIdTExt undefined) undefined
                      $ flip runReaderT (const id,undefined,undefined)
                      $ unFcET
                      $ fcPgmToFcTm (coveredBy pgm tm) >>= fcEvalTm return
  return result
