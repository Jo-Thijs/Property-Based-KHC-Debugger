{-# LANGUAGE GADTs, FlexibleContexts, RankNTypes #-}
module Backend.Debugger where

import Frontend.HsTypes
import Backend.FcTypes
import Utils.Unique
import Utils.Var
import Utils.Substitution
import Utils.Ctx
import Utils.Annotated
import Utils.Kind
import Utils.TermId
import Utils.FreeVars
import Utils.PrettyPrint

import Control.Monad.State
import Control.Monad.Except

import Data.Maybe
import Data.List
import qualified Data.Map as M

import Debug.Trace

-- | Tables
infixl 4 <-*->
(<-*->) :: TermTable (a -> b) -> TermTable a -> TermTable b
tf <-*-> ta = M.mapWithKey (flip ($) . (ta M.!)) tf

data TermMetaData = TMD { getRnTerm :: RnTerm
                        , getRnType :: RnMonoTy
                        , getSourceRegion :: SourceRegion }

type TermSrcTable = TermTable SourceRegion

type TermMetaTable = TermTable TermMetaData

genMetaDataTable :: TermTable RnTerm
                 -> TermTable RnMonoTy
                 -> TermTable SourceRegion
                 -> TermMetaTable
genMetaDataTable t1 t2 t3 = TMD <$> t1 <-*-> t2 <-*-> t3

genAutoTable :: Program a -> TermTable (Term a)
genAutoTable pgm = M.fromList [(termId tm, tm) | tm <- subtermsOfPgm pgm]

subtermsOfTerm :: Term a -> [Term a]
subtermsOfTerm tm@(TmVar _ _)         = [tm]
subtermsOfTerm tm@(TmCon _ _)         = [tm]
subtermsOfTerm tm@(TmAbs _ _ tm1)     = tm : subtermsOfTerm tm1
subtermsOfTerm tm@(TmApp _ tm1 tm2)   = tm : (subtermsOfTerm tm1 ++ subtermsOfTerm tm2)
subtermsOfTerm tm@(TmLet _ _ tm1 tm2) = tm : (subtermsOfTerm tm1 ++ subtermsOfTerm tm2)
subtermsOfTerm tm@(TmCase _ tm1 alts) = tm : (subtermsOfTerm tm1 ++ concatMap subtermsOfAlt alts)

subtermsOfAlt :: HsAlt a -> [Term a]
subtermsOfAlt (HsAlt _ tm) = subtermsOfTerm tm

subtermsOfPgm :: Program a -> [Term a]
subtermsOfPgm (PgmExp  tm)       = subtermsOfTerm tm
subtermsOfPgm (PgmCls  decl pgm) = subtermsOfPgm pgm
subtermsOfPgm (PgmInst decl pgm) = subtermsOfInstDecl decl ++ subtermsOfPgm pgm
subtermsOfPgm (PgmData decl pgm) = subtermsOfPgm pgm
subtermsOfPgm (PgmFunc decl pgm) = subtermsOfFuncDecl decl ++ subtermsOfPgm pgm

subtermsOfInstDecl :: InsDecl a -> [Term a]
subtermsOfInstDecl = subtermsOfTerm . imetm

subtermsOfFuncDecl :: FuncDecl a -> [Term a]
subtermsOfFuncDecl = subtermsOfTerm . fdeftm

-- | Debugger strucures

type Tests = Either (RnMonoTy,FcTermInterp) RnTerm -> [Maybe (RnTerm,FcTermInterp)]

data SrcRepr = Rep { getCoreTerm :: RnTerm
                   , getSubsts :: [(RnTmVar, SrcRepr)] }
               deriving Show

constructFromRepr :: SrcRepr -> RnTerm
constructFromRepr (Rep baseTm substs) =
  let heads = map (\(var,tm) -> (var, constructFromRepr tm)) substs
  in  foldl (flip (uncurry (TmLet invalidTmId))) baseTm heads

pprSrcReprWithMeta :: TermSrcTable -> SrcRepr -> Doc
pprSrcReprWithMeta tab (Rep core bnds) = vcat (map pprBnd (reverse bnds) ++ [pprTm id core])
  where
    pprTm f tm      = vcat [ colorDoc green $
                             text "-- found at" <+> (ppr $ tab M.! termId tm)
                           , f (ppr tm)]
    pprBnd (v,repr) =  colorDoc yellow (text "let")
                   <+> ppr v
                   <+> colorDoc yellow (text "=")
                   <+> pprSrcReprWithMeta tab repr

data ShrinkTrace = ST SrcRepr RnTerm SrcRepr RnTerm Integer

newShrinkTrace :: SrcRepr -> RnTerm -> ShrinkTrace
newShrinkTrace repr tester = ST repr tester repr tester 0

lastShrunk :: ShrinkTrace -> (SrcRepr, RnTerm)
lastShrunk (ST _ _ repr tester _) = (repr, tester)

isShrinkTraceNew :: ShrinkTrace -> Bool
isShrinkTraceNew (ST _ _ _ _ n) = n == 0

mapShrinkTrace :: (SrcRepr -> SrcRepr) -> ShrinkTrace -> ShrinkTrace
mapShrinkTrace f (ST x x' y y' n) = ST (f x) x' (f y) y' n

pprShrinkTraceWithMeta :: TermSrcTable -> TermSrcTable -> ShrinkTrace -> Doc
pprShrinkTraceWithMeta mainTab testerTab (ST x x' y y' _) =
  vcat [ text "Shrunk: " <+> pprx
       , text "to:     " <+> ppry ]
  where
    pprx = vcat [ colorDoc green $  text "-- failed the property at"
                                <+> ppr (testerTab M.! termId x')
                , pprSrcReprWithMeta mainTab x ]
    ppry = vcat [ colorDoc green $  text "-- failed the property at"
                                <+> ppr (testerTab M.! termId y')
                , ppr $ constructFromRepr y ]

instance Semigroup ShrinkTrace where
  ST x1 x1' _ _ n1 <> ST _ _ y2 y2' n2 = ST x1 x1' y2 y2' (n1 + n2 + 1)

performTests :: Monad m
             => Int -> (Bool -> FcTermInterp -> m FcTermInterp) -> Tests
             -> Maybe (RnMonoTy,FcTermInterp) -> m SrcRepr -> m (Maybe ShrinkTrace)
performTests depth evaluate tests optional testeeReprGen = do
    testeeRepr <- maybe testeeReprGen (const $ return undefined) optional
    let rnTestee = constructFromRepr testeeRepr
    let applicableTests = catMaybes $ tests $ maybe (Right rnTestee) Left optional
    testResults <- mapM (fmap check . evaluate (isJust optional) . snd) applicableTests
    if any isNothing testResults
    then return Nothing --error $ "Invalid test result encountered during debugging"
    else if any (== Just False) testResults
         then do
           testeeRepr' <- testeeReprGen
           let (tester,_) = head
                          $ map fst
                          $ filter ((== Just False) . snd)
                          $ zip applicableTests testResults
           Just . (newShrinkTrace testeeRepr' tester <>) <$>
             shrinkHook depth evaluate tests testeeRepr' tester
         else return Nothing
  where
    check :: FcTermInterp -> Maybe Bool
    check testResult | isFcValidTm testResult = Just True
                     | isFcBugTm   testResult = Just False
                     | otherwise              = Nothing

-- | Debug phase 1: Find first bug occurrence (testee generation + test evaluation)

debugHook :: Monad m
          => (ShrinkTrace -> m FcTermInterp -> m FcTermInterp)
          -> (Bool -> FcTermInterp -> m FcTermInterp)
          -> (TermId -> Bool)
          -> Tests
          -> (FcTermInterp -> m SrcRepr)
          -> (TermId -> m RnMonoTy)
          -> FcTermInterp -> m FcTermInterp -> m FcTermInterp
debugHook handler evaluate maySkip tests getRepr getTy tm evaluation = do
  let fcTestee = case tm of
        FcTmApp _ tm' _     -> tm'
        FcTmCase _ tm' _    -> tm'
        _                   -> error "Unexpected redex encountered in debug mode"
  let tId = termId fcTestee
  if isTmIdInvalid tId
  then evaluation
  else if maySkip tId
       then evaluation
       else do
        ty <- getTy tId
        let testeeReprGen = getRepr fcTestee
        results <- performTests 4 evaluate tests (Just (ty,fcTestee)) testeeReprGen
        case results of
          Just trace -> handler trace evaluation
          Nothing    -> evaluation

-- | Debug phase 2: Shrink testees

shrinkHook :: Monad m
           => Int -> (Bool -> FcTermInterp -> m FcTermInterp) -> Tests
           -> SrcRepr -> RnTerm -> m ShrinkTrace
shrinkHook depth evaluate tests (Rep core bnds) tester = do
  if depth < 1
  then return $ newShrinkTrace (Rep core bnds) tester
  else -- Let Collapsing
    case letCollapsingHook (Rep core bnds) of
      Just repr -> (newShrinkTrace repr tester <>) <$> shrinkHook depth' evaluate tests repr tester
      Nothing   -> do
        -- Applying default shrinking rules to term body/core
        let subs = zip (termConts core) (subtermsOfTerm core)
        result <- firstM (localSearch (flip Rep bnds)) subs
        case result of
          Just trace -> (trace <>) <$> uncurry (shrinkHook depth' evaluate tests) (lastShrunk trace)
          Nothing    -> do
            -- Shrink term bindings
            results <- mapM (uncurry $ uncurry bndSearch) (parts bnds)
            case listToMaybe $ filter (not . isShrinkTraceNew) results of
              Just trace -> (trace <>) <$> uncurry (shrinkHook depth' evaluate tests) (lastShrunk trace)
              Nothing    -> return $ newShrinkTrace (Rep core bnds) tester
  where
    --localSearch :: Monad m
    --            => (RnTerm -> SrcRepr) -> (RnTerm -> RnTerm, RnTerm) -> m (Maybe ShrinkTrace)
    localSearch f (cont, subTm) = do
      let cands = map cont $ termCuts subTm
      r <- firstM (\cand -> performTests depth' evaluate tests Nothing (return $ f cand)) cands
      return r
    
    --bndSearch :: Monad m
    --          => [(RnTmVar, SrcRepr)] -> (RnTmVar, SrcRepr) -> [(RnTmVar, SrcRepr)]
    --          -> m ShrinkTrace
    bndSearch bs1 (x,repr) bs2 =  mapShrinkTrace (enhance bs1 bs2 x)
                              <$> shrinkHook depth' evaluate (enhancedTests bs1 bs2 x) repr tester
    
    --enhance :: [(RnTmVar, SrcRepr)] -> [(RnTmVar, SrcRepr)] -> RnTmVar -> SrcRepr -> SrcRepr
    enhance bs1 bs2 x = Rep core
                      . (bs1 ++)
                      . (: bs2)
                      . (,) x
    
    --enhancedTests :: [(RnTmVar, SrcRepr)] -> [(RnTmVar, SrcRepr)] -> RnTmVar -> Tests
    enhancedTests bs1 bs2 x (Right tm) = tests
                                       $ Right
                                       $ constructFromRepr
                                       $ enhance bs1 bs2 x
                                       $ flip Rep []
                                       $ tm

    depth' = depth - 1

letCollapsingHook :: SrcRepr -> Maybe SrcRepr
letCollapsingHook (Rep core bnds) =
  let fvs = ftmvsOf core
      bnds' = filter ((flip elem fvs) . fst) bnds
      --bnds'' = map head $ filter (\((x,_):bs) -> notElem x $ map fst bs) (init $ tails bnds')
      Rep core''' bnds''' = f2 $ f1 (Rep core bnds')
  in  if length bnds == length bnds'''
      then Nothing
      else Just $ Rep core''' bnds'''
  where f1 (Rep core' []          ) = Rep core' []
        f1 (Rep core' (bnd':bnds')) = case bnd' of
                                        (x,Rep tm@(TmCon _ _) _) -> f1 $ Rep (substVar x tm core') bnds'
                                        _                        -> let Rep core'' bnds'' = f1 $ Rep core' bnds'
                                                                    in  Rep core'' (bnd':bnds'')
        
        f2 (Rep core' []          ) = Rep core' []
        f2 (Rep core' (bnd':bnds')) = case bnd' of
                                        (x,Rep tm bs) ->
                                          if null (filter (flip elem $ map fst bs) $ ftmvsOf tm)
                                          && not (elem x $ ftmvsOf tm)
                                          && frntmvOccurrenceCount x core' == 1
                                          then f2 $ Rep (substVar x tm core') bnds'
                                          else let Rep core'' bnds'' = f2 $ Rep core' bnds'
                                               in  Rep core'' (bnd':bnds'')

termConts :: Term a -> [Term a -> Term a]
termConts (TmVar tId _)         = [id]
termConts (TmCon tId _)         = [id]
termConts (TmAbs tId x tm1)     = id : map (TmAbs tId x .) (termConts tm1)
termConts (TmApp tId tm1 tm2)   = id : ( map (flip (TmApp tId) tm2 .) (termConts tm1)
                                      ++ map (      TmApp tId  tm1 .) (termConts tm2) )
termConts (TmLet tId x tm1 tm2) = id : ( map (flip (TmLet tId x) tm2 .) (termConts tm1)
                                      ++ map (      TmLet tId x  tm1 .) (termConts tm2) )
termConts (TmCase tId tm1 alts) = id : ( map (flip (TmCase tId) alts .) (termConts tm1)
                                      ++ mapInsert (\(HsAlt pat _) -> HsAlt pat)
                                                   (TmCase tId tm1)
                                                   alts )

termCuts :: Term a -> [Term a]
termCuts (TmApp _ tm1 tm2)   = tm1 : tm2 : (termCuts tm1 ++ termCuts tm2)
termCuts (TmCase _ tm1 alts) = tm1 : termCuts tm1
termCuts  _                  = []

mapInsert :: Monad m => (a -> m a) -> ([a] -> b) -> [a] -> [m b]
mapInsert f g = map (\((xs1,x),xs2) -> g . (xs1 ++) . (: xs2) <$> f x) . parts

parts :: [a] -> [(([a],a),[a])]
parts xs = zip (zip (inits xs) xs) (tail $ tails xs)

firstM :: Monad m => (a -> m (Maybe b)) -> [a] -> m (Maybe b)
firstM f []     = return Nothing
firstM f (x:xs) = f x >>= maybe (firstM f xs) (return . Just)

frntmvOccurrenceCount :: RnTmVar -> RnTerm -> Integer
frntmvOccurrenceCount x (TmCon _ dc)        = 0
frntmvOccurrenceCount x (TmVar _ y)         = if x == y then 1 else 0
frntmvOccurrenceCount x (TmAbs _ y tm)      = if x == y then 0 else frntmvOccurrenceCount x tm
frntmvOccurrenceCount x (TmApp _ tm1 tm2)   = frntmvOccurrenceCount x tm1 + frntmvOccurrenceCount x tm2
frntmvOccurrenceCount x (TmLet _ y tm1 tm2) = if x == y then 0 else frntmvOccurrenceCount x tm1 + frntmvOccurrenceCount x tm2
frntmvOccurrenceCount x (TmCase _ tm alts)  = frntmvOccurrenceCount x tm + sum (map (frntmvOccurrenceCountAlt x) alts)

frntmvOccurrenceCountAlt :: RnTmVar -> RnAlt -> Integer
frntmvOccurrenceCountAlt x (HsAlt (HsPat _ ys) tm) = if elem x ys then 0 else frntmvOccurrenceCount x tm