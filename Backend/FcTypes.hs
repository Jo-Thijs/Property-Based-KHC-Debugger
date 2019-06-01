{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE EmptyDataDecls        #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Backend.FcTypes where

import Utils.Unique
import Utils.Var
import Utils.Kind
import Utils.PrettyPrint
import Utils.Annotated
import Utils.TermId
import Utils.FreeVars

import Data.List
import Data.Maybe (isJust)
import Data.Function (on)

import qualified Data.Map as M
import qualified Data.Foldable as F

-- * Arrow Type Constructor
-- ----------------------------------------------------------------------------

mkFcArrowTy :: FcType -> FcType -> FcType
mkFcArrowTy ty1 ty2 = FcTyApp (FcTyApp (FcTyCon fcArrowTyCon) ty1) ty2

fcArrowTyCon :: FcTyCon
fcArrowTyCon = FcTC (mkName (mkSym "(->)") arrowTyConUnique)

isFcArrowTy :: FcType -> Maybe (FcType, FcType)
isFcArrowTy (FcTyApp (FcTyApp (FcTyCon tc) ty1) ty2)
  | tc == fcArrowTyCon  = Just (ty1, ty2)
isFcArrowTy _other_type = Nothing

-- * Debug Type Constructor
-- ----------------------------------------------------------------------------

fcTestResultTyCon :: FcTyCon
fcTestResultTyCon = FcTC (mkName (mkSym "TestResult") testResultTyConUnique)

isFcTestResultTy :: FcType -> Bool
isFcTestResultTy (FcTyCon tc)
  | tc == fcTestResultTyCon  = True
isFcTestResultTy _other_type = False

-- * Debug Data Constructors
-- ----------------------------------------------------------------------------

fcBugDataCon :: FcDataCon
fcBugDataCon = FcDC (mkName (mkSym "Bug") bugDataConUnique)

isFcBugTm :: FcTm a -> Bool
isFcBugTm (FcTmDataCon _ dc)
  | dc == fcBugDataCon  = True
isFcBugTm _other_term = False

fcValidDataCon :: FcDataCon
fcValidDataCon = FcDC (mkName (mkSym "Valid") validDataConUnique)

isFcValidTm :: FcTm a -> Bool
isFcValidTm (FcTmDataCon _ dc)
  | dc == fcValidDataCon  = True
isFcValidTm _other_term = False

-- * Types
-- ----------------------------------------------------------------------------
data FcType = FcTyVar FcTyVar        -- ^ Type variable
            | FcTyAbs FcTyVar FcType -- ^ Type abstraction
            | FcTyApp FcType  FcType -- ^ Type application
            | FcTyCon FcTyCon        -- ^ Type constructor

-- | Syntactic equality on System F types
eqFcTypes :: FcType -> FcType -> Bool
eqFcTypes (FcTyVar v1)    (FcTyVar v2)    = v1 == v2
eqFcTypes (FcTyAbs v1 t1) (FcTyAbs v2 t2) = (v1 == v2)      && eqFcTypes t1 t2
eqFcTypes (FcTyApp t1 t2) (FcTyApp t3 t4) = eqFcTypes t1 t3 && eqFcTypes t2 t4
eqFcTypes (FcTyCon tc1)   (FcTyCon tc2)   = tc1 == tc2

eqFcTypes (FcTyVar {}) _ = False
eqFcTypes (FcTyAbs {}) _ = False
eqFcTypes (FcTyApp {}) _ = False
eqFcTypes (FcTyCon {}) _ = False

-- | Type Constructors
newtype FcTyCon = FcTC { unFcTC :: Name }

instance Eq FcTyCon where
  (==) = (==) `on` unFcTC

instance Ord FcTyCon where
  compare = compare `on` unFcTC

instance Symable FcTyCon where
  symOf = symOf . unFcTC

instance Named FcTyCon where
  nameOf = unFcTC

instance Uniquable FcTyCon where
  getUnique = getUnique . unFcTC

data FcTyConInfo
  = FcTCInfo { fc_tc_ty_con    :: FcTyCon     -- ^ The type constructor name
             , fc_tc_type_args :: [FcTyVar] } -- ^ Universal types

-- | Pretty print type constructor info
instance PrettyPrint FcTyConInfo where
  ppr (FcTCInfo tc type_args)
    = braces $ vcat $ punctuate comma
    $ [ text "fc_tc_ty_con"    <+> colon <+> ppr tc
      , text "fc_tc_type_args" <+> colon <+> ppr type_args
      ]

  needsParens _ = False

-- | Data Constructors
newtype FcDataCon = FcDC { unFcDC :: Name }
  deriving (Eq, Ord)

instance Show FcDataCon where
  show = show . unFcDC

instance Symable FcDataCon where
  symOf = symOf . unFcDC

instance Named FcDataCon where
  nameOf = unFcDC

instance Uniquable FcDataCon where
  getUnique = getUnique . unFcDC

data FcDataConInfo
  = FcDCInfo { fc_dc_data_con :: FcDataCon  -- ^ The data constructor name
             , fc_dc_univ     :: [FcTyVar]  -- ^ Universal type variables
             , fc_dc_parent   :: FcTyCon    -- ^ Parent type constructor
             , fc_dc_arg_tys  :: [FcType] } -- ^ Argument types

-- | Pretty print data constructor info
instance PrettyPrint FcDataConInfo where
  ppr (FcDCInfo dc univ tc arg_tys)
    = braces $ vcat $ punctuate comma
    $ [ text "fc_dc_data_con" <+> colon <+> ppr dc
      , text "fc_dc_univ"     <+> colon <+> ppr univ
      , text "fc_dc_parent"   <+> colon <+> ppr tc
      , text "fc_dc_arg_tys"  <+> colon <+> ppr arg_tys
      ]
  needsParens _ = False

constructFcTypeHM :: ([FcTyVar], [FcType], FcType) -> FcType
constructFcTypeHM (as, tys, ty) = fcTyAbs as (fcTyArr tys ty)

-- | Take apart a type constructor application
tyConAppMaybe :: FcType -> Maybe (FcTyCon, [FcType])
tyConAppMaybe ty = go ty []
  where
    go :: FcType -> [FcType] -> Maybe (FcTyCon, [FcType])
    go (FcTyApp ty1 ty2)  tys = go ty1 (ty2:tys)
    go (FcTyCon tc)       tys = Just (tc, tys)
    go _other_ty         _tys = Nothing

-- * Some smart constructors (uncurried variants)
-- ----------------------------------------------------------------------------

-- | Uncurried version of data constructor FcTyAbs
fcTyAbs :: [FcTyVar] -> FcType -> FcType
fcTyAbs vars ty = foldr FcTyAbs ty vars

-- | Uncurried version of data constructor FcTyArr
fcTyArr :: [FcType] -> FcType -> FcType
fcTyArr tys ty = foldr mkFcArrowTy ty tys

-- | Uncurried version of data constructor FcTyApp
fcTyApp :: FcType -> [FcType] -> FcType
fcTyApp ty tys = foldl FcTyApp ty tys

-- | Apply a type constructor to a bunch of types
fcTyConApp :: FcTyCon -> [FcType] -> FcType
fcTyConApp tc tys = fcTyApp (FcTyCon tc) tys

-- * Terms
-- ----------------------------------------------------------------------------
data FcTm a where
  FcTmVar      :: TermId -> FcTmVar                               -> FcTm a  -- ^ Term variable
  FcTmAbs      :: TermId -> FcTmVar -> FcType -> FcTm a           -> FcTm a  -- ^ Term abstraction: lambda x : ty . tm
  FcTmApp      :: TermId -> FcTm a -> FcTm a                      -> FcTm a  -- ^ Term application
  FcTmTyAbs    :: TermId -> FcTyVar -> FcTm a                     -> FcTm a  -- ^ Type abstraction: Lambda a . tm
  FcTmTyApp    :: TermId -> FcTm a -> FcType                      -> FcTm a  -- ^ Type application
  FcTmDataCon  :: TermId -> FcDataCon                             -> FcTm a  -- ^ Data constructor
  FcTmLet      :: TermId -> FcTmVar -> FcType -> FcTm a -> FcTm a -> FcTm a  -- ^ Let binding: let x : ty = tm in tm
  FcTmCase     :: TermId -> FcTm a -> [FcAlt a]                   -> FcTm a  -- ^ Case
  FcTmChunk    :: TermId -> ChunkId                         -> FcTermInterp  -- ^! Chunk

instance Show (FcTm a) where
  show (FcTmVar _ x) = show x
  show (FcTmAbs _ x _ tm) = "(\\" ++ show x ++ ". " ++ show tm ++ ")"
  show (FcTmApp _ tm1 tm2) = "(" ++ show tm1 ++ " " ++ show tm2 ++ ")"
  show (FcTmTyAbs _ a tm) = "(/\\" ++ show a ++ ". " ++ show tm ++ ")"
  show (FcTmTyApp _ tm _) = show tm ++ " []"
  show (FcTmDataCon _ dc) = show dc
  show (FcTmLet _ x _ tm1 tm2) = "(let " ++ show x ++ " = " ++ show tm1 ++ " in " ++ show tm2 ++ ")"
  show (FcTmCase _ tm alts) = "(case " ++ show tm ++ " of { " ++ concatMap ((++ "; ") . show) alts ++ " }" ++ ")"
  show (FcTmChunk _ cId) = "chunk_" ++ show cId

instance HasTermId (FcTm a) where
  termId (FcTmVar tId _)       = tId
  termId (FcTmAbs tId _ _ _)   = tId
  termId (FcTmApp tId _ _)     = tId
  termId (FcTmTyAbs tId _ _)   = tId
  termId (FcTmTyApp tId _ _)   = tId
  termId (FcTmDataCon tId _)   = tId
  termId (FcTmLet tId _ _ _ _) = tId
  termId (FcTmCase tId _ _)    = tId
  termId (FcTmChunk tId _)     = tId
  updateTermId tId (FcTmVar _ x)            = FcTmVar tId x
  updateTermId tId (FcTmAbs _ x ty tm)      = FcTmAbs tId x ty tm
  updateTermId tId (FcTmApp _ tm1 tm2)      = FcTmApp tId tm1 tm2
  updateTermId tId (FcTmTyAbs _ a tm)       = FcTmTyAbs tId a tm
  updateTermId tId (FcTmTyApp _ tm ty)      = FcTmTyApp tId tm ty
  updateTermId tId (FcTmDataCon _ con)      = FcTmDataCon tId con
  updateTermId tId (FcTmLet _ x ty tm1 tm2) = FcTmLet tId x ty tm1 tm2
  updateTermId tId (FcTmCase _ tm alts)     = FcTmCase tId tm alts
  updateTermId tId (FcTmChunk _ cId)        = FcTmChunk tId cId

newtype ChunkId = ChunkId Integer deriving (Eq, Ord, Show)
type ChunkTable = M.Map ChunkId FcTermInterp

type TemplateAssocs = [(RnTmVar, FcTermInterp)]

mapTemplateAssocs :: (FcTermInterp -> FcTermInterp) -> TemplateAssocs -> TemplateAssocs
mapTemplateAssocs f = map (\(v, tm) -> (v, f tm))

data FcTermGeneral
data FcTermInterpreter

type FcTerm = FcTm FcTermGeneral
type FcTermInterp = FcTm FcTermInterpreter

fcTermToInterp :: FcTm a -> FcTermInterp
fcTermToInterp (FcTmVar tId var)            = FcTmVar tId var
fcTermToInterp (FcTmAbs tId var ty tm)      = FcTmAbs tId var ty (fcTermToInterp tm)
fcTermToInterp (FcTmApp tId tm1 tm2)        = FcTmApp tId (fcTermToInterp tm1) (fcTermToInterp tm2)
fcTermToInterp (FcTmTyAbs tId tyVar tm)     = FcTmTyAbs tId tyVar (fcTermToInterp tm)
fcTermToInterp (FcTmTyApp tId tm ty)        = FcTmTyApp tId (fcTermToInterp tm) ty
fcTermToInterp (FcTmDataCon tId con)        = FcTmDataCon tId con
fcTermToInterp (FcTmLet tId var ty tm1 tm2) = FcTmLet tId var ty (fcTermToInterp tm1) (fcTermToInterp tm2)
fcTermToInterp (FcTmCase tId tm alts)       = FcTmCase tId (fcTermToInterp tm) (map fcAltToInterp alts)
fcTermToInterp (FcTmChunk tId cId)          = FcTmChunk tId cId

fcAltToInterp :: FcAlt a -> FcAltInterp
fcAltToInterp (FcAlt pat tm) = FcAlt pat (fcTermToInterp tm)

-- GEORGE: You should never need to make terms and patterns instances of Eq. If
-- you do it means that something is probably wrong (the only setting where you
-- need stuff like this is for optimizations).

-- | Patterns
data FcPat = FcConPat FcDataCon [FcTmVar]

-- | Case alternative(s)
data FcAlt a = FcAlt FcPat (FcTm a)
type FcAlternative = FcAlt FcTermGeneral
type FcAltInterp = FcAlt FcTermInterpreter

instance Show (FcAlt a) where
  show (FcAlt pat tm) = show pat ++ " -> " ++ show tm

instance Show FcPat where
  show (FcConPat con xs) = show con ++ concatMap ((" " ++) . show) xs

-- * Some smart constructors (uncurried variants)
-- ----------------------------------------------------------------------------

-- | Uncurried version of data constructor FcTmAbs
fcTmAbs :: [(FcTmVar, FcType)] -> FcTm a -> FcTm a
fcTmAbs binds tm = foldr (uncurry (FcTmAbs invalidTmId)) tm binds

-- | Uncurried version of data constructor FcTmTyAbs
fcTmTyAbs :: [FcTyVar] -> FcTm a -> FcTm a
fcTmTyAbs tvs tm = foldr (FcTmTyAbs invalidTmId) tm tvs

-- | Uncurried version of data constructor FcTmApp
fcTmApp :: FcTm a -> [FcTm a] -> FcTm a
fcTmApp tm tms = foldl (FcTmApp invalidTmId) tm tms

-- | Uncurried version of data constructor FcTmTyApp
fcTmTyApp :: FcTm a -> [FcType] -> FcTm a
fcTmTyApp tm tys = foldl (FcTmTyApp invalidTmId) tm tys

-- | Create a data constructor application
fcDataConApp :: FcDataCon -> FcType -> [FcTm a] -> FcTm a
fcDataConApp dc ty = fcTmApp (FcTmTyApp invalidTmId (FcTmDataCon invalidTmId dc) ty)

-- | Apply a term to a list of dictionary variables
fcDictApp :: FcTm a -> [DictVar] -> FcTm a
fcDictApp tm ds = foldl (FcTmApp invalidTmId) tm (map (FcTmVar invalidTmId) ds)

-- * Programs and declarations
-- ----------------------------------------------------------------------------

-- | Data Type Declaration
data FcDataDecl = FcDataDecl { fdata_decl_tc   :: FcTyCon                 -- ^ Type Constructor
                             , fdata_decl_tv   :: [FcTyVar]               -- ^ Universal Type variables
                             , fdata_decl_cons :: [(FcDataCon, [FcType])] -- ^ Data Constructors
                             }

-- | Top-level Value Binding
data FcValBnd a = FcValBind { fval_bind_var :: FcTmVar   -- ^ Variable Name
                            , fval_bind_ty  :: FcType    -- ^ Variable Type
                            , fval_bind_tm  :: FcTm a    -- ^ Variable Value
                            }

type FcValBind = FcValBnd FcTermGeneral

-- | Program
data FcPgm a = FcPgmDataDecl FcDataDecl   (FcPgm a) -- ^ Data Declaration
             | FcPgmValDecl (FcValBnd a) (FcPgm a) -- ^ Value Binding
             | FcPgmTerm (FcTm a)                   -- ^ Term

type FcProgram       = FcPgm FcTermGeneral
type FcProgramInterp = FcPgm FcTermInterpreter

fcPgmToInterp :: FcPgm a -> FcProgramInterp
fcPgmToInterp (FcPgmDataDecl decl p) = FcPgmDataDecl decl (fcPgmToInterp p)
fcPgmToInterp (FcPgmValDecl  decl p) = FcPgmValDecl (fcValBindToInterp decl) (fcPgmToInterp p)
fcPgmToInterp (FcPgmTerm tm)         = FcPgmTerm (fcTermToInterp tm)

fcValBindToInterp :: FcValBnd a -> FcValBnd FcTermInterpreter
fcValBindToInterp (FcValBind var ty tm) = FcValBind var ty (fcTermToInterp tm)

-- * Free term variables

instance ContainsFreeTmVars (FcTm a) FcTmVar where
  ftmvsOf (FcTmVar _ x)           = [x]
  ftmvsOf (FcTmAbs _ x _ tm)      = ftmvsOf tm \\ [x]
  ftmvsOf (FcTmApp _ tm1 tm2)     = nub $ ftmvsOf tm1 ++ ftmvsOf tm2
  ftmvsOf (FcTmTyAbs _ _ tm)      = ftmvsOf tm
  ftmvsOf (FcTmTyApp _ tm _ )     = ftmvsOf tm
  ftmvsOf (FcTmDataCon _ _)       = []
  ftmvsOf (FcTmLet _ x _ tm1 tm2) = nub $ (ftmvsOf tm1 ++ ftmvsOf tm2) \\ [x]
  ftmvsOf (FcTmCase _ tm alts)    = nub $ ftmvsOf tm ++ ftmvsOf alts
  ftmvsOf (FcTmChunk _ _)         = []

instance ContainsFreeTmVars (FcAlt a) FcTmVar where
  ftmvsOf (FcAlt _ tm) = ftmvsOf tm

-- * Free type variables

instance ContainsFreeTyVars (FcTm a) FcTyVar where
  ftyvsOf (FcTmVar _ _)            = []
  ftyvsOf (FcTmAbs _ _ ty tm)      = nub $ ftyvsOf ty ++ ftyvsOf tm
  ftyvsOf (FcTmApp _ tm1 tm2)      = nub $ ftyvsOf tm1 ++ ftyvsOf tm2
  ftyvsOf (FcTmTyAbs _ tv tm)      = ftyvsOf tm \\ [tv]
  ftyvsOf (FcTmTyApp _ tm ty)      = nub $ ftyvsOf ty ++ ftyvsOf tm
  ftyvsOf (FcTmDataCon _ _)        = []
  ftyvsOf (FcTmLet _ _ ty tm1 tm2) = nub $ ftyvsOf ty ++ ftyvsOf tm1 ++ ftyvsOf tm2
  ftyvsOf (FcTmCase _ tm alts)     = nub $ ftyvsOf tm ++ ftyvsOf alts
  ftyvsOf (FcTmChunk _ _)          = []

instance ContainsFreeTyVars (FcAlt a) FcTyVar where
  ftyvsOf (FcAlt _ tm) = ftyvsOf tm

instance ContainsFreeTyVars FcType FcTyVar where
  ftyvsOf (FcTyVar tv)      = [tv]
  ftyvsOf (FcTyAbs tv ty)   = ftyvsOf ty \\ [tv]
  ftyvsOf (FcTyApp ty1 ty2) = nub $ ftyvsOf ty1 ++ ftyvsOf ty2
  ftyvsOf (FcTyCon _)       = []

-- * Pretty printing
-- ----------------------------------------------------------------------------

isFcTyApp :: FcType -> Bool
isFcTyApp (FcTyApp {}) = True
isFcTyApp _other       = False

isFcTyAbs :: FcType -> Bool
isFcTyAbs (FcTyAbs {}) = True
isFcTyAbs _other       = False

-- | Pretty print types
instance PrettyPrint FcType where
  ppr ty | Just (ty1, ty2) <- isFcArrowTy ty
         , let d1 = if isJust (isFcArrowTy ty1) || isFcTyAbs ty1
                      then pprPar ty1
                      else ppr ty1
         , let d2 = if isJust (isFcArrowTy ty2) || isFcTyApp ty2
                      then ppr ty2
                      else pprPar ty2
         = d1 <+> arrow <+> d2

  ppr (FcTyVar a)       = ppr a
  ppr (FcTyAbs a ty)    = text "forall" <+> ppr a <> dot <+> ppr ty
  ppr (FcTyApp ty1 ty2)
    | FcTyApp {} <- ty1 = ppr ty1    <+> pprPar ty2
    | otherwise         = pprPar ty1 <+> pprPar ty2
  ppr (FcTyCon tc)      = ppr tc

  needsParens (FcTyApp {}) = True
  needsParens (FcTyAbs {}) = True
  needsParens (FcTyVar {}) = False
  needsParens (FcTyCon {}) = False

-- | Pretty print type constructors
instance PrettyPrint FcTyCon where
  ppr           = ppr . symOf -- Do not show the uniques on the constructors
  needsParens _ = False

-- | Pretty print data constructors
instance PrettyPrint FcDataCon where
  ppr           = ppr . symOf -- Do not show the uniques on the constructors
  needsParens _ = False

-- | Pretty print terms
instance PrettyPrint (FcTm a) where
  ppr (FcTmAbs _ x ty tm)              = hang (backslash <> parens (ppr x <+> dcolon <+> ppr ty) <> dot) 2 (ppr tm)
  ppr (FcTmVar _ x)                    = ppr x
  ppr (FcTmApp _ tm1 tm2)
    | FcTmApp   {} <- tm1              = ppr tm1    <+> pprPar tm2
    | FcTmTyApp {} <- tm1              = ppr tm1    <+> pprPar tm2
    | otherwise                        = pprPar tm1 <+> pprPar tm2
  ppr (FcTmTyAbs _ a tm)               = hang (colorDoc yellow (text "/\\") <> ppr a <> dot) 2 (ppr tm)
  ppr (FcTmTyApp _ tm ty)              = pprPar tm <+> brackets (ppr ty)
  ppr (FcTmDataCon _ dc)               = ppr dc
  ppr (FcTmLet _ x ty tm1 tm2)
    =  (colorDoc yellow (text "let") <+> ppr x <+> ((colon <+> ppr ty) $$ (equals <+> ppr tm1)))
    $$ (colorDoc yellow (text "in" ) <+> ppr tm2)
  ppr (FcTmCase _ tm cs)               = hang (colorDoc yellow (text "case") <+> ppr tm <+> colorDoc yellow (text "of"))
                                            2 (vcat $ map ppr cs)
  ppr (FcTmChunk _ (ChunkId n))        = colorDoc turquoise (text $ "Chnk_" ++ show n)

  needsParens (FcTmApp      {}) = True
  needsParens (FcTmTyApp    {}) = True
  needsParens (FcTmLet      {}) = True
  needsParens (FcTmCase     {}) = True
  needsParens (FcTmAbs      {}) = True
  needsParens (FcTmVar      {}) = False
  needsParens (FcTmTyAbs    {}) = True
  needsParens (FcTmDataCon  {}) = False
  needsParens (FcTmChunk    {}) = False

-- | Pretty print patterns
instance PrettyPrint FcPat where
  ppr (FcConPat dc xs) = ppr dc <+> hsep (map ppr xs)
  needsParens _        = True

-- | Pretty print case alternatives
instance PrettyPrint (FcAlt a) where
  ppr (FcAlt p tm) = ppr p <+> arrow <+> ppr tm
  needsParens _    = True

-- | Pretty print data declarations
instance PrettyPrint FcDataDecl where
  ppr (FcDataDecl tc as dcs) = hsep [colorDoc green (text "data"), ppr tc, hsep (map ppr ann_as), cons]
    where
      ann_as = map (\a -> (a :| kindOf a)) as
      ppr_dc (dc, tys) = hsep (colorDoc yellow (char '|') : ppr dc : map pprPar tys)

      cons = sep $ case dcs of
        []               -> []
        ((dc, tys):rest) -> hsep (equals : ppr dc : map pprPar tys) : map ppr_dc rest

  needsParens _ = False

-- | Pretty print top-level value bindings
instance PrettyPrint (FcValBnd a) where
  ppr (FcValBind x ty tm) = hsep [ colorDoc yellow (text "let"), ppr x
                                 , vcat [ colon <+> ppr ty, equals <+> ppr tm ]
                                 ]
  needsParens _ = False

-- | Pretty print programs
instance PrettyPrint (FcPgm a) where
  ppr (FcPgmDataDecl datadecl pgm) = ppr datadecl $$ ppr pgm
  ppr (FcPgmValDecl  valbind  pgm) = ppr valbind  $$ ppr pgm
  ppr (FcPgmTerm tm)               = ppr tm
  needsParens _ = False
