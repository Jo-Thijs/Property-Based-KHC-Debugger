module Frontend.HsParser (hsParse, hsParseTesters) where

-- | Main types
import Frontend.HsTypes
import Utils.Kind (Kind(..))
import Utils.Var (Sym, mkSym, PsTyVar, mkPsTyVar, PsTmVar, mkPsTmVar)
import Utils.Annotated (Ann((:|)))
import Utils.TermId

-- | Utilities
import Control.Applicative (Alternative, liftA2, (<**>))
import Data.Functor (($>))
import Data.Void
import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.State

-- Lexer
import qualified Text.Megaparsec.Char.Lexer as L

-- Parser
import Text.Megaparsec
import Text.Megaparsec.Char

-- * The Parsing Monad
-- ------------------------------------------------------------------------------
type PsM = ReaderT SpaceConsumer (GenTmIdT SourceRegion (Parsec Void String))
newtype SpaceConsumer = SC (PsM ())

-- | Parse a complete program from a file
hsParse :: FilePath -> IO (Either String (PsProgram, TermTable SourceRegion))
hsParse = buildParser (sc *> pProgram <* eof)

hsParseTesters :: FilePath -> IO (Either String ([PsTerm], TermTable SourceRegion))
hsParseTesters = buildParser (sc *> some (symbol ">" *> pTerm) <* eof)

buildParser :: PsM a -> FilePath -> IO (Either String (a, TermTable SourceRegion))
buildParser parser path = readFile path >>= \contents ->
  return $ case runP contents $ runG $ runR parser of
    Left err       -> Left (errorBundlePretty err)
    Right (p, tab) -> Right (p, getTermTable tab)
  where
    runR = flip runReaderT (SC sc)
    runG = flip runGenTmIdT initialTermId
    runP = flip $ flip runParser path

-- * The Parser Monad State
-- ------------------------------------------------------------------------------

-- | Initial Parser Term Data State (starting term identifiers by 0)
initialSourceRegion :: SourcePos -> SourceRegion
initialSourceRegion tmStart = SrcReg { sourceFile = sourceName tmStart
                                     , sourceStartLine = unPos $ sourceLine tmStart
                                     , sourceStartCol = unPos $ sourceColumn tmStart
                                     , sourceEndLine = undefined
                                     , sourceEndCol = undefined }

finishSourceRegion :: SourcePos -> SourceRegion -> SourceRegion
finishSourceRegion tmEnd region
  | sourceName tmEnd /= sourceFile region = error $ "Mismatching source files while parsing: \""
                                                 ++ sourceFile region ++ "\" and  \""
                                                 ++ sourceName tmEnd ++ "\""
  | otherwise                             = region { sourceEndLine = unPos $ sourceLine tmEnd
                                                   , sourceEndCol = unPos $ sourceColumn tmEnd }

-- * Unique Term Generation by Regions
-- ------------------------------------------------------------------------------
type TermRegionT = StateT (SourcePos, Maybe TermId)

-- | Marks where a term may start
openRegion :: TermRegionT PsM ()
openRegion = getSourcePos >>= \pos -> put (pos, Nothing)

-- | Generates a new term identifier
newTerm :: (TermId -> a) -> TermRegionT PsM a
newTerm f = do
    (pos, Nothing) <- get
    tId <- genTerm (initialSourceRegion pos)
    modify $ const (pos, Just tId)
    return $ f tId

-- | Marks the end of the current region
-- | and starts a new region starting at the same position as the previous region
-- | (handy for using in combination with chainl1)
splitRegion :: TermRegionT PsM ()
splitRegion = do
    currentPos <- getSourcePos
    (startPos, optionalTmId) <- get
    maybe (return ()) (updateTermInfo (finishSourceRegion currentPos)) optionalTmId
    put (startPos, Nothing)

-- | Marks where a term may end
closeRegion :: TermRegionT PsM ()
closeRegion = splitRegion <* put undefined

-- | Transforms an unclosed region to a closed one
runRegion :: TermRegionT PsM a -> PsM a
runRegion p = evalStateT p undefined

-- | Perform in a new region
asRegion :: TermRegionT PsM a -> PsM a
asRegion p = runRegion $ openRegion *> p <* closeRegion

-- * The Lexer and Utilities
-- ------------------------------------------------------------------------------

-- | The space comsumer
sc :: PsM ()
sc = L.space space1 (L.skipLineComment "--") (L.skipBlockComment "{--" "--}")

-- | Turn a parser indent aware
indent :: PsM a -> PsM a
indent p =
  ask >>= \(SC sc') ->
    L.lineFold sc' $ \sc'' ->
      local (const (SC (try sc'' <|> return ()))) (p <* sc')

-- | Turn a parser into a lexeme parser
lexeme :: PsM a -> PsM a
lexeme x = ask >>= \(SC sc') -> L.lexeme sc' x

-- | List of reserved names
reservedNames :: [String]
reservedNames =
  ["let", "in", "case", "of", "data", "class", "instance", "where", "forall"]

-- | Parse an identifier given a parser for the first character
identifier :: PsM Char -> PsM Sym
identifier firstChar = mkSym <$> (lexeme . try) (p >>= check)
  where
    p = (:) <$> firstChar <*> many (alphaNumChar <|> oneOf "_'")
    check x =
      if x `elem` reservedNames
        then fail $ "keyword " ++ show x ++ " cannot be an identifier"
        else return x

-- | Parse an identifier that starts with a lowercase
lowerIdent :: PsM Sym
lowerIdent = identifier lowerChar

-- | Parse an identifier that starts with an uppercase
upperIdent :: PsM Sym
upperIdent = identifier (lift $ lift upperChar)

-- | Parse a specific string
symbol :: String -> PsM ()
symbol s = ask >>= \(SC sc') -> L.symbol sc' s $> ()

-- | Parse something enclosed in parentheses
parens :: PsM a -> PsM a
parens = between (symbol "(") (symbol ")")

-- | Parse a dot
dot :: PsM ()
dot = symbol "."

-- | Parse a comma-separated list of things
commaSep :: PsM a -> PsM [a]
commaSep = (`sepBy` symbol ",")

-- | The Monoidal applicative operator
infixl 5 <&>
(<&>) :: Applicative f => f a -> f b -> f (a, b)
(<&>) = liftA2 (,)

-- | Left associative operator chaining
chainl1 :: Alternative m => m a -> m (a -> a -> a) -> m a
chainl1 p op = scan where
  scan = p <**> rst
  rst = (\f y g x -> g (f x y)) <$> op <*> p <*> rst <|> pure id

-- | Right associative operator chaining
chainr1 :: Alternative m => m a -> m (a -> a -> a) -> m a
chainr1 p op = scan where
  scan = p <**> rst
  rst = (flip <$> op <*> scan) <|> pure id

-- * Parse Declarations and Programs
-- ------------------------------------------------------------------------------

-- | Parse a program
pProgram :: PsM PsProgram
pProgram  =  PgmCls  <$> pClsDecl  <*> pProgram
         <|> PgmInst <$> pInstDecl <*> pProgram
         <|> PgmData <$> pDataDecl <*> pProgram
         <|> PgmFunc <$> pFuncDecl <*> pProgram
         <|> PgmExp  <$> pTerm

-- | Parse a class declaration
pClsDecl :: PsM PsClsDecl
pClsDecl  =  indent $ (\ctx cls a (m,ty) -> ClsD ctx cls a m ty)
         <$  symbol "class"
         <*> pClassCts
         <*> pClass
         <*> pTyVarWithKind
         <*  symbol "where"
         <*> (pTmVar <&> (symbol "::" *> pPolyTy))

-- | Parse an instance declaration
pInstDecl :: PsM PsInsDecl
pInstDecl  =  indent $ (\ctx cls ty (m,tm) -> InsD ctx cls ty m tm)
          <$  symbol "instance"
          <*> pClassCts
          <*> pClass
          <*> pPrimTyPat
          <*  symbol "where"
          <*> (pTmVar <&> (symbol "=" *> pTerm))

-- | Parse a datatype declaration
pDataDecl :: PsM PsDataDecl
pDataDecl  =  indent $ DataD
          <$  symbol "data"
          <*> pTyCon
          <*> many (parens pTyVarWithKind)
          <*  symbol "="
          <*> sepBy1 (pDataCon <&> many pPrimTy) (symbol "|")

-- | Parse a datatype declaration
pFuncDecl :: PsM PsFuncDecl
pFuncDecl  =  indent $ FuncD
          <$> pTmVar
          <*  symbol "::"
          <*> pPolyTy
          <*  symbol "="
          <*> pTerm

-- * Parse all kinds of names
-- ------------------------------------------------------------------------------

-- | Parse a type variable
pTyVar :: PsM PsTyVar
pTyVar = mkPsTyVar <$> lowerIdent <?> "a type variable"

-- | Parse a term variable
pTmVar :: PsM PsTmVar
pTmVar = mkPsTmVar <$> lowerIdent <?> "a term variable"

-- | Parse a class name
pClass :: PsM PsClass
pClass = Class <$> upperIdent <?> "a class name"

-- | Parse a type constructor
pTyCon :: PsM PsTyCon
pTyCon = HsTC <$> upperIdent <?> "a type constructor"

-- | Parse a data constructor
pDataCon :: PsM PsDataCon
pDataCon = HsDC <$> upperIdent <?> "a data constructor"

-- * Parse types, type patterns, kinds and constraints
-- ------------------------------------------------------------------------------

-- | Parse a polytype
pPolyTy :: PsM PsPolyTy
pPolyTy =
  PPoly <$ symbol "forall" <*> parens pTyVarWithKind <* dot <*> pPolyTy <|>
  PQual <$> pQualTy

-- | Parse a qualified type -- Type Well-formedness says 1 constraint
pQualTy :: PsM PsQualTy
pQualTy =
  try (QQual <$> pClassCtr <* symbol "=>" <*> pQualTy) <|> QMono <$> pMonoTy

-- | Parse a primitive monotype
pPrimTy :: PsM PsMonoTy
pPrimTy = parens pMonoTy <|> TyCon <$> pTyCon <|> TyVar <$> pTyVar

-- | Parse a type pattern
pPrimTyPat :: PsM PsTyPat
pPrimTyPat = parens pMonoTyPat <|> HsTyConPat <$> pTyCon <|> HsTyVarPat <$> pTyVarWithKind

-- | Parse a monotype
pMonoTy :: PsM PsMonoTy
pMonoTy = chainr1 (chainl1 pPrimTy (pure TyApp))
                  (mkPsArrowTy <$ symbol "->")

-- | Parse a monotype pattern
pMonoTyPat :: PsM PsTyPat
pMonoTyPat = chainr1 (chainl1 pPrimTyPat (pure HsTyAppPat))
                  (mkPsArrowTyPat <$ symbol "->")

-- | Parse a kind
pKind :: PsM Kind
pKind = chainr1 (parens pKind <|> (KStar <$ symbol "*")) (KArr <$ symbol "->")
     <?> "a kind"

-- | Parse a class constraint
pClassCtr :: PsM PsClsCt
pClassCtr = ClsCt <$> pClass <*> pPrimTy

-- | Parse a class/instance context
pClassCts :: PsM PsClsCs
pClassCts  =  option [] . try
           $  (parens (commaSep pClassCtr)
          <|> (pure <$> pClassCtr))
          <*  symbol "=>"

-- | Parse a kind-annotated type variable (without the parentheses!!)
pTyVarWithKind :: PsM PsTyVarWithKind
pTyVarWithKind = liftA2 (:|) pTyVar (symbol "::" *> pKind)

-- * Parse terms
-- ------------------------------------------------------------------------------

-- | Parse a term (highest priority)
pPrimTerm :: PsM PsTerm
pPrimTerm  = asRegion p
  where p =  newTerm TmVar <*> lift pTmVar
         <|> newTerm TmCon <*> lift pDataCon
         <|> lift (parens pTerm)

-- | Parse a term (medium priority)
pAppTerm :: PsM PsTerm
pAppTerm = asRegion $ chainl1 (lift pPrimTerm <* splitRegion) (newTerm TmApp)

-- | Parse a term (lowest priority)
pTerm :: PsM PsTerm
pTerm = asRegion p
  where p =  lift pAppTerm
         <|> newTerm TmAbs
             <*  lift (symbol "\\")
             <*> lift pTmVar
             <*  lift dot
             <*> lift pTerm
         <|> newTerm TmLet
             <*  lift (symbol "let")
             <*> lift pTmVar
             <*  lift (symbol "=")
             <*> lift pTerm
             <*  lift (symbol "in")
             <*> lift pTerm
         <|> newTerm TmCase
             <*  lift (symbol "case")
             <*> lift pTerm
             <*  lift (symbol "of")
             <*> lift (some (indent pAlt))

-- | Parse a pattern
pPat :: PsM PsPat
pPat = HsPat <$> pDataCon <*> many pTmVar

-- | Parse a case alternative
pAlt :: PsM PsAlt
pAlt = HsAlt <$> pPat <* symbol "->" <*> pTerm
