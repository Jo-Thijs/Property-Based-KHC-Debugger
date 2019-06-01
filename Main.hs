{-# LANGUAGE LambdaCase #-}

module Main (main, runTest) where

import Frontend.HsParser      (hsParse, hsParseTesters)
import Frontend.HsRenamer     (hsRename, hsRenameTesters)
import Frontend.HsTypeChecker (hsElaborate, hsElaborateTesters)
import Backend.FcTypeChecker  (fcTypeCheck)
import Backend.FcEvaluator    (fcEvaluate, fcEvaluateDebug, getChunkTable)
import Backend.Debugger       (genMetaDataTable, genAutoTable, pprShrinkTraceWithMeta)

import Utils.Unique  (newUniqueSupply)
import Utils.PrettyPrint
import Utils.Trace   (dumpTrace)
import Utils.TermId  (initialTermId, getNewTermId, getTermTable)

import System.Environment (getArgs)

import Data.Char (toUpper)

import Control.Monad.State
import Control.Monad.Trans.Maybe

import qualified Data.Map as M

main :: IO ()
main = getArgs >>= \case
  [filename] -> runEval filename
  [progFilename,propFilename] -> runDebug progFilename propFilename
  _          -> putStrLn $ "Usage:\nTo compile and evaluate:\n\tkhc <source_code_filename>\n"
                        ++ "To compile and debug:\n\tkhc <source_code_filename> <properties_filename>"

{-
main :: IO ()
main = getArgs >>= \case
  [filename] -> runTest filename
  _other     -> putStrLn "Usage: ghc <filename>"
-}
-- | Run a single testfile
runTest :: FilePath -> IO ()
runTest file = do
  -- Parsing
  hsParse file >>= \case
    Left err                 -> throwMainError "parser" err
    Right (ps_pgm, srcTable) -> do
      -- Renaming
      us0 <- newUniqueSupply 'u'
      case hsRename us0 ps_pgm of
        (Left err, _) -> throwMainError "renamer" err
        (Right (((rn_pgm, _rn_ctx), us1), rn_env), _) ->
          -- Elaborating and typechecking haskell
          case hsElaborate rn_env us1 initialTermId rn_pgm of
            (Left err, _) -> throwMainError "typechecker" err
            (Right (((((fc_pgm, tc_ty, theory, tyTable, _), envs), genTab), us2), _tc_env), _) -> do
              -- Typechecking FC
               case fcTypeCheck envs us2 fc_pgm of
                (Left err, _) -> throwMainError "System F typechecker" err
                (Right ((fc_ty, us3), _fc_env), _trace) -> do
                  -- Evaluating
                  let (((fc_evaluated, _genTab), store), _us4) = fcEvaluate (getNewTermId genTab) us3 fc_pgm
                  -- Output
                  putStrLn "---------------------------- Elaborated Program ---------------------------"
                  putStrLn $ renderWithColor $ ppr fc_pgm
                  {-putStrLn "------------------------------- Program Type ------------------------------"
                  putStrLn $ renderWithColor $ ppr tc_ty
                  putStrLn "------------------------------ Program Theory -----------------------------"
                  putStrLn $ renderWithColor $ ppr theory
                  putStrLn "-------------------------- System F Program Type --------------------------"
                  putStrLn $ renderWithColor $ ppr fc_ty
                  putStrLn "---------------------------- Evaluation Result ----------------------------"
                  putStrLn $ renderWithColor $ ppr fc_evaluated
                  putStrLn "------------------------------- Chunk Store -------------------------------"
                  putStrLn $ renderWithColor $ ppr store-}

-- | Evaluate a single testfile
runEval :: FilePath -> IO ()
runEval file = do
  -- Parsing
  hsParse file >>= \case
    Left err                 -> throwMainError "parser" err
    Right (ps_pgm, srcTable) -> do
      -- Renaming
      us0 <- newUniqueSupply 'u'
      case hsRename us0 ps_pgm of
        (Left err, _) -> throwMainError "renamer" err
        (Right (((rn_pgm, _rn_ctx), us1), rn_env), _) ->
          -- Elaborating and typechecking haskell
          case hsElaborate rn_env us1 initialTermId rn_pgm of
            (Left err, _) -> throwMainError "typechecker" err
            (Right (((((fc_pgm, tc_ty, theory, tyTable, _), envs), genTab), us2), _tc_env), _) -> do
              -- Typechecking FC
               case fcTypeCheck envs us2 fc_pgm of
                (Left err, _) -> throwMainError "System F typechecker" err
                (Right ((fc_ty, us3), _fc_env), _trace) -> do
                  -- Evaluating
                  let (((fc_evaluated, _genTab), store), _us4) = fcEvaluate (getNewTermId genTab) us3 fc_pgm
                  -- Output
                  putStrLn "---------------------------- Evaluation Result ----------------------------"
                  putStrLn $ renderWithColor $ ppr fc_evaluated
                  --putStrLn $ show $ M.size $ getChunkTable store

throwMainError phase e
  | label <- colorDoc red (text phase <+> text "failure")
  , msg   <- brackets label <+> colorDoc red (text e)
  = putStrLn (renderWithColor msg)

runDebug :: FilePath -> FilePath -> IO ()
runDebug mainFile testerFiles = do
  -- Parsing
  hsParse mainFile >>= \case
    Left err -> throwMainError "main parser" err
    Right (ps_pgm, srcTable) -> do
      hsParseTesters testerFiles >>= \case
        Left err -> throwMainError "prop parser" err
        Right (ps_testers, srcTable') -> do
          -- Renaming
          us0 <- newUniqueSupply 'u'
          case hsRename us0 ps_pgm of
            (Left err, _) -> throwMainError "main renamer" err
            (Right (((rn_pgm, rn_ctx), us1), rn_env), _) ->
              case hsRenameTesters us1 rn_ctx rn_env ps_testers of
                (Left err, _) -> throwMainError "prop renamer" err
                (Right (rn_testers, us2), _) ->
                  -- Elaborating & Typechecking
                  case hsElaborate rn_env us2 initialTermId rn_pgm of
                    (Left err, _) -> throwMainError "main typechecker" err
                    ( Right (((((fc_pgm, tc_ty, theory, tyTable, tc_ctx), envs), genTab), us3), tc_env), _ ) ->
                      case hsElaborateTesters theory tc_ctx tc_env us3 (getNewTermId genTab) rn_testers of
                        (Left err, _) -> throwMainError "prop typechecker" err
                        (Right ((((testers, tests), _), us4), _), _) -> do
                          -- Evaluating
                          let autoTable = genAutoTable rn_pgm
                          let metaTable = genMetaDataTable autoTable tyTable srcTable
                          let evaluator = fcEvaluateDebug metaTable
                                                          (getTermTable genTab)
                                                          tests
                                                          (getNewTermId genTab)
                                                          us4
                                                          fc_pgm
                          -- Output
                          {-
                          putStrLn "---------------------------- Elaborated Program ---------------------------"
                          putStrLn $ renderWithColor $ ppr fc_pgm
                          putStrLn "---------------------------- Elaborated Testers ---------------------------"
                          putStrLn $ renderWithColor $ ppr testers
                          -}
                          evalResult <- runMaybeT
                                      $ evaluator
                                      $ \shrinkTrace cont -> do
                              lift $ lift $ putStrLn "------------------------------ Debug Result -------------------------------"
                              lift $ lift $ putStrLn $ renderWithColor $ pprShrinkTraceWithMeta srcTable srcTable' shrinkTrace
                              flag <- lift $ lift getFlag
                              if flag
                              then cont
                              else lift mzero
                          case evalResult of
                            Just (((fc_evaluated, _), store), _) -> do
                              putStrLn "---------------------------- Evaluation Result ----------------------------"
                              putStrLn $ renderWithColor $ ppr fc_evaluated
                            Nothing                              -> return ()
  where
    getFlag = do
      putStrLn "Enter Y to continue debugging or N to exit."
      c <- getLine
      case map toUpper c of
        'Y':_ -> return True
        'N':_ -> return False
        _   -> getFlag
