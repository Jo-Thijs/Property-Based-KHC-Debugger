{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE UndecidableInstances   #-}

-- | Class ContainsFreeTyVars: collect variables from objects

module Utils.FreeVars (ContainsFreeTmVars(..), ContainsFreeTyVars(..), subsetOf) where

import Data.List (nub, (\\))

-- | Collect the free term variables from objects
class ContainsFreeTmVars t tv | t -> tv where
  ftmvsOf :: t -> [tv]

instance (Eq tv, ContainsFreeTmVars a tv) => ContainsFreeTmVars [a] tv where
  ftmvsOf = nub . concatMap ftmvsOf

-- | Collect the free type variables from objects
class ContainsFreeTyVars t tv | t -> tv where
  ftyvsOf :: t -> [tv]

instance (Eq tv, ContainsFreeTyVars a tv) => ContainsFreeTyVars [a] tv where
  ftyvsOf = nub . concatMap ftyvsOf

instance (Eq tv, ContainsFreeTyVars a tv, ContainsFreeTyVars b tv) => ContainsFreeTyVars (a, b) tv where
  ftyvsOf (x,y) = nub (ftyvsOf x ++ ftyvsOf y)

-- | Check whether the first list is a subset of the second (treated as sets)
subsetOf :: Eq a => [a] -> [a] -> Bool
subsetOf xs ys = (xs \\ ys) == []

