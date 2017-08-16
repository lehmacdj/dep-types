{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module Lang.Dependent.AST where

import Numeric.Natural

import Control.Lens.Plated
import Data.Map (Map)
import qualified Data.Map as M
import Data.Data hiding (typeOf)

import Data.Semigroup

import Lang.Common.Variable

import Control.Applicative

type Name = String

data Term = V Name Int
          | Lam Name Term Term
          | Pi Name Term Term
          | App Term Term
          | Void
          | Unit | UnitTy
          | T | F | Bool | IF Term Term Term
          | TypeUniverse Natural
          deriving (Eq, Show, Read, Data, Typeable)

instance Plated Term

instance VarContaining Term (Name, Int) where
    freeVars = undefined
    allVars = undefined

instance Substitutable (Name, Int) Term Term where
    substitute = undefined

type Env = Map (Name, Int) Term

mapVarIndex :: (Int -> Int) -> Name -> Term -> Term
mapVarIndex f x (V y i)
  | x == y = V y (f i)
  | otherwise = V y i
mapVarIndex f x t = transform (mapVarIndex f x) t

getFromEnv :: Env -> (Name, Int) -> Either String Term
getFromEnv env a = maybe (Left err) Right (M.lookup a env) where
    err = show a ++ " is not present in the environment"

typeOf :: Term -> Either String Term
typeOf = undefined

nf :: Term -> Term
nf = undefined

whnf :: Term -> Term
whnf = undefined
