{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module Lang.Dependent.AST where

import Numeric.Natural

import Control.Lens
import Control.Lens.Plated
import Data.Map (Map)
import Data.List ((\\))
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

instance VarContaining Term Name where
    freeVars t = fst <$> (freeVars t :: [(Name, Int)])
    allVars t = fst <$> (allVars t :: [(Name, Int)])

overName :: Name -> (a -> a) -> [(Name, a)] -> [(Name, a)]
overName n = over (mapped . filtered ((==n) . fst) . _2)

decrVar :: Name -> Term -> Term
decrVar = mapVarIndex pred

incrVar :: Name -> Term -> Term
incrVar = mapVarIndex succ

instance VarContaining Term (Name, Int) where
    freeVars (V n i)
      | i >= 0 = [(n, i)]
      | otherwise = []
    freeVars (Lam n ty t) = overName n succ $ freeVars (decrVar n t)
    freeVars (Pi n ty t) = overName n succ $ freeVars (decrVar n t)
    freeVars t = children t >>= freeVars
    allVars t = [(n, i) | V n i <- universe t]

instance Substitutable Name Term Term where
    substitute x rep (V y i)
      | x == y && i == 0 = rep
      | otherwise = V y i
    substitute x rep (Lam y ty t)
      | x == y = Lam y ty $ incrVar y $ substitute x rep' (decrVar y t)
      | otherwise = Lam y ty $ substitute x rep' t
        where rep' = incrVar x rep
    substitute x rep (Pi y ty t)
      | x == y = Pi y ty $ incrVar y $ substitute x rep' (decrVar y t)
      | otherwise = Pi y ty $ substitute x rep' t
        where rep' = incrVar x rep
    substitute x rep t = over plate (substitute x rep) t

type Env = Map (Name, Int) Term

mapVarIndex :: (Int -> Int) -> Name -> Term -> Term
mapVarIndex f x = transform go
    where go (V y i)
            | x == y = V y $ f i
            | otherwise = V y i
          go t = t

getFromEnv :: Env -> (Name, Int) -> Either String Term
getFromEnv env a = maybe (Left err) Right (M.lookup a env) where
    err = show a ++ " is not present in the type environment"

typeOf :: Term -> Either String Term
typeOf = undefined

nf :: Term -> Term
nf = undefined

whnf :: Term -> Term
whnf = undefined
