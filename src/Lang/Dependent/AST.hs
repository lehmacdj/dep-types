{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module Lang.Dependent.AST where

import Numeric.Natural

import Control.Monad.Reader

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

type Env = Map Name Term

mapVarIndex :: (Int -> Int) -> Name -> Term -> Term
mapVarIndex f x = transform go
    where go (V y i)
            | x == y = V y $ f i
            | otherwise = V y i
          go t = t

getFromEnv :: Env -> Name -> Either String Term
getFromEnv env x = maybe (Left err) Right (M.lookup x env) where
    err = show x ++ " is not present in the type environment"

extendedWith :: (Name, Term) -> Env -> Env
extendedWith (k, v) = M.insert k v

-- assert that two terms are equal, for example: during type checking
assertEq :: Term -> Term -> Either String ()
assertEq s t
  | s == t = pure ()
  | otherwise = Left $ "term " ++ show s ++ " is not equal to " ++ show t

-- (f : (πx:Type.x)) Bool

substitute' :: Name -> Term -> Term -> Term
substitute' = ((nf.).) . substitute

typeOf' :: Env -> Term -> Either String Term
typeOf' = (fmap nf .) .  typeOf

typeOf :: Env -> Term -> Either String Term
typeOf g Unit = Right UnitTy
typeOf g T = Right Bool
typeOf g F = Right Bool
typeOf g Void = Right $ TypeUniverse 0
typeOf g UnitTy = Right $ TypeUniverse 0
typeOf g Bool = Right $ TypeUniverse 0
typeOf g (TypeUniverse n) = Right $ TypeUniverse $ n + 1
typeOf g (IF p t e) = do
    p' <- typeOf' g p
    t' <- typeOf' g t
    e' <- typeOf' g e
    assertEq Bool p'
    assertEq t' e'
    pure t'
typeOf g (App s t) = do
    s' <- typeOf' g s
    t' <- typeOf' g t
    case s' of
        Pi x x' r' -> do
            assertEq x' t'
            Right $ substitute' x t r'
        _ -> Left $ "type of " ++ show t ++ " was "
                 ++ show t' ++ " but was expected to be a function type"
typeOf g (Pi x x' e) = do
    e' <- typeOf' (extendedWith (x, x') g) e
    case (x', e') of
        -- this may not be particualarly sound. See this for more details:
        -- https://cs.stackexchange.com/questions/13285/universes-in-dependent-type-theory
        (TypeUniverse i, TypeUniverse j) -> Right $ TypeUniverse $ max i j
        _ -> Left $ "function arguments and return types must be types"
                 ++ "and cannot be values"
typeOf g (Lam x x' e) = do
    e' <- typeOf' (extendedWith (x, x') g) e
    Right $ Pi x x' e'
typeOf g (V x 0) = getFromEnv g x

nf :: Term -> Term
nf Unit = Unit
nf T = T
nf F = F
nf Void = Void
nf UnitTy = UnitTy
nf Bool = Bool
nf (TypeUniverse n) = TypeUniverse n
nf (IF p t e) = case nf p of
    T -> nf t
    F -> nf e
nf (App f a) = case whnf f of
    Lam x x' e -> nf $ substitute x a e
    _ -> error "invalid function application"
nf (Lam x x' e) = Lam x (nf x') (nf e)
nf (Pi x x' e) = Pi x (nf x') (nf e)
nf (V x i) = V x i

whnf :: Term -> Term
whnf (App f a) = case whnf f of
    Lam x x' e -> whnf $ substitute x a e
    _ -> error "invalid function application"
whnf t = t
