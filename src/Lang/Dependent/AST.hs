{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE DeriveFunctor #-}

module Lang.Dependent.AST where

import Numeric.Natural

import Control.Monad.Reader

import Control.Lens
import Control.Lens.Plated
import Data.Data hiding (typeOf)
import Data.String (fromString, IsString)

import Data.Semigroup

import Lang.Common.Variable
import Lang.Common.Unique

import Control.Arrow

import Data.List (sortBy)
import Data.Function (on)

import Control.Applicative

newtype Name = N { name :: String }
  deriving (Eq, Data, Typeable, Uniquable)

instance Show Name where
  show x = "(N " ++ name x ++ ")"

instance IsString Name where
  fromString = N

data Term = V Name Int
          | Lam Name Term Term
          | Pi Name Term Term
          | App Term Term
          | TypeUniverse Natural
          deriving (Eq, Show, Data, Typeable)

-- newtype wrapper for alpha equality
newtype Alpha = Alpha Term
  deriving (Show, Data, Typeable)

instance Eq Alpha where
  (Alpha a) == (Alpha b) = alphaNormal a == alphaNormal b

-- newtype wrapper for beta equality
newtype Beta = Beta Term
  deriving (Show, Data, Typeable)

instance Eq Beta where
  (Beta a) == (Beta b) = case (nf a, nf b) of
    (Right a, Right b) -> Alpha a == Alpha b
    _ -> False

alphaNormal :: Term -> Term
alphaNormal t = composed subs rebound
  where uniqueSubs =
          mapM (\v -> (fresh :: Unique Name Name) >>= pure . mkSubst v) vars
        sequenced :: Unique Name ([Term -> Term], Term)
        sequenced = do
          u' <- uniqueSubs
          r' <- rebindBound t
          pure (u', r')
        (subs, rebound) = runUnique sequenced []
        composed :: [a -> a] -> a -> a
        composed = foldl (.) id
        vars :: [(Name, Int)]
        vars = freeVars t
        mkSubst :: (Name, Int) -> Name -> Term -> Term
        mkSubst v f = substitute v (V f 0)

instance Plated Term

instance IsString Term where
  fromString s = V (fromString s) 0

instance VarContaining Term Name where
    freeVars t = fst <$> (freeVars t :: [(Name, Int)])
    allVars t = fst <$> (allVars t :: [(Name, Int)])

rebindBound :: Term -> Unique Name Term
rebindBound (Lam x x' e) = do
  f <- fresh
  f' <- rebindBound (subst f x')
  e' <- rebindBound (subst f e)
  pure (Lam f f' e')
    where subst f = substitute ((x, 0) :: (Name, Int)) (V f 0)
rebindBound (Pi x x' e) = do
  f <- fresh
  f' <- rebindBound (subst f x')
  e' <- rebindBound (subst f e)
  pure (Pi f f' e')
    where subst f = substitute ((x, 0) :: (Name, Int)) (V f 0)
rebindBound t = mapMOf plate rebindBound t

overName :: Name -> (a -> a) -> [(Name, a)] -> [(Name, a)]
overName n = over (mapped . filtered ((==n) . fst) . _2)

mapVarIndex :: (Int -> Int) -> Name -> Term -> Term
mapVarIndex f x = transform go
    where go (V y i)
            | x == y = V y $ f i
            | otherwise = V y i
          go t = t

decrVar :: Name -> Term -> Term
decrVar = mapVarIndex pred

incrVar :: Name -> Term -> Term
incrVar = mapVarIndex succ

incrFree :: Name -> Term -> Term
incrFree x t = composed substs t
  where
    composed = foldl (.) id
    substs = zipWith substitute ordered incremented
    incremented = map (\(x, i) -> V x (i + 1)) ordered
    ordered = sortBy (compare `on` snd) vars
    vars = filter ((==x) . fst) (freeVars t :: [(Name, Int)])

instance VarContaining Term (Name, Int) where
    allVars (V n i) = [(n, i)]
    allVars (Lam n ty t) = allVars (decrVar n t)
    allVars (Pi n ty t) = allVars (decrVar n t)
    allVars t = children t >>= allVars
    freeVars = filter ((>= 0) . snd) . allVars

instance Substitutable (Name, Int) Term Term where
    substitute (x, i) rep (V y j)
      | x == y && i == j = rep
      | otherwise = V y j
    substitute (x, i) rep (Lam y ty t)
      | x == y = Lam y ty $ substitute (x, i + 1) rep' t
      | otherwise = Lam y ty $ substitute (x, i) rep' t
        where rep' = incrFree y rep
    substitute (x, i) rep (Pi y ty t)
      | x == y = Pi y ty $ substitute (x, i + 1) rep' t
      | otherwise = Pi y ty $ substitute (x, i) rep' t
        where rep' = incrFree y rep
    substitute x rep t = over plate (substitute x rep) t

instance Substitutable Name Term Term where
  substitute x = substitute (x , 0 :: Int)

type Env = [(Name, Term)]

-- failable applicative with an environent of type `g`
data TyCheck g e a = Failed e | Checked g a
  deriving (Functor)

instance (Monoid e, Monoid g) => Applicative (TyCheck g e) where
  pure = Checked mempty
  Checked g f <*> Checked h x = Checked (g `mappend` h) (f x)
  Failed e1 <*> Failed e2 = Failed (e1 `mappend` e2)
  Failed e <*> Checked g x = Failed e
  Checked g f <*> Failed e = Failed e

instance (Monoid e, Monoid g) => Monad (TyCheck g e) where
  return = pure
  Checked g x >>= f = case f x of
    Checked h x' -> Checked (g `mappend` h) x'
    Failed e -> Failed e
  Failed e >>= f = Failed e

data TyErr = NotInEnv Name
           | NotEqual Term Term
           | MustBeFunction Term
           | MustBeTypeUniverse Term

type TyChecking = TyCheck Env [TyErr]

getFromEnvSkip :: Env -> Name -> Int -> Either String Term
getFromEnvSkip [] x 0 = Left $ show x ++ " is not present in the type environment"
getFromEnvSkip [] x n = Left $ "Missing " ++ show n ++ " bindings for " ++ show x
getFromEnvSkip ((x, t):bs) y i
  | x == y && i == 0 = Right t
  | x == y = getFromEnvSkip bs y (i - 1)
  | otherwise = getFromEnvSkip bs y i

getFromEnv :: Env -> Name -> Either String Term
getFromEnv env x = maybe (Left err) Right (lookup x env) where
    err = show x ++ " is not present in the type environment"

extendedWith :: (Name, Term) -> Env -> Env
extendedWith = (:)

-- assert that two terms are equal, for example: during type checking
assertEq :: Term -> Term -> Either String ()
assertEq s t
  | Beta s == Beta t = pure ()
  | otherwise = Left $ "term " ++ pretty s ++ " is not equal to " ++ pretty t

-- I don't think I make any effort to resove variables based on the environment
-- or ensure that they are well formed; this needs to change
typeOf :: Env -> Term -> Either String Term
typeOf g (TypeUniverse n) = Right $ TypeUniverse $ n + 1
typeOf g (App s t) = do
    s' <- typeOf g s
    case s' of
        Pi x x' r' -> do
            t' <- typeOf g t
            assertEq x' t'
            pure $ substitute x t r'
        _ -> Left $ "type of " ++ pretty s ++ " was "
                 ++ pretty s' ++ " but was expected to be a function type"
typeOf g (Pi x x' r') = do
    nfx' <- nf x'
    r'' <- typeOf (extendedWith (x, nfx') g) r'
    x'' <- typeOf g x'
    case (x'', r'') of
        -- this may not be particualarly sound. See this for more details:
        -- https://cs.stackexchange.com/questions/13285/universes-in-dependent-type-theory
        (TypeUniverse i, TypeUniverse j) -> Right $ TypeUniverse $ max i j
        _ -> Left $ "function argument types and return types must be"
                 ++ " types and cannot be values"
typeOf g (Lam x x' e) = do
    x'' <- nf x'
    e' <- typeOf (extendedWith (x, x'') g) e
    Right $ Pi x x' e'
typeOf g (V x n) = getFromEnvSkip g x n

typeCheck :: Term -> Either String Term
typeCheck = typeOf []

nf :: Term -> Either String Term
nf (TypeUniverse n) = pure $ TypeUniverse n
nf (App f a) = do
    f' <- whnf f
    case f' of
        Lam x x' e -> nf $ substitute x a e
        V x i -> pure $ App f a
        _ -> Left $ "invalid function application of " ++ pretty f
nf (Lam x x' e) = do
    x'' <- nf x'
    e' <- nf e
    pure $ Lam x x'' e'
nf (Pi x x' e) = do
    x'' <- nf x'
    e' <- nf e
    pure $ Pi x x'' e'
nf (V x i) = pure $ V x i

whnf :: Term -> Either String Term
whnf (App f a) = do
    f' <- whnf f
    case f' of
        Lam x x' e -> whnf $ substitute x a e
        V x i -> pure $ App f a
        _ -> Left $ "invalid function application of " ++ pretty f
whnf t = pure t

pretty :: Term -> String
pretty (TypeUniverse n)
  | n == 0 = "T"
  | otherwise = "T_" ++ show n
pretty (App e1 e2) = "(" ++ pretty e1 ++ " " ++ pretty e2 ++ ")"
pretty (Lam x x' e) = "(λ" ++ name x ++ ":" ++ pretty x' ++ "." ++ pretty e ++ ")"
pretty (Pi x x' e)
  | name x == "_" = "(" ++ pretty x' ++ " -> " ++ pretty e ++ ")"
  | otherwise = "(∀" ++ name x ++ ":" ++ pretty x' ++ "." ++ pretty e ++ ")"
pretty (V x i)
  | i == 0 = name x
  | otherwise = name x ++ "_" ++ show i

class PP a where
  pp :: a -> IO ()
instance PP (Either String Term) where
  pp (Right t) = putStrLn $ pretty t
  pp (Left s) = putStrLn s
instance PP Term where
  pp t = putStrLn $ pretty t
