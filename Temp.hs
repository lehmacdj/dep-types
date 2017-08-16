{-# LANGUAGE DeriveFunctor, DeriveTraversable, DeriveFoldable #-}
-- {-# LANGUAGE TemplateHaskell #-}
module Temp where

import Numeric.Natural

import Bound

import Control.Monad (ap)

import Data.Eq.Deriving
import Text.Show.Deriving

data Term a = V a
            | Lam (Scope () Term a) (Term a)
            | Pi (Scope () Term a) (Term a)
            | Unit
            | UnitTy
            | TypeUniverse Natural
            deriving (Functor, Foldable, Traversable)

instance Applicative Term where
    pure = V
    (<*>) = ap

instance Monad Term where
    return = V
    V a >>= f = f a
    Lam s ty >>= f = Lam (s >>>= f) (ty >>= f)
    Pi s ty >>= f = Pi (s >>>= f) (ty >>= f)
    Unit >>= f = Unit
    UnitTy >>= f = UnitTy
    TypeUniverse n >>= f = TypeUniverse n
