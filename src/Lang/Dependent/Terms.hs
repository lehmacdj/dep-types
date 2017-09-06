{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE OverloadedStrings #-}

module Lang.Dependent.Terms where

import Prelude (($))
import Lang.Dependent.AST

infixr 5 ~>

(~>) :: Term -> Term -> Term
(~>) = Pi "_"

infixl 5 @@

(@@) :: Term -> Term -> Term
(@@) = App

ty = TypeUniverse 0

const = Lam "a" ty $ Lam "b" ty $ Lam "x" "a" $ Lam "y" "b" "x"

const' = Pi "a" ty $ Pi "b" ty $ Pi "x" "a" $ Pi "y" "b" "a"


-- void

voidTy = Pi "a" ty "a"

absurd = Lam "a" ty $ Lam "x" voidTy $ "x" @@ "a"


-- unit

unitTy = Pi "a" ty $ "a" ~> "a"

unit = Lam "a" ty $ Lam "x" "a" "x"


-- booleans

boolTy = Pi "a" ty $ "a" ~> "a" ~> "a"

true = Lam "a" ty $ Lam "x" "a" $ Lam "y" "a" "x"

false = Lam "a" ty $ Lam "x" "a" $ Lam "y" "a" "y"

_if = Lam "a" ty $ Lam "b" boolTy $ Lam "x" "a" $ Lam "y" "a" $
  "b" @@ "a" @@ "x" @@ "y"


-- product types

prodTy = Lam "a" ty $ Lam "b" ty $ Pi "c" ty $ "a" ~> "b" ~> "c"

pair = Lam "a" ty $ Lam "b" ty $ Lam "x" "a" $ Lam "y" "b" $
  Lam "c" ty $ Lam "f" ("a" ~> "b" ~> "c") $ "f" @@ "x" @@ "y"

pair' = Pi "a" ty $ Pi "b" ty $ Pi "x" "a" $ Pi "y" "b" $
  Pi "c" ty $ Pi "f" ("a" ~> "b" ~> "c") "c"

-- pi1 = Λα.Λβ.λp:∀γ.(α→β→γ)→γ.(pα(λx:α.λy:β.x))
pi1 = Lam "a" ty $ Lam "b" ty $ Lam "p" (prodTy @@ "a" @@ "b") $
  "p" @@ "a" @@ Lam "x" "a" (Lam "y" "b" "x")

-- pi2 = Λα.Λβ.λp:∀γ.(α→β→γ)→γ.(pβ(λx:α.λy:β.y))
pi2 = Lam "a" ty $ Lam "b" ty $ Lam "p" (prodTy @@ "a" @@ "b") $
  "p" @@ "b" @@ Lam "x" "a" (Lam "y" "b" "y")


-- sum types

sumTy = Lam "a" ty $ Lam "b" ty $ Pi "c" ty $
  ("a" ~> "c") ~> ("b" ~> "c") ~> "c"

inl = Lam "a" ty $ Lam "b" ty $ Lam "x" "a" $
  Lam "c" ty $ Lam "f" ("a" ~> "c") $ Lam "g" ("b" ~> "c") $ "f" @@ "x"

inr = Lam "a" ty $ Lam "b" ty $ Lam "y" "a" $
  Lam "c" ty $ Lam "f" ("a" ~> "c") $ Lam "g" ("b" ~> "c") $ "g" @@ "y"

match = Lam "a" ty $ Lam "b" ty $ Lam "s" (sumTy @@ "a" @@ "b") $ Lam "c" ty $
  Lam "f" ("a" ~> "c") $ Lam "g" ("b" ~> "c") $ "s" @@ "c" @@ "f" @@ "g"

-- primitive recursion

natTy = Pi "a" ty $ Pi "f" ("a" ~> "a") $ Pi "x" "a" "a"

zero = Lam "a" ty $ Lam "f" ("a" ~> "a") $ Lam "x" "a" "x"

succ = Lam "n" natTy $ Lam "a" ty $ Lam "f" ("a" ~> "a") $ Lam "x" "a" $
  "f" @@ ("n" @@ "a" @@ "f" @@ "x")
