{-# LANGUAGE ScopedTypeVariables #-}

import Lang.Dependent.AST
import Lang.Common.Variable

import Test.Tasty
import Test.Tasty.QuickCheck

import Control.Applicative (liftA3, liftA2)

main :: IO ()
main = defaultMain properties

properties :: TestTree
properties = testGroup "QuickCheck property tests"
    [testProperty "substitution" $
        \(x :: Name) (t :: Term) ->
            x `notElem` freeVars t ==> substitute x t t == t
    ]

instance Arbitrary Term where
    arbitrary = sized aterm

aterm :: Int -> Gen Term
aterm 0 = oneof
    [ V <$> arbitrary <*> (mod <$> arbitrary <*> pure 3)
    , pure Unit , pure UnitTy
    , pure T, pure F, pure Bool
    , TypeUniverse <$> arbitrary ]

aterm n = oneof
    [ liftA3 Lam arbitrary t t
    , liftA3 Pi arbitrary t t
    , liftA3 IF t t t
    , liftA2 App t t
    ]
        where t = aterm (n `div` 2)
