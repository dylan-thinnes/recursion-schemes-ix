{-# LANGUAGE TemplateHaskell, GADTs, KindSignatures, DataKinds #-}
module THSpec (main, spec) where

import           Data.IFunctor.TH
import           Test.Hspec
import           Test.QuickCheck
import           THSpec.Internal

data Dec = FunD String [([Pat], Exp)]
data Exp = App Exp Exp | Abs Pat Exp | VarE String | Case [Branch]
data Pat = Wildcard | VarP String | ConP String [Pat]
data Branch = Branch Pat Exp [Dec]

deriveMutualGADT ''Exp

indexExists   = $(typeExists "ExpIx")
functorExists = $(typeExists "ExpMF")
synonymExists = $(typeExists "ExpM")

decIExists = $(valueExists "DecI")
expIExists = $(valueExists "ExpI")
patIExists = $(valueExists "PatI")
branchIExists = $(valueExists "BranchI")

main :: IO ()
main = hspec spec

spec :: Spec
spec =
    describe "template haskell deriveMutualGADT" $ do
        it "builds index"   $ True `shouldBe` indexExists
        it "builds functor" $ True `shouldBe` functorExists
        it "builds synonym" $ True `shouldBe` synonymExists
        it "builds all four indices" $
            replicate 4 True
            `shouldBe`
            [decIExists, expIExists, patIExists, branchIExists]
