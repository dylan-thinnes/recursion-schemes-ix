{-# LANGUAGE DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_HADDOCK hide #-}
-- Defines orphan instances for Recursive Type
module Data.IFunctor.TH.Internal where

-- template-haskell
import Language.Haskell.TH.Syntax

-- recursion-schemes
import Data.Functor.Foldable.TH (makeBaseFunctor)

-- Useful, non-indexed recursion schemes over types
-- Used in typeUpdateConcrete
makeBaseFunctor ''Type
