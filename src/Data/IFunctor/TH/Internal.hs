{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

{-# OPTIONS_HADDOCK hide #-}

-- Defines orphan instances for Recursive Type
module Data.IFunctor.TH.Internal where

import           Data.Functor.Foldable.TH   (makeBaseFunctor)
import           Language.Haskell.TH.Syntax

-- Useful, non-indexed recursion schemes over types
-- Used in typeUpdateConcrete
makeBaseFunctor ''Type
