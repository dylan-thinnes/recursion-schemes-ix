module THSpec.Internal where

import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax

typeExists :: String -> Q Exp
typeExists name = lift . (/= Nothing) =<< lookupTypeName name

valueExists :: String -> Q Exp
valueExists name = lift . (/= Nothing) =<< lookupValueName name
