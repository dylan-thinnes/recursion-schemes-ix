{-# LANGUAGE LambdaCase #-}

module Data.IFunctor.TH
    ( deriveMutualGADT
    ) where

import           Control.Monad              ((>=>))
import           Data.Functor.Foldable (cata, embed)
import           Data.IFunctor.TH.Internal
import qualified Data.Map                   as M
import           Data.Maybe                 (fromJust)
import qualified Data.Set                   as S
import qualified Language.Haskell.TH        as TH
import qualified Language.Haskell.TH.Syntax as TH

{-|
  Given the name of a mutually-recursive datatype, derive an index and an
  indexed functor as a GADT.

  For example, given:

  @
  data Exp = App Exp Exp | Abs Pat Exp | VarE String
  data Pat = Wildcard | VarP String | ConP String [Pat]
  @

  We could invoke @deriveMutualGADT ''Exp@ to produce the following:

  @
  data ExpIx = ExpI | PatI
  data ExpMF (f :: ExpIx -> *) (ix :: ExpIx) where
    AppMF      :: f ExpI -> f ExpI   -> MF f ExpI
    AbsMF      :: f PatI -> f ExpI   -> MF f ExpI
    VarEMF     :: String             -> MF f ExpI
    WildcardMF ::                       MF f PatI
    VarPMF     :: String             -> MF f PatI
    ConPMF     :: String -> [f PatI] -> MF f PatI
  @
-}
deriveMutualGADT :: TH.Name -> TH.Q [TH.Dec]
deriveMutualGADT topLevel = do
    -- Find all constructors that are involved in a cycle
    recursiveConsNames <- S.toList <$> findRecursiveConstructors topLevel

    -- Derive tag name, tag constructors' names
    tagName <- suffixify "Ix" topLevel
    tagConsNames <- mapM (suffixify "I") recursiveConsNames
    let lookupTagConsByCons cons = lookup cons $ zip recursiveConsNames tagConsNames

    -- Tag declaration
    let tagConss = flip TH.NormalC [] <$> tagConsNames
    let tagDecl = TH.DataD [] tagName [] Nothing tagConss []

    -- Name of Mutually-recursive base Functor, GADT, algebra f, index ix
    gadtName <- suffixify "MF" topLevel
    gadtF <- TH.newName "f"
    let gadtFKind = TH.KindedTV gadtF (TH.ArrowT `TH.AppT` TH.ConT tagName `TH.AppT` TH.StarT)
    gadtIx <- TH.newName "ix"
    let gadtIxKind = TH.KindedTV gadtIx (TH.ConT tagName)

    -- Given a recursiveConsName, derive the constructors for a GADT
    let recConsNameToGadtConss recursiveConsName = do
            -- Pull out the datatype's constuctors & the tag constructor
            TH.TyConI (TH.DataD _ _ _ _ conss _) <- TH.reify recursiveConsName
            let tagCons = fromJust $ lookupTagConsByCons recursiveConsName

            -- Final type is `<name> <f> <tag>`
            let finalType = TH.ConT gadtName `TH.AppT` TH.VarT gadtF `TH.AppT` TH.PromotedT tagCons

            -- Given a concrete type, if it matches any of the recursive
            -- datatypes, replace it with `f <tag>`
            let updateMatchingType =
                    typeUpdateConcrete $ \name ->
                        case lookupTagConsByCons name of
                          Just tag -> TH.AppT (TH.VarT gadtF) (TH.PromotedT tag)
                          Nothing  -> TH.ConT name

            -- Update all constructors' types using updateMatchingType
            -- Append MF to all constructor names
            -- Convert base constructors to GADT constructors
            let updatedTypes = map (updateTypes updateMatchingType) conss
            mfAppended <- mapM updateToMFName updatedTypes
            let gadtConss = conToGadt finalType <$> mfAppended

            pure gadtConss

    -- Derive GADT constructors for all recursive data types, concat
    allGadtConss <- concat <$> mapM recConsNameToGadtConss recursiveConsNames

    -- Final GADT w/ name, f, ix, and derived constructors
    let gadt = TH.DataD [] gadtName [gadtFKind, gadtIxKind] Nothing allGadtConss []

    pure [gadt, tagDecl]

-- Name grouping & name manipulation
type Names = S.Set TH.Name
type NameMap = M.Map TH.Name Names

nameToStr :: TH.Name -> String
nameToStr (TH.Name (TH.OccName str) _) = str

suffixify :: String -> TH.Name -> TH.Q TH.Name
suffixify suff name = TH.newName (nameToStr name ++ suff)

-- Convert normal constructors to GADT equivalents, w/ a custom final type
conToGadt :: TH.Type -> TH.Con -> TH.Con
conToGadt finalType con =
    case con of
        TH.NormalC name bangTypes -> TH.GadtC [name] bangTypes finalType
        TH.RecC name varBangTypes -> TH.RecGadtC [name] varBangTypes finalType
        TH.InfixC _ _ _           ->
            error $ "Constructor '" ++ show con ++ "' to turn to GADT is Infix"
        TH.ForallC _ _ _          ->
            error $ "Constructor '" ++ show con ++ "' to turn to GADT is forall quanitified"
        _                         ->
            error $ "Constructor '" ++ show con ++ "' to turn to GADT is already a GADT"

-- Update data constructors names to have MF suffix
updateToMFName :: TH.Con -> TH.Q TH.Con
updateToMFName =
    \case
        TH.NormalC name bangTypes            -> suffixify "MF" name >>= \name -> pure $ TH.NormalC name bangTypes
        TH.RecC name varBangTypes            -> suffixify "MF" name >>= \name -> pure $ TH.RecC name varBangTypes
        TH.InfixC lType name rType           -> suffixify "MF" name >>= \name -> pure $ TH.InfixC lType name rType
        TH.ForallC bndrs cxt con             -> TH.ForallC bndrs cxt <$> updateToMFName con
        TH.GadtC names bangTypes type_       -> mapM (suffixify "MF") names >>= \names -> pure $ TH.GadtC names bangTypes type_
        TH.RecGadtC names varBangTypes type_ -> mapM (suffixify "MF") names >>= \names -> pure $ TH.RecGadtC names varBangTypes type_

-- Update types using lenses
updateTypes :: (TH.Type -> TH.Type) -> TH.Con -> TH.Con
updateTypes f =
    let updateBangType (bang, type_) = (bang, f type_)
        updateVarBangType (var, bang, type_) = (var, bang, f type_)
        updateBangTypes = map updateBangType
        updateVarBangTypes = map updateVarBangType
    in
    \case
        TH.NormalC name bangTypes            -> TH.NormalC name $ updateBangTypes bangTypes
        TH.RecC name varBangTypes            -> TH.RecC name $ updateVarBangTypes varBangTypes
        TH.InfixC lType name rType           -> TH.InfixC (updateBangType lType) name (updateBangType rType)
        TH.ForallC bndrs cxt con             -> TH.ForallC bndrs cxt $ updateTypes f con
        TH.GadtC names bangTypes type_       -> TH.GadtC names (updateBangTypes bangTypes) (f type_)
        TH.RecGadtC names varBangTypes type_ -> TH.RecGadtC names (updateVarBangTypes varBangTypes) (f type_)

-- Update concrete types to others using a function f
typeUpdateConcrete :: (TH.Name -> TH.Type) -> TH.Type -> TH.Type
typeUpdateConcrete f = cata alg
    where
        alg (ConTF name) = f name
        alg x = embed x

-- Find recursive constructors, given the name of the "starting" type
findRecursiveConstructors :: TH.Name -> TH.Q Names
findRecursiveConstructors name = S.fromList . M.keys . prune <$> nameDeps name
    where
    prune :: NameMap -> NameMap
    prune names =
        let nonterminalNames = M.filter (not . S.null) names
            nonterminalParents = M.map (S.filter (flip M.member nonterminalNames)) nonterminalNames
        in
        if nonterminalParents == names
           then names
           else prune nonterminalParents

-- Find all concrete names used a group of mutually-recursive datatypes, index as map
nameDeps :: TH.Name -> TH.Q NameMap
nameDeps name = go M.empty [name]
    where
    go found frontier =
        if null frontier
        then pure found
        else do
            newNamePairs <- zip frontier <$> mapM dataConcreteNames frontier
            let unseenNamePairs = filter (not . flip M.member found . fst) newNamePairs
            let newFound = foldr (\(parent, children) found -> M.insert parent children found) found unseenNamePairs
            let newFrontier = S.toList $ foldr S.union S.empty $ map snd unseenNamePairs
            go newFound newFrontier

-- Get all concrete names used in the constructors for a datatype by name
dataConcreteNames :: TH.Name -> TH.Q Names
dataConcreteNames name
  = S.fromList
  . concatMap (conTypes >=> typeConcreteNames)
  <$> dataConstructors name

-- Get all constructors for a datatype by name
dataConstructors :: TH.Name -> TH.Q [TH.Con]
dataConstructors parentName = do
    infoMaybeCon <- TH.reify parentName
    pure $ case infoMaybeCon of
              TH.TyConI (TH.DataD _ _ _ _ conss _) -> conss
              _ -> []

-- Get all types used in a constructor
conTypes :: TH.Con -> [TH.Type]
conTypes =
    \case
      TH.NormalC _ bangTypes -> bangTypeToType <$> bangTypes
      TH.RecC _ varBangTypes -> varBangTypeToType <$> varBangTypes
      TH.InfixC lBangType _ rBangType -> bangTypeToType <$> [lBangType, rBangType]
      TH.ForallC _ _ subcon -> conTypes subcon
      TH.GadtC _ bangTypes subtype -> subtype : map bangTypeToType bangTypes
      TH.RecGadtC _ varBangTypes subtype -> subtype : map varBangTypeToType varBangTypes
  where
    bangTypeToType (_, type_) = type_
    varBangTypeToType (_, _, type_) = type_

-- Get all concrete type names in a type
typeConcreteNames :: TH.Type -> [TH.Name]
typeConcreteNames =
    \case
      TH.ForallT _ _ subtype -> typeConcreteNames subtype
      TH.AppT lType rType -> [lType, rType] >>= typeConcreteNames
      TH.SigT subtype _ -> typeConcreteNames subtype
      TH.VarT _ -> []
      TH.ConT name -> [name]
      TH.PromotedT _ -> []
      TH.InfixT lType name rType -> [name] ++ ([lType, rType] >>= typeConcreteNames)
      TH.UInfixT lType name rType -> [name] ++ ([lType, rType] >>= typeConcreteNames)
      TH.ParensT subtype -> typeConcreteNames subtype
      _ -> []
