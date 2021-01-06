{-# LANGUAGE LambdaCase, TupleSections #-}

module Data.IFunctor.TH
    ( deriveMutualGADT
    , deriveIFunctorITraversable
      -- * Re-exports
    , IFix(..)
    , IFunctor
    , ITraversable
    ) where

import           Control.Monad              (guard, (>=>))
import           Data.Functor               ((<&>))
import           Data.IFunctor
import           Data.Functor.Foldable      (cata, embed)
import           Data.IFunctor.Foldable     (IFix(..))
import           Data.IFunctor.TH.Internal  ()
import           Data.ITraversable
import qualified Data.Map                   as M
import           Data.Maybe                 (fromJust)
import           Data.List                  (nub)
import           Data.Function              ((&))
import qualified Data.Set                   as S
import qualified Language.Haskell.TH        as TH
import qualified Language.Haskell.TH.Syntax as TH

{-|
Given a GADT with type @(ix -> *) -> ix -> *@ where all uses of the internal
function @(ix -> *)@ are unwrapped or wrapped in traversable functors, derive
the IFunctor and ITraversable instances.

Goes best with @deriveMutualGADT@.

For example, given:

@
data Exp = App Exp Exp | Abs Pat Exp | VarE String
data Pat = Wildcard | VarP String | ConP String [Pat]
@

We could invoke @deriveMutualGADT ''Exp@ to produce the following:

@
data ExpIx = ExpI | PatI
data ExpMF (f :: ExpIx -> *) (ix :: ExpIx) where
  AppMF      :: f 'ExpI -> f 'ExpI   -> MF f 'ExpI
  AbsMF      :: f 'PatI -> f 'ExpI   -> MF f 'ExpI
  VarEMF     :: String               -> MF f 'ExpI
  WildcardMF ::                         MF f 'PatI
  VarPMF     :: String               -> MF f 'PatI
  ConPMF     :: String  -> [f 'PatI] -> MF f 'PatI
type ExpM = IFix ExpMF
@

We would also need to use @singlethongs ''ExpIx@ to derive the singlethongs
instances for the generated @ExpIx@.

We could then invoke @deriveIFunctorITraversable ''ExpMF@ to produce the
following instances:

@
instance IFunctor ExpMF where
    imap func =
        \case
            AppMF a0 a1  -> AppMF (id func a0) (id func a1)
            AbsMF a0 a1  -> AbsMF (id func a0) (id func a1)
            VarEMF a0    -> VarEMF a0
            WildcardMF   -> WildcardMF
            VarPMF a0    -> VarPMF a0
            ConPMF a0 a1 -> ConPMF a0 ((fmap . id) func a1)

instance ITraversable ExpMF where
    itraverse func =
        \case
             AppMF a0 a1  -> (pure AppMF \<*\> id func a0) \<*\> id func a1
             AbsMF a0 a1  -> (pure AbsMF \<*\> id func a0) \<*\> id func a1
             VarEMF a0    -> pure VarEMF \<*\> pure a0
             WildcardMF   -> pure WildcardMF
             VarPMF a0    -> pure VarPMF \<*\> pure a0
             ConPMF a0 a1 -> (pure ConPMF \<*\> pure a0) \<*\> (traverse . id) func a1
@

Some unnecessary calls to @pure@ and @id@ are used to make the TemplateHaskell
generation simpler.
-}
deriveIFunctorITraversable :: TH.Name -> TH.Q [TH.Dec]
deriveIFunctorITraversable name = do
    TH.TyConI (TH.DataD _ _ tyVarBndrs _ cons _) <- TH.reify name
    let [TH.KindedTV f fk, TH.KindedTV ix ixk] = tyVarBndrs

    funcName <- TH.newName "func"

    let isFType =
            \case
              (TH.AppT (TH.VarT f') _) -> f' == f
              _ -> False

    let gadtConToMatches (conNames, bangTypes, finalType) = do
            let [conName] = conNames
            let types = snd <$> bangTypes
            patNames <- (TH.newName . ("a"++) . show) `mapM` [0..length types-1]

            let updateFTypesToFmaps (patName, type_) = do
                    (subtype, depth) <- typeGetFunctorAppDepth type_
                    pure $
                        if not $ isFType subtype
                            then TH.VarE patName
                            else repeatedFmap depth (TH.VarE funcName) (TH.VarE patName)

            fmappings <- mapM updateFTypesToFmaps $ zip patNames types

            let updateFTypesToTraversals (patName, type_) = do
                    (subtype, depth) <- typeGetTraversableAppDepth type_
                    pure $
                        if not $ isFType subtype
                            then TH.VarE (TH.mkName "pure") `TH.AppE` TH.VarE patName
                            else repeatedTraverse depth (TH.VarE funcName) (TH.VarE patName)

            traversals <- mapM updateFTypesToTraversals $ zip patNames types

            let fullPat = TH.ConP conName $ TH.VarP <$> patNames
            let appliedFmappings = foldl TH.AppE (TH.ConE conName) fmappings

            let appliedTraversals = foldl apTH (TH.VarE (TH.mkName "pure") `TH.AppE` TH.ConE conName) traversals
                    where
                        apTH a b = TH.InfixE (Just a) (TH.VarE $ TH.mkName "<*>") (Just b)

            pure
                ( TH.Match fullPat (TH.NormalB appliedFmappings) []
                , TH.Match fullPat (TH.NormalB appliedTraversals) []
                )

    (imapMatches, itraverseMatches) <- unzip <$> mapM (gadtConToMatches . fromJust . gadtCon) cons

    let imapDef = TH.LamCaseE imapMatches
    let itraverseDef = TH.LamCaseE itraverseMatches

    let imapName = TH.mkName "imap"
    let imapDec = TH.FunD imapName [TH.Clause [TH.VarP funcName] (TH.NormalB imapDef) []]
    let ifunctorDec = TH.InstanceD Nothing [] (TH.ConT (TH.mkName "IFunctor") `TH.AppT` TH.ConT name) [imapDec]

    let itraverseName = TH.mkName "itraverse"
    let itraverseDec = TH.FunD itraverseName [TH.Clause [TH.VarP funcName] (TH.NormalB itraverseDef) []]
    let itraversableDec = TH.InstanceD Nothing [] (TH.ConT (TH.mkName "ITraversable") `TH.AppT` TH.ConT name) [itraverseDec]

    pure [ifunctorDec, itraversableDec]

gadtCon :: TH.Con -> Maybe ([TH.Name], [TH.BangType], TH.Type)
gadtCon (TH.ForallC _ _ subcon)              = gadtCon subcon
gadtCon (TH.GadtC names bangTypes finalType) = Just (names, bangTypes, finalType)
gadtCon _                                    = Nothing

repeatedApp :: Int -> TH.Name -> TH.Exp -> TH.Exp
repeatedApp i f x = composeAll (replicate i (TH.VarE f)) `TH.AppE` x
    where
        composeAll = foldr compose (TH.VarE $ TH.mkName "id")
        compose exp1 exp2 = TH.InfixE (Just exp1) (TH.VarE $ TH.mkName ".") (Just exp2)

repeatedFmap :: Int -> TH.Exp -> TH.Exp -> TH.Exp
repeatedFmap i f x = repeatedApp i (TH.mkName "fmap") f `TH.AppE` x

repeatedTraverse :: Int -> TH.Exp -> TH.Exp -> TH.Exp
repeatedTraverse i f x = repeatedApp i (TH.mkName "traverse") f `TH.AppE` x

-- Extract type value within type functions matching a typeclass
typeGetClassAppDepth :: TH.Name -> TH.Type -> TH.Q (TH.Type, Int)
typeGetClassAppDepth className type_ =
    case type_ of
        TH.AppT fn arg -> do
            let isVar =
                    case fn of
                      TH.VarT _ -> True
                      _         -> False
            isFunctor <- (not isVar &&) <$> TH.isInstance className [fn]
            if isFunctor
               then (fmap . fmap) (+1) (typeGetFunctorAppDepth arg)
               else pure (type_, 0)
        _ -> pure (type_, 0)

typeGetFunctorAppDepth = typeGetClassAppDepth (TH.mkName "Functor")
typeGetTraversableAppDepth = typeGetClassAppDepth (TH.mkName "Traversable")

{-|
=== Basic use

Requires @DataKinds@, @GADTs@, @KindSignatures@.

Given the name of a mutually-recursive datatype, derive an index and an
indexed functor as a GADT, with suffixes Ix\/I and MF\/MF respectively. Also
derive a type synonym for the IFix'd indexed functor, with suffix F.

For example, given:

@
data Exp = App Exp Exp | Abs Pat Exp | VarE String
data Pat = Wildcard | VarP String | ConP String [Pat]
@

We could invoke @deriveMutualGADT ''Exp@ to produce the following:

@
data ExpIx = ExpI | PatI
data ExpMF (f :: ExpIx -> *) (ix :: ExpIx) where
  AppMF      :: f 'ExpI -> f 'ExpI   -> MF f 'ExpI
  AbsMF      :: f 'PatI -> f 'ExpI   -> MF f 'ExpI
  VarEMF     :: String               -> MF f 'ExpI
  WildcardMF ::                         MF f 'PatI
  VarPMF     :: String               -> MF f 'PatI
  ConPMF     :: String  -> [f 'PatI] -> MF f 'PatI
type ExpM = IFix ExpMF
@

=== Handling Type Variables

If the datatypes have type variables, these will be passed around in the
index. For example, given:

@
data Exp a = App a Exp Exp | Abs a Pat Exp | VarE a String
data Pat a (n :: Nat) = Wildcard a | VarP a (Proxy n) String | ConP a String [Pat (n + 1)]
@

We will derive an index:

@
data ExpIx a0 a1 = ExpI a0 | PatI a0 a1
@

Which, when lifted by DataKinds, will have constructors:

@
'ExpI :: a0       -> ExpIx a0 a1
'PatI :: a0 -> a1 -> ExpIx a0 a1
@

Will be used as the index to the mutually-recursive datatype:

@
data ExpMF (f :: ExpIx * Nat -> *) (ix :: ExpIx * Nat) where
  AppMF      :: a0 -> f ('ExpI a0)    -> f ('ExpI a0)      -> ExpMF f ('ExpI a0)
  AbsMF      :: a0 -> f ('PatI a0 a1) -> f ('ExpI a0)      -> ExpMF f ('ExpI a0)
  VarEMF     :: a0 -> String                               -> ExpMF f ('ExpI a0)
  WildcardMF :: a0                                         -> ExpMF f ('PatI a0 a1)
  VarPMF     :: a0 -> Proxy a1        -> String            -> ExpMF f ('PatI a0 a1)
  ConPMF     :: a0 -> String          -> [f ('PatI a0 a1)] -> ExpMF f ('PatI a0 a1)
type ExpM = IFix ExpMF
@

=== Note on Singlethongs and Type variables

Singlethongs is currently unable to derive singleton instances for datatypes
that are not simple enums.

As such, singlethongs does not support the index types generated for
mutually-recursive datatypes with type variables, as in the example above with
@Exp a@ and @Pat a n@.

-}
deriveMutualGADT :: TH.Name -> TH.Q [TH.Dec]
deriveMutualGADT topLevel = do
    assertExtensionEnabled TH.DataKinds
    assertExtensionEnabled TH.GADTs
    assertExtensionEnabled TH.KindSignatures

    -- Find all datatypes that are involved in a mutually-recursive cycle
    mutrecNames <- S.toList <$> findRecursiveConstructors topLevel

    -- Derive tag name, kinds that will be instantiated in the tag as types
    tagName <- suffixify "Ix" topLevel
    allKinds <- datasGetKinds mutrecNames
    kindVars <- mapM (TH.newName . ("a"++) . show) [0..length allKinds-1]
    let tagKindToVar kind = lookup kind $ zip allKinds kindVars

    -- Make a tag constructor for declaration, and return variables inserted
    let mkTag mutrecName = do
            (TH.TyConI (TH.DataD _ _ tyVarBndrs _ _ _)) <- TH.reify mutrecName
            tagConName <- suffixify "I" mutrecName
            let tagConVars =
                    TH.VarT . fromJust . tagKindToVar . tyVarBndrToKind <$> tyVarBndrs
            let tagBangTypes = (TH.Bang TH.NoSourceUnpackedness TH.NoSourceStrictness,) <$> tagConVars
            let constructor = TH.NormalC tagConName tagBangTypes
            pure (tagConName, constructor, tagConVars)

    -- Create tag constructors, tag declaration
    (tagConNames, tagConstructors, tagConVars) <- unzip3 <$> mapM mkTag mutrecNames
    let tagDecl = TH.DataD [] tagName (TH.PlainTV <$> kindVars) Nothing tagConstructors []
    let appliedTag = foldl TH.AppT (TH.ConT tagName) allKinds
    let mutrecNamesAndTagConNamesVars = zip mutrecNames $ zip tagConNames tagConVars

    -- Name of Mutually-recursive base Functor, GADT, algebra f, index ix
    gadtName <- suffixify "MF" topLevel
    gadtF <- TH.newName "f"
    let gadtFKind = TH.KindedTV gadtF (TH.ArrowT `TH.AppT` appliedTag `TH.AppT` TH.StarT)
    gadtIx <- TH.newName "ix"
    let gadtIxKind = TH.KindedTV gadtIx appliedTag

    -- Given a mutrecName, derive the constructors for a GADT
    let mutrecNameAndTagToGadtCons (mutrecName, (tagConName, tagConVar)) = do
            -- Pull out the datatype's constuctors and type variables
            TH.TyConI (TH.DataD _ _ tyVarBndrs _ cons _) <- TH.reify mutrecName

            -- Given a concrete type, if it matches any of the recursive
            -- datatypes, replace it with @f <tag>@
            let matchingTypeToFTag =
                    typeUpdateDeepApp $ \(name, depth) -> do
                        (tagConName, tagConVar) <- lookup name mutrecNamesAndTagConNamesVars
                        guard $ depth == length tagConVar
                        pure $ TH.VarT gadtF `TH.AppT` foldl TH.AppT (TH.ConT tagConName) tagConVar

            -- Convert type variables to their corresponding tag variables
            let tyVarNames = tyVarBndrToName <$> tyVarBndrs
            let tyVarNameToConVarName name = lookup name $ tyVarNames `zip` tagConVar

            -- Final type is @<name> <f> <tag>@
            let finalType = TH.ConT gadtName `TH.AppT` TH.VarT gadtF `TH.AppT` foldl TH.AppT (TH.ConT tagConName) tagConVar

            cons
                -- Update all constructors' types using to their @f <tag>@ equivalents
                & map (updateTypes matchingTypeToFTag)
                -- Update all appropriate type variables with equivalents provided by the index
                & map (updateTypes (typeUpdateVariable tyVarNameToConVarName))
                -- Append MF to all constructor names
                & mapM updateToMFName
                -- Convert base constructors to GADT constructors
                & fmap (map $ conToGadt finalType)

    -- Derive GADT constructors for all recursive data types, concat
    allGadtCons <- concat <$> mapM mutrecNameAndTagToGadtCons mutrecNamesAndTagConNamesVars

    -- Final GADT w/ name, f, ix, and derived constructors
    let gadtDecl = TH.DataD [] gadtName [gadtFKind, gadtIxKind] Nothing allGadtCons []

    -- Type synonym for fixed version of GADT
    gadtFixName <- suffixify "M" topLevel
    let gadtFix = TH.TySynD gadtFixName [] $ TH.ConT (TH.mkName "IFix") `TH.AppT` TH.ConT gadtName

    pure [tagDecl, gadtDecl, gadtFix]

-- Get the kinds for type variables to a datatype
dataGetKinds :: TH.Name -> TH.Q [TH.Kind]
dataGetKinds name = TH.reify name <&> \info ->
    let (TH.TyConI (TH.DataD _ _ tyVarBndrs _ _ _)) = info
    in
    tyVarBndrToKind <$> tyVarBndrs

tyVarBndrToKind :: TH.TyVarBndr -> TH.Kind
tyVarBndrToKind (TH.PlainTV _) = TH.StarT
tyVarBndrToKind (TH.KindedTV _ kind) = kind

tyVarBndrToName :: TH.TyVarBndr -> TH.Name
tyVarBndrToName (TH.PlainTV name) = name
tyVarBndrToName (TH.KindedTV name _) = name

datasGetKinds :: Traversable t => t TH.Name -> TH.Q [TH.Kind]
datasGetKinds = fmap (nub . concat) . traverse dataGetKinds

assertExtensionEnabled :: TH.Extension -> TH.Q ()
assertExtensionEnabled ext = do
    enabled <- TH.isExtEnabled ext
    if enabled
       then pure ()
       else fail $ "deriveMutualGADT: Extension '" ++ show ext ++ "' is not enabled."

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
        TH.InfixC {}              ->
            error $ "Constructor '" ++ show con ++ "' to turn to GADT is Infix"
        TH.ForallC {}             ->
            error $ "Constructor '" ++ show con ++ "' to turn to GADT is forall quanitified"
        _                         ->
            error $ "Constructor '" ++ show con ++ "' to turn to GADT is already a GADT"

-- Update data constructors names to have MF suffix
updateToMFName :: TH.Con -> TH.Q TH.Con
updateToMFName =
    \case
        TH.NormalC name bangTypes            -> suffixify "MF" name >>= \nameS -> pure $ TH.NormalC nameS bangTypes
        TH.RecC name varBangTypes            -> suffixify "MF" name >>= \nameS -> pure $ TH.RecC nameS varBangTypes
        TH.InfixC lType name rType           -> suffixify "MF" name >>= \nameS -> pure $ TH.InfixC lType nameS rType
        TH.ForallC bndrs cxt con             -> TH.ForallC bndrs cxt <$> updateToMFName con
        TH.GadtC names bangTypes type_       -> mapM (suffixify "MF") names >>= \namesS -> pure $ TH.GadtC namesS bangTypes type_
        TH.RecGadtC names varBangTypes type_ -> mapM (suffixify "MF") names >>= \namesS -> pure $ TH.RecGadtC namesS varBangTypes type_

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

-- Update types matching a predicate pred using a function f
typeUpdateG :: (TH.Type -> Maybe TH.Type) -> TH.Type -> TH.Type
typeUpdateG f = cata alg
    where
        alg x =
            case f (embed x) of
              Nothing -> embed x
              Just t  -> t

-- Update concrete types to others using a function f
typeUpdateConcrete :: (TH.Name -> Maybe TH.Type) -> TH.Type -> TH.Type
typeUpdateConcrete f = typeUpdateG $ matchConT >=> f

-- Update variable types to others using a function f
typeUpdateVariable :: (TH.Name -> Maybe TH.Type) -> TH.Type -> TH.Type
typeUpdateVariable f = typeUpdateG $ matchVarT >=> f

matchConT, matchVarT :: TH.Type -> Maybe TH.Name
matchConT (TH.ConT name) = Just name
matchConT _ = Nothing
matchVarT (TH.VarT name) = Just name
matchVarT _ = Nothing

-- Update applied concrete type of a specific depth
typeUpdateDeepApp :: ((TH.Name, Int) -> Maybe TH.Type) -> TH.Type -> TH.Type
typeUpdateDeepApp f = typeUpdateG $ depth >=> f
    where
        depth (TH.ConT name) = Just (name, 0)
        depth (TH.AppT fn _) = fmap (fmap (1 +)) (depth fn)
        depth _              = Nothing

-- Find recursive constructors, given the name of the "starting" type
findRecursiveConstructors :: TH.Name -> TH.Q Names
findRecursiveConstructors name = S.fromList . M.keys . prune <$> nameDeps name
    where
    prune :: NameMap -> NameMap
    prune names =
        let nonterminalNames = M.filter (not . S.null) names
            nonterminalParents = M.map (S.filter (`M.member` nonterminalNames)) nonterminalNames
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
            let newFound = foldr (uncurry M.insert) found unseenNamePairs
            let newFrontier = S.toList $ foldr (S.union . snd) S.empty unseenNamePairs
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
              TH.TyConI (TH.DataD _ _ _ _ cons _) -> cons
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
      TH.InfixT lType name rType -> name : ([lType, rType] >>= typeConcreteNames)
      TH.UInfixT lType name rType -> name : ([lType, rType] >>= typeConcreteNames)
      TH.ParensT subtype -> typeConcreteNames subtype
      _ -> []
