{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module MiniConcatTypechecker where

import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Control.Monad.State
import Control.Monad (foldM)

--------------------------------------------------------------------------------
-- 1. Element types, stack types, and arrow types
--------------------------------------------------------------------------------

newtype TVar = TV String
  deriving (Eq, Ord)

instance Show TVar where
  show (TV s) = s

newtype SVar = SV String
  deriving (Eq, Ord)

instance Show SVar where
  show (SV s) = s

-- Element types
data Ty
  = TVarTy TVar
  | TInt
  | TBool
  deriving (Eq, Ord)

instance Show Ty where
  show (TVarTy a) = show a
  show TInt       = "Int"
  show TBool      = "Bool"

-- Stack types: lists of element types with stack variables
data SType
  = SVarTy SVar      -- ρ
  | SNil             -- empty stack •
  | SCons SType Ty   -- Σ · τ
  deriving (Eq, Ord)

instance Show SType where
  show SNil = "•"
  show (SVarTy v) = show v
  show st = "[" ++ go st ++ "]"
    where
      go SNil = ""
      go (SVarTy v) = show v
      go (SCons s t) =
        case s of
          SNil        -> show t
          _           -> go s ++ ", " ++ show t

-- Arrows: stack transformers Σ_in ⇒ Σ_out
data Arrow = Arrow SType SType
  deriving (Eq, Ord)

instance Show Arrow where
  show (Arrow s1 s2) = show s1 ++ " ⇒ " ++ show s2

--------------------------------------------------------------------------------
-- 2. Schemes and environments (only polymorphism over stack vars & type vars)
--------------------------------------------------------------------------------

data Scheme = Forall [TVar] [SVar] Arrow
  deriving (Eq, Ord)

instance Show Scheme where
  show (Forall tvars svars arr) =
    "∀ " ++ unwords (map show tvars ++ map show svars) ++ ". " ++ show arr

type Env = Map String Scheme

--------------------------------------------------------------------------------
-- 3. Substitutions and "apply"
--------------------------------------------------------------------------------

data Subst = Subst
  { tySub :: Map TVar Ty
  , stSub :: Map SVar SType
  } deriving (Eq, Show)

emptySubst :: Subst
emptySubst = Subst M.empty M.empty

-- composeSubst s2 s1 = apply s2 after s1
composeSubst :: Subst -> Subst -> Subst
composeSubst s2 s1 =
  Subst
    { tySub = M.map (apply s2) (tySub s1) `M.union` tySub s2
    , stSub = M.map (apply s2) (stSub s1) `M.union` stSub s2
    }

class Substitutable a where
  apply :: Subst -> a -> a

instance Substitutable Ty where
  apply (Subst tSub _) t@(TVarTy v) =
    fromMaybe t (M.lookup v tSub)
  apply _ TInt       = TInt
  apply _ TBool      = TBool

instance Substitutable SType where
  apply s@(Subst _ sSub) st@(SVarTy v) =
    case M.lookup v sSub of
      Nothing -> st
      Just st' -> apply s st'
  apply _ SNil = SNil
  apply s (SCons st ty) = SCons (apply s st) (apply s ty)

instance Substitutable Arrow where
  apply s (Arrow i o) = Arrow (apply s i) (apply s o)

instance Substitutable Scheme where
  -- For a sketch we just apply to the arrow; a real system would avoid
  -- touching bound variables in Forall.
  apply s (Forall tv sv arr) = Forall tv sv (apply s arr)

instance Substitutable Env where
  apply s = M.map (apply s)

--------------------------------------------------------------------------------
-- 4. Constraints and unification
--------------------------------------------------------------------------------

data Constraint
  = CEqTy Ty Ty
  | CEqStack SType SType
  deriving (Eq, Show)

-- Occurs check for type vars
occursTy :: TVar -> Ty -> Bool
occursTy a (TVarTy b) = a == b
occursTy _ TInt       = False
occursTy _ TBool      = False

occursTySubst :: Subst -> TVar -> Ty -> Bool
occursTySubst s a = go M.empty
  where
    go seen (TVarTy b)
      | a == b = True
      | M.member b seen = False
      | otherwise =
          case M.lookup b (tySub s) of
            Nothing -> False
            Just t' -> go (M.insert b () seen) t'
    go _ TInt = False
    go _ TBool = False

-- Occurs check for stack vars
occursStack :: SVar -> SType -> Bool
occursStack v (SVarTy v')    = v == v'
occursStack _ SNil           = False
occursStack v (SCons s t)    = occursStack v s || occursTyInStack v t
  where
    occursTyInStack _ (TVarTy _) = False
    occursTyInStack _ TInt       = False
    occursTyInStack _ TBool      = False

occursStackSubst :: Subst -> SVar -> SType -> Bool
occursStackSubst s v = go M.empty
  where
    go seen (SVarTy v')
      | v == v' = True
      | M.member v' seen = False
      | otherwise =
          case M.lookup v' (stSub s) of
            Nothing -> False
            Just st' -> go (M.insert v' () seen) st'
    go _ SNil = False
    go seen (SCons st _) = go seen st

-- Unify simple element types
unifyTy :: Subst -> Ty -> Ty -> Either String Subst
unifyTy s t1 t2 =
  let t1' = apply s t1
      t2' = apply s t2
  in case (t1', t2') of
    (TVarTy a, t) -> bindTyVar s a t
    (t, TVarTy a) -> bindTyVar s a t
    (TInt, TInt)  -> Right s
    (TBool, TBool)-> Right s
    _             -> Left $ "Cannot unify types: " ++ show t1' ++ " vs " ++ show t2'

bindTyVar :: Subst -> TVar -> Ty -> Either String Subst
bindTyVar s a t
  | t == TVarTy a = Right s
  | occursTySubst s a t = Left $ "Occurs check failed: " ++ show a ++ " in " ++ show t
  | otherwise     = Right s { tySub = M.insert a t (tySub s) }

-- Unify stack types
unifyStack :: Subst -> SType -> SType -> Either String Subst
unifyStack s st1 st2 =
  let st1' = apply s st1
      st2' = apply s st2
  in case (st1', st2') of
    (SNil, SNil) -> Right s
    (SVarTy v, st) -> bindStackVar s v st
    (st, SVarTy v) -> bindStackVar s v st
    (SCons s1 t1, SCons s2 t2) -> do
      s'  <- unifyTy s t1 t2
      s'' <- unifyStack s' s1 s2
      Right s''
    _ -> Left $ "Cannot unify stacks: " ++ show st1' ++ " vs " ++ show st2'

bindStackVar :: Subst -> SVar -> SType -> Either String Subst
bindStackVar s v st
  | st == SVarTy v     = Right s
  | occursStackSubst s v st =
      Left $ "Occurs check failed on stack: " ++ show v ++ " in " ++ show st
  | otherwise          = Right s { stSub = M.insert v st (stSub s) }

-- Solve a list of constraints
solve :: [Constraint] -> Either String Subst
solve = foldM step emptySubst
  where
    step s (CEqTy t1 t2)     = unifyTy s t1 t2
    step s (CEqStack st1 st2)= unifyStack s st1 st2

--------------------------------------------------------------------------------
-- 5. Inference monad and helpers (for fresh vars and instantiation)
--------------------------------------------------------------------------------

newtype Infer a = Infer { runInfer :: State Int a }
  deriving (Functor, Applicative, Monad)

runInfer0 :: Infer a -> a
runInfer0 m = evalState (runInfer m) 0

freshTyVar :: Infer Ty
freshTyVar = Infer $ do
  n <- get
  put (n + 1)
  pure (TVarTy (TV ("a" ++ show n)))

freshSVar :: Infer SType
freshSVar = Infer $ do
  n <- get
  put (n + 1)
  pure (SVarTy (SV ("ρ" ++ show n)))

freshSVarName :: Infer SVar
freshSVarName = Infer $ do
  n <- get
  put (n + 1)
  pure (SV ("ρ" ++ show n))

freshTyVarName :: Infer TVar
freshTyVarName = Infer $ do
  n <- get
  put (n + 1)
  pure (TV ("a" ++ show n))

-- Instantiate a polymorphic scheme with fresh type & stack variables
instantiate :: Scheme -> Infer Arrow
instantiate (Forall tvars svars arr) = do
  newTVs <- mapM (const freshTyVarName) tvars
  newSVs <- mapM (const freshSVarName) svars
  let tSub = M.fromList (zip tvars (map TVarTy newTVs))
      sSub = M.fromList (zip svars (map SVarTy newSVs))
      subst = Subst tSub sSub
  pure (apply subst arr)

--------------------------------------------------------------------------------
-- 6. Terms and inference rules
--------------------------------------------------------------------------------

data Term
  = Prim String
  | Tensor Term Term      -- juxtaposition (automatic tensor)
  | Seq Term Term         -- t >> u
  deriving (Show)

-- Stack append: Σ1 · Σ2 (right-associative)
appendStack :: SType -> SType -> SType
appendStack SNil s2          = s2
appendStack (SVarTy v) s2    = SCons (SVarTy v) (errorTy s2)
  where
    -- this is a hacky placeholder; for a full system you'd
    -- represent stack concatenation structurally. For a simple
    -- toy, we avoid ever actually using appendStack on SVarTy in
    -- well-typed examples.
    errorTy _ = TInt
appendStack (SCons s t) s2   = SCons (appendStack s s2) t

-- For our simple calculus we only append *concrete* stacks built from SNil/SCons.
-- In the example we never need to append SVarTy stacks directly.

-- Inference: given an Env and a Term, produce an Arrow and constraints
infer :: Env -> Term -> Infer (Arrow, [Constraint])
infer env (Prim name) =
  case M.lookup name env of
    Nothing ->
      error $ "Unknown primitive: " ++ name
    Just sc -> do
      arr <- instantiate sc
      pure (arr, [])

infer env (Tensor t u) = do
  (Arrow i1 o1, c1) <- infer env t
  (Arrow i2 o2, c2) <- infer env u
  let inStack  = appendStack i1 i2
      outStack = appendStack o1 o2
  pure (Arrow inStack outStack, c1 ++ c2)

infer env (Seq t u) = do
  (Arrow i1 o1, c1) <- infer env t
  (Arrow i2 o2, c2) <- infer env u
  let c = CEqStack o1 i2
  pure (Arrow i1 o2, c1 ++ c2 ++ [c])

--------------------------------------------------------------------------------
-- 7. A sample primitive environment
--------------------------------------------------------------------------------

-- Helpers to build stack types
sNil :: SType
sNil = SNil

sCons :: SType -> Ty -> SType
sCons = SCons

-- Primitive environment:
--  1      : • ⇒ • · Int
--  2      : • ⇒ • · Int
--  f,g    : • · Int ⇒ • · Int
--  +      : • · Int · Int ⇒ • · Int
--  print  : • · Int ⇒ •
primEnv :: Env
primEnv =
  let oneTy   = Forall [] []
        (Arrow sNil (sCons sNil TInt))
      twoTy   = Forall [] []
        (Arrow sNil (sCons sNil TInt))
      fTy     = Forall [] []
        (Arrow (sCons sNil TInt) (sCons sNil TInt))
      gTy     = fTy
      plusTy  = Forall [] []
        (Arrow (sCons (sCons sNil TInt) TInt)
               (sCons sNil TInt))
      printTy = Forall [] []
        (Arrow (sCons sNil TInt) sNil)
  in M.fromList
       [ ("1",     oneTy)
       , ("2",     twoTy)
       , ("f",     fTy)
       , ("g",     gTy)
       , ("+",     plusTy)
       , ("print", printTy)
       ]

--------------------------------------------------------------------------------
-- 8. Example program: 1 2 >> f g >> + >> print
--------------------------------------------------------------------------------

-- AST for: 1 2 >> f g >> + >> print
exampleTerm :: Term
exampleTerm =
  Seq
    (Seq
      (Seq
        (Tensor (Prim "1") (Prim "2"))
        (Tensor (Prim "f") (Prim "g")))
      (Prim "+"))
    (Prim "print")

-- Run inference + unification
inferExample :: Either String Arrow
inferExample =
  let (arr, cs) = runInfer0 (infer primEnv exampleTerm)
  in do
    s <- solve cs
    pure (apply s arr)

--------------------------------------------------------------------------------
-- 9. Pretty driver to see the result in GHCi
--------------------------------------------------------------------------------

prettyInferExample :: IO ()
prettyInferExample =
  case inferExample of
    Left err ->
      putStrLn $ "Type error: " ++ err
    Right arr ->
      putStrLn $ "exampleTerm : " ++ show arr
