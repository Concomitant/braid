{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module MiniConcatTypechecker where

import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import Data.List (nub, intercalate, (\\))
import Control.Monad.State
import Control.Monad (foldM)
import Data.Char (isDigit, isSpace)

--------------------------------------------------------------------------------
-- 1. Element types, stack types, and arrow types
--
-- Remainder discipline (see expanded-spec.md): every stack type is a
-- left-to-right list of element types with an end that is either closed
-- (SEnd, the empty stack •) or a single stack variable (STail ρ).  The
-- variable may only ever be the tail — never leading, never in the middle.
-- This keeps stack unification plain list unification and inference
-- HM-principal.
--------------------------------------------------------------------------------

newtype TVar = TV String
  deriving (Eq, Ord)

instance Show TVar where
  show (TV s) = s

newtype SVar = SV String
  deriving (Eq, Ord)

instance Show SVar where
  show (SV s) = s

-- Element types.  TCode nests whole arrows inside element types, so
-- stack variables can occur inside types — all traversals (occurs
-- checks, substitution, unification) must recurse through it.
data Ty
  = TVarTy TVar
  | TInt
  | TBool
  | TCode Arrow          -- Code⟨Γ ⇒ Δ⟩: a reified program
  | TList Ty             -- List A: homogeneous list
  deriving (Eq, Ord)

instance Show Ty where
  show (TVarTy a)  = show a
  show TInt        = "Int"
  show TBool       = "Bool"
  show (TCode arr) = "Code⟨" ++ show arr ++ "⟩"
  show (TList t)   = "List " ++ parens t
    where
      parens u@(TList _) = "(" ++ show u ++ ")"
      parens u           = show u

-- Stack types: front (leftmost) wire first, optional tail variable at the end
data SType
  = SEnd             -- closed end: empty stack •
  | STail SVar       -- open end: remainder variable ρ
  | SCons Ty SType   -- τ Σ (τ is the leftmost wire)
  deriving (Eq, Ord)

instance Show SType where
  show SEnd       = "•"
  show (STail v)  = show v
  show st         = unwords (go st)
    where
      go SEnd           = []
      go (STail v)      = [show v]
      go (SCons t rest) = show t : go rest

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
  apply s@(Subst tSub _) t@(TVarTy v) =
    case M.lookup v tSub of
      Nothing -> t
      Just t' -> apply s t'   -- chase chains, like the SType instance
  apply _ TInt        = TInt
  apply _ TBool       = TBool
  apply s (TCode arr) = TCode (apply s arr)
  apply s (TList t)   = TList (apply s t)

instance Substitutable SType where
  apply _ SEnd = SEnd
  apply s@(Subst _ sSub) st@(STail v) =
    case M.lookup v sSub of
      Nothing  -> st
      Just st' -> apply s st'
  apply s (SCons ty rest) = SCons (apply s ty) (apply s rest)

instance Substitutable Arrow where
  apply s (Arrow i o) = Arrow (apply s i) (apply s o)

instance Substitutable Scheme where
  -- Bound variables are removed from the substitution before it touches
  -- the arrow, so quantified names are never captured.
  apply s (Forall tv sv arr) =
    let s' = Subst (foldr M.delete (tySub s) tv)
                   (foldr M.delete (stSub s) sv)
    in Forall tv sv (apply s' arr)

instance Substitutable Env where
  apply s = M.map (apply s)

--------------------------------------------------------------------------------
-- 4. Constraints and unification
--------------------------------------------------------------------------------

data Constraint
  = CEqTy Ty Ty
  | CEqStack SType SType
  deriving (Eq, Show)

-- All variables (type and stack) in order of first appearance, recursing
-- through Code⟨Γ ⇒ Δ⟩ element types.  The single traversal backing the
-- occurs checks, generalization, and alpha-normalization.
varsOfTy :: Ty -> ([TVar], [SVar])
varsOfTy (TVarTy v)  = ([v], [])
varsOfTy TInt        = ([], [])
varsOfTy TBool       = ([], [])
varsOfTy (TCode arr) = varsOfArrow arr
varsOfTy (TList t)   = varsOfTy t

varsOfStack :: SType -> ([TVar], [SVar])
varsOfStack SEnd           = ([], [])
varsOfStack (STail v)      = ([], [v])
varsOfStack (SCons t rest) =
  let (t1, s1) = varsOfTy t
      (t2, s2) = varsOfStack rest
  in (t1 ++ t2, s1 ++ s2)

varsOfArrow :: Arrow -> ([TVar], [SVar])
varsOfArrow (Arrow i o) =
  let (t1, s1) = varsOfStack i
      (t2, s2) = varsOfStack o
  in (nub (t1 ++ t2), nub (s1 ++ s2))

-- Occurs checks.  Callers (bindTyVar/bindStackVar) only ever check
-- against fully-applied targets, so a pure structural traversal is
-- sufficient — no substitution chasing needed.
occursTy :: TVar -> Ty -> Bool
occursTy a t = a `elem` fst (varsOfTy t)

occursStack :: SVar -> SType -> Bool
occursStack v st = v `elem` snd (varsOfStack st)

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
    (TCode (Arrow i1 o1), TCode (Arrow i2 o2)) -> do
      s' <- unifyStack s i1 i2
      unifyStack s' o1 o2
    (TList a1, TList a2) -> unifyTy s a1 a2
    _             -> Left $ "Cannot unify types: " ++ show t1' ++ " vs " ++ show t2'

bindTyVar :: Subst -> TVar -> Ty -> Either String Subst
bindTyVar s a t
  | t == TVarTy a = Right s
  | occursTy a t = Left $ "Occurs check failed: " ++ show a ++ " in " ++ show t
  | otherwise     = Right s { tySub = M.insert a t (tySub s) }

-- Unify stack types (plain list unification with an optional tail variable)
unifyStack :: Subst -> SType -> SType -> Either String Subst
unifyStack s st1 st2 =
  let st1' = apply s st1
      st2' = apply s st2
  in case (st1', st2') of
    (SEnd, SEnd) -> Right s
    (STail v, st) -> bindStackVar s v st
    (st, STail v) -> bindStackVar s v st
    (SCons t1 r1, SCons t2 r2) -> do
      s'  <- unifyTy s t1 t2
      unifyStack s' r1 r2
    _ -> Left $ "Cannot unify stacks: " ++ show st1' ++ " vs " ++ show st2'

bindStackVar :: Subst -> SVar -> SType -> Either String Subst
bindStackVar s v st
  | st == STail v = Right s
  | occursStack v st =
      Left $ "Occurs check failed on stack: " ++ show v ++ " in " ++ show st
  | otherwise = Right s { stSub = M.insert v st (stSub s) }

-- Solve a list of constraints
solve :: [Constraint] -> Either String Subst
solve = foldM step emptySubst
  where
    step s (CEqTy t1 t2)      = unifyTy s t1 t2
    step s (CEqStack st1 st2) = unifyStack s st1 st2

--------------------------------------------------------------------------------
-- 5. Inference monad and helpers (for fresh vars and instantiation)
--------------------------------------------------------------------------------

newtype Infer a = Infer { runInfer :: State Int a }
  deriving (Functor, Applicative, Monad)

runInfer0 :: Infer a -> a
runInfer0 m = evalState (runInfer m) 0

freshTyVarName :: Infer TVar
freshTyVarName = Infer $ do
  n <- get
  put (n + 1)
  pure (TV ("a" ++ show n))

freshSVarName :: Infer SVar
freshSVarName = Infer $ do
  n <- get
  put (n + 1)
  pure (SV ("ρ" ++ show n))

-- One-shot simultaneous substitution, NO chasing.  Instantiation is a
-- rename: a scheme generalized in one inference run may bind names (a0,
-- ρ1, …) that textually coincide with this run's fresh names, so using
-- the solver's chasing `apply` here can chain (a0 → a1 → a2, collapsing
-- distinct binders) or even cycle (a0 → a0, diverging).
substOnce :: Subst -> Arrow -> Arrow
substOnce s (Arrow i o) = Arrow (goS i) (goS o)
  where
    goS SEnd = SEnd
    goS st@(STail v)  = fromMaybe st (M.lookup v (stSub s))
    goS (SCons t rest) = SCons (goT t) (goS rest)

    goT t@(TVarTy v) = fromMaybe t (M.lookup v (tySub s))
    goT (TCode arr)  = TCode (substOnce s arr)
    goT (TList t)    = TList (goT t)
    goT t            = t

-- Instantiate a polymorphic scheme with fresh type & stack variables
-- (used for the final atom of a tensor chain, which may stay open).
instantiate :: Scheme -> Infer Arrow
instantiate (Forall tvars svars arr) = do
  newTVs <- mapM (const freshTyVarName) tvars
  newSVs <- mapM (const freshSVarName) svars
  let tSub = M.fromList (zip tvars (map TVarTy newTVs))
      sSub = M.fromList (zip svars (map STail newSVs))
  pure (substOnce (Subst tSub sSub) arr)

-- Instantiate a scheme *closed*: bound stack variables become the empty
-- stack (ρ := •).  Used for every non-final atom of a tensor chain, per
-- the remainder discipline.
instantiateClosed :: Scheme -> Infer Arrow
instantiateClosed (Forall tvars svars arr) = do
  newTVs <- mapM (const freshTyVarName) tvars
  let tSub = M.fromList (zip tvars (map TVarTy newTVs))
      sSub = M.fromList (zip svars (repeat SEnd))
  pure (substOnce (Subst tSub sSub) arr)

--------------------------------------------------------------------------------
-- 6. Terms
--------------------------------------------------------------------------------

data Term
  = Prim String
  | Tensor [Term]         -- n-ary tensor chain, atoms aligned with wires left to right
  | Seq Term Term         -- t >> u
  | Quote Term            -- [p]: push the reified program p
  | ListLit [Term]        -- list(e1, …, en): push a list; each element
                          -- must be a pure push (• ⇒ A)
  deriving (Eq, Show)

--------------------------------------------------------------------------------
-- 6.0 Tokenizer
--
-- Newline is strict `>>` (a program is a sequence of tensor stages, one
-- per line); `>>>` and `...` are the remainder sugar.
--------------------------------------------------------------------------------

data Token
  = TokIdent String
  | TokInt Int
  | TokSeq        -- >>
  | TokSeqPass    -- >>>
  | TokEllipsis   -- ...
  | TokNewline    -- line break (strict >>)
  | TokLBrack     -- [ (open quotation)
  | TokRBrack     -- ] (close quotation)
  | TokLParen     -- ( (list literal)
  | TokRParen     -- )
  | TokComma      -- ,
  deriving (Eq, Show)

tokenize :: String -> Either String [Token]
tokenize = go
  where
    go [] = Right []
    go ('\r':'\n':cs) = (TokNewline :) <$> go cs
    go ('\n':cs)      = (TokNewline :) <$> go cs
    go ('>':'>':'>':cs) = (TokSeqPass :) <$> go cs
    go ('>':'>':cs)     = (TokSeq :) <$> go cs
    go ('>':_)          = Left "Unexpected '>' without matching '>>'"
    go ('.':'.':'.':cs) = (TokEllipsis :) <$> go cs
    go ('.':_)          = Left "Unexpected '.' (did you mean '...'?)"
    go ('[':cs)         = (TokLBrack :) <$> go cs
    go (']':cs)         = (TokRBrack :) <$> go cs
    go ('(':cs)         = (TokLParen :) <$> go cs
    go (')':cs)         = (TokRParen :) <$> go cs
    go (',':cs)         = (TokComma :) <$> go cs
    go (c:cs)
      | isSpace c = go cs
      | isDigit c =
          let (digits, rest) = span isDigit (c:cs)
          in (TokInt (read digits) :) <$> go rest
      | otherwise =
          let (ident, rest) = span isIdentChar (c:cs)
          in (TokIdent ident :) <$> go rest

    isIdentChar ch =
      not (isSpace ch) && ch `notElem` (">.[]()," :: String)

-- Collapse newline runs, drop leading/trailing newlines, and absorb
-- newlines adjacent to an explicit >> / >>> (the operator wins).
normalizeToks :: [Token] -> [Token]
normalizeToks = trim . collapse
  where
    collapse [] = []
    collapse (TokNewline : ts) =
      case dropWhile (== TokNewline) ts of
        rest@(t : _) | isSeqOp t -> collapse rest
        rest                     -> TokNewline : collapse rest
    collapse (t : ts)
      | isSeqOp t = t : collapse (dropWhile (== TokNewline) ts)
      | otherwise = t : collapse ts

    trim = dropWhile (== TokNewline) . dropTrailing
    dropTrailing = reverse . dropWhile (== TokNewline) . reverse

    isSeqOp t = t == TokSeq || t == TokSeqPass

--------------------------------------------------------------------------------
-- 6.1 Parser: stages, >>, >>>, newline, and ... (juxtaposition binds
-- tighter than sequencing; both left-associative)
--------------------------------------------------------------------------------

data Stage = Stage
  { stageAtoms :: [Term]
  , stageHasPass :: Bool   -- stage ends in `...` (trailing remainder)
  } deriving (Show)

data StageOp
  = StageSeq      -- >> or newline
  | StageSeqPass  -- >>>
  deriving (Eq, Show)

data Stmt = Stmt Stage [(StageOp, Stage)]
  deriving (Show)

parseProgram :: String -> Either String Term
parseProgram input = do
  toks <- normalizeToks <$> tokenize input
  (stmt, rest) <- parseStmt toks
  case rest of
    [] -> Right (desugarStmt stmt)
    _  -> Left $ "Unexpected tokens at end: " ++ show rest

parseStmt :: [Token] -> Either String (Stmt, [Token])
parseStmt toks = do
  (s0, rest) <- parseStage toks
  (ops, rest') <- go [] rest
  Right (Stmt s0 ops, rest')
  where
    go acc (TokSeq : rest')     = next acc StageSeq rest'
    go acc (TokSeqPass : rest') = next acc StageSeqPass rest'
    go acc (TokNewline : rest') = next acc StageSeq rest'
    go acc rest'                = Right (reverse acc, rest')

    next acc op rest' = do
      (stage, rest'') <- parseStage rest'
      go ((op, stage) : acc) rest''

parseStage :: [Token] -> Either String (Stage, [Token])
parseStage = go []
  where
    go acc (TokIdent "list" : TokLParen : rest) = do
      (elems, rest') <- parseListElems rest
      go (ListLit elems : acc) rest'
    go acc (TokIdent name : rest) = go (Prim name : acc) rest
    go acc (TokInt n : rest)      = go (Prim (show n) : acc) rest
    go acc (TokLBrack : rest)     = do
      (stmt, rest') <- parseStmt rest
      case rest' of
        (TokRBrack : rest'') -> go (Quote (desugarStmt stmt) : acc) rest''
        _ -> Left "Unclosed quotation (expected ']')"
    go acc (TokEllipsis : rest)   =
      case rest of
        (t : _) | isStageTok t ->
          Left "'...' must be the final atom of a tensor stage"
        _ -> Right (Stage (reverse acc) True, rest)
    go acc rest
      | null acc  = Left $ "Expected a tensor stage" ++ context rest
      | otherwise = Right (Stage (reverse acc) False, rest)

    isStageTok (TokIdent _) = True
    isStageTok (TokInt _)   = True
    isStageTok TokEllipsis  = True
    isStageTok TokLBrack    = True
    isStageTok _            = False

    context []      = " (unexpected end of input)"
    context (t : _) = ", got: " ++ show t

-- Elements of list(…): atoms only, comma-separated.
parseListElems :: [Token] -> Either String ([Term], [Token])
parseListElems (TokRParen : rest) = Right ([], rest)
parseListElems toks = do
  (e, rest) <- elemAtom toks
  case rest of
    (TokComma : rest')  -> do
      (es, rest'') <- parseListElems rest'
      Right (e : es, rest'')
    (TokRParen : rest') -> Right ([e], rest')
    _ -> Left "Expected ',' or ')' in list literal"
  where
    elemAtom (TokIdent name : rest) = Right (Prim name, rest)
    elemAtom (TokInt n : rest)      = Right (Prim (show n), rest)
    elemAtom (TokLBrack : rest)     = do
      (stmt, rest') <- parseStmt rest
      case rest' of
        (TokRBrack : rest'') -> Right (Quote (desugarStmt stmt), rest'')
        _ -> Left "Unclosed quotation (expected ']')"
    elemAtom ts =
      Left $ "Expected a list element" ++
        case ts of
          []      -> " (unexpected end of input)"
          (t : _) -> ", got: " ++ show t

--------------------------------------------------------------------------------
-- 6.2 Desugaring (stages → Term)
--------------------------------------------------------------------------------

-- Append pass as the final atom of a chain (trailing remainder).
appendPassTerm :: Term -> Term
appendPassTerm (Tensor ts) = Tensor (ts ++ [Prim "pass"])
appendPassTerm t           = Tensor [t, Prim "pass"]

tensorChain :: [Term] -> Term
tensorChain []  = Prim "pass"
tensorChain [t] = t
tensorChain ts  = Tensor ts

desugarStage :: Stage -> Term
desugarStage (Stage atoms hasPass) =
  let base = tensorChain atoms
  in if hasPass then appendPassTerm base else base

-- `>>>` opens only the immediately preceding tensor stage, never the
-- accumulated program:  a >> b >>> c  ≡  a >> (b pass) >> c.
desugarStmt :: Stmt -> Term
desugarStmt (Stmt firstStage rest) =
  let stages    = firstStage : map snd rest
      followOps = map (Just . fst) rest ++ [Nothing]
      desugared = zipWith openIf stages followOps
  in foldl1 Seq desugared
  where
    openIf stage (Just StageSeqPass) = appendPassTerm (desugarStage stage)
    openIf stage _                   = desugarStage stage

--------------------------------------------------------------------------------
-- 6.3 Stack append and inference
--------------------------------------------------------------------------------

-- Append two stacks, front first.  Total under the remainder discipline:
-- every non-final tensor operand is instantiated closed, so the front
-- stack always ends in SEnd.  An open front is an internal invariant
-- violation, not a user-facing type error.
appendStack :: SType -> SType -> SType
appendStack SEnd s2           = s2
appendStack (SCons t rest) s2 = SCons t (appendStack rest s2)
appendStack (STail v) _ =
  error $ "appendStack: open stack " ++ show v
       ++ " in non-final tensor position (remainder discipline violation)"

-- Inference: given an Env and a Term, produce an Arrow and constraints
infer :: Env -> Term -> Infer (Arrow, [Constraint])
infer env p@(Prim _)    = inferOperand env True p
infer env q@(Quote _)   = inferOperand env True q
infer env l@(ListLit _) = inferOperand env True l

infer env (Tensor ts) = do
  let n = length ts
  results <- sequence
    [ inferOperand env (ix == n - 1) t | (ix, t) <- zip [0 ..] ts ]
  let arrows = map fst results
      cs     = concatMap snd results
      inS    = foldr1 appendStack [ i | Arrow i _ <- arrows ]
      outS   = foldr1 appendStack [ o | Arrow _ o <- arrows ]
  pure (Arrow inS outS, cs)

infer env (Seq t u) = do
  (Arrow i1 o1, c1) <- infer env t
  (Arrow i2 o2, c2) <- infer env u
  let c = CEqStack o1 i2
  pure (Arrow i1 o2, c1 ++ c2 ++ [c])

-- Infer one operand of a tensor chain.  Only the final operand may keep
-- its remainder variable open; all earlier operands are closed (ρ := •).
inferOperand :: Env -> Bool -> Term -> Infer (Arrow, [Constraint])
inferOperand env final (Prim name)
  | isIntLiteral name = pick intLitScheme
  | otherwise =
      case M.lookup name env of
        Nothing ->
          -- inferProgram pre-checks names, so this is unreachable from
          -- the driver; kept as a guard for direct calls.
          error $ "Unknown primitive: " ++ name
        Just sc -> pick sc
  where
    pick sc = do
      arr <- if final then instantiate sc else instantiateClosed sc
      pure (arr, [])
inferOperand env final (ListLit es) = do
  -- Each element must be a pure push: • ⇒ A, all at the same A.
  elemTy <- TVarTy <$> freshTyVarName
  results <- mapM (inferOperand env False) es
  let cs = concat
        [ CEqStack i SEnd
            : CEqStack o (SCons elemTy SEnd)
            : csE
        | (Arrow i o, csE) <- results ]
      listTy = TList elemTy
  if final
    then do
      v <- freshSVarName
      let r = STail v
      pure (Arrow r (SCons listTy r), cs)
    else
      pure (Arrow SEnd (SCons listTy SEnd), cs)
inferOperand env final (Quote p) = do
  -- The quoted program is inferred as a whole; its remainder variables
  -- stay as metavariables inside Code⟨…⟩, solved (monomorphically) at
  -- the use site.  The quote itself pushes exactly one value.
  (arrP, cs) <- infer env p
  let code = TCode arrP
  if final
    then do
      v <- freshSVarName
      let r = STail v
      pure (Arrow r (SCons code r), cs)
    else
      pure (Arrow SEnd (SCons code SEnd), cs)
inferOperand env final t
  | final     = infer env t
  | otherwise =
      -- The parser only produces atoms (Prim/Quote) inside tensor chains.
      error $ "Non-final tensor operand must be an atom: " ++ show t

isIntLiteral :: String -> Bool
isIntLiteral name = not (null name) && all isDigit name

-- Integer literals: ∀ρ. ρ ⇒ Int ρ
intLitScheme :: Scheme
intLitScheme =
  let rho = SV "ρ"
      r   = STail rho
  in Forall [] [rho] (Arrow r (SCons TInt r))

--------------------------------------------------------------------------------
-- 7. The primitive environment (remainder ρ always trailing)
--------------------------------------------------------------------------------

--  id    : ∀ρ A. A ρ ⇒ A ρ
--  swap  : ∀ρ A B. A B ρ ⇒ B A ρ
--  dup   : ∀ρ A. A ρ ⇒ A A ρ
--  drop  : ∀ρ A. A ρ ⇒ ρ
--  pass  : ∀ρ. ρ ⇒ ρ
--  f, g  : ∀ρ. Int ρ ⇒ Int ρ
--  +, *  : ∀ρ. Int Int ρ ⇒ Int ρ
--  print : ∀ρ A. A ρ ⇒ ρ
--  true, false : ∀ρ. ρ ⇒ Bool ρ
--  apply : ∀Γ Δ. Code⟨Γ ⇒ Δ⟩ Γ ⇒ Δ   (quotation on the first wire; the
--          consumed segment Γ is the tail, per the remainder discipline)
--  (integer literals are handled by rule: ∀ρ. ρ ⇒ Int ρ)
primEnv :: Env
primEnv =
  let rho = SV "ρ"
      r   = STail rho
      a   = TV "A"
      b   = TV "B"
      ta  = TVarTy a
      tb  = TVarTy b
      gam = SV "Γ"
      del = SV "Δ"
      codeGD = TCode (Arrow (STail gam) (STail del))
      applyTy = Forall [] [gam, del]
        (Arrow (SCons codeGD (STail gam)) (STail del))
      -- branch : Bool Code⟨Γ⇒Δ⟩ Code⟨Γ⇒Δ⟩ Γ ⇒ Δ (true-quotation first)
      branchTy = Forall [] [gam, del]
        (Arrow (SCons TBool (SCons codeGD (SCons codeGD (STail gam))))
               (STail del))
      -- map : Code⟨A ⇒ B⟩ List A ρ ⇒ List B ρ
      mapTy = Forall [a, b] [rho]
        (Arrow (SCons (TCode (Arrow (SCons ta SEnd) (SCons tb SEnd)))
                 (SCons (TList ta) r))
               (SCons (TList tb) r))
      -- fold : Code⟨B A ⇒ B⟩ B List A ρ ⇒ B ρ
      foldTy = Forall [a, b] [rho]
        (Arrow (SCons (TCode (Arrow (SCons tb (SCons ta SEnd))
                                    (SCons tb SEnd)))
                 (SCons tb (SCons (TList ta) r)))
               (SCons tb r))
      unaryTy  = Forall [] [rho] (Arrow (SCons TInt r) (SCons TInt r))
      binIntTy = Forall [] [rho]
        (Arrow (SCons TInt (SCons TInt r)) (SCons TInt r))
      boolLit  = Forall [] [rho] (Arrow r (SCons TBool r))
  in M.fromList
       [ ("id",    Forall [a]    [rho] (Arrow (SCons ta r) (SCons ta r)))
       , ("swap",  Forall [a, b] [rho]
           (Arrow (SCons ta (SCons tb r)) (SCons tb (SCons ta r))))
       , ("dup",   Forall [a]    [rho] (Arrow (SCons ta r) (SCons ta (SCons ta r))))
       , ("drop",  Forall [a]    [rho] (Arrow (SCons ta r) r))
       , ("pass",  Forall []     [rho] (Arrow r r))
       , ("f",     unaryTy)
       , ("g",     unaryTy)
       , ("+",     binIntTy)
       , ("*",     binIntTy)
       , ("print", Forall [a]    [rho] (Arrow (SCons ta r) r))
       , ("true",  boolLit)
       , ("false", boolLit)
       , ("negative?", Forall [] [rho] (Arrow (SCons TInt r) (SCons TBool r)))
       , ("apply",  applyTy)
       , ("branch", branchTy)
       , ("map",    mapTy)
       , ("fold",   foldTy)
       ]

--------------------------------------------------------------------------------
-- 8. Driver: parse + infer + solve
--------------------------------------------------------------------------------

primsIn :: Term -> [String]
primsIn (Prim n)      = [n]
primsIn (Tensor ts)   = concatMap primsIn ts
primsIn (Seq t u)     = primsIn t ++ primsIn u
primsIn (Quote t)     = primsIn t
primsIn (ListLit es)  = concatMap primsIn es

-- Infer a term's principal arrow in a given environment.
inferTermIn :: Env -> Term -> Either String Arrow
inferTermIn env term =
  case nub [ n | n <- primsIn term
               , not (isIntLiteral n)
               , not (M.member n env) ] of
    (n : _) -> Left $ "Unknown primitive: " ++ n
    [] -> do
      let (arr, cs) = runInfer0 (infer env term)
      s <- solve cs
      pure (apply s arr)

inferProgram :: String -> Either String Arrow
inferProgram src = do
  term <- parseProgram src
  inferTermIn primEnv term

exampleSrc :: String
exampleSrc = "1 2 >> f g >> + >> print"

inferExample :: Either String Arrow
inferExample = inferProgram exampleSrc

prettyInferExample :: IO ()
prettyInferExample =
  case inferExample of
    Left err ->
      putStrLn $ "Type error: " ++ err
    Right arr ->
      putStrLn $ "exampleTerm : " ++ show arr

--------------------------------------------------------------------------------
-- 9. Alpha-normalization (for stable test expectations)
--------------------------------------------------------------------------------

-- Rename variables to a0, a1, … / ρ0, ρ1, … in order of first appearance
-- (a simultaneous rename, so substOnce is exactly the right applicator).
normalizeArrow :: Arrow -> Arrow
normalizeArrow arr =
  let (tvs, svs) = varsOfArrow arr
      tm = M.fromList
             (zip tvs [ TVarTy (TV ("a" ++ show n)) | n <- [0 :: Int ..] ])
      sm = M.fromList
             (zip svs [ STail (SV ("ρ" ++ show n)) | n <- [0 :: Int ..] ])
  in substOnce (Subst tm sm) arr

-- Infer and alpha-normalize; the workhorse for tests.
inferNormalized :: String -> Either String Arrow
inferNormalized = fmap normalizeArrow . inferProgram

--------------------------------------------------------------------------------
-- 10. Definitions (def name = program) with let-polymorphism
--------------------------------------------------------------------------------

-- Every variable in a bare arrow is free.
freeVarsArrow :: Arrow -> ([TVar], [SVar])
freeVarsArrow = varsOfArrow

freeVarsScheme :: Scheme -> ([TVar], [SVar])
freeVarsScheme (Forall tv sv arr) =
  let (ft, fs) = freeVarsArrow arr
  in (ft \\ tv, fs \\ sv)

freeVarsEnv :: Env -> ([TVar], [SVar])
freeVarsEnv env =
  let pairs = map freeVarsScheme (M.elems env)
  in (nub (concatMap fst pairs), nub (concatMap snd pairs))

-- Generalize all free type & stack variables not fixed by the environment.
generalize :: Env -> Arrow -> Scheme
generalize env arr =
  let (ftv, fsv) = freeVarsArrow arr
      (etv, esv) = freeVarsEnv env
  in Forall (ftv \\ etv) (fsv \\ esv) arr

-- A checked module: definitions in order, plus an optional main program.
data Module = Module
  { modEnv  :: Env
  , modDefs :: [(String, Scheme, Term)]
  , modMain :: Maybe (Term, Arrow)
  }

-- Split source into `def name = body` lines and the main program
-- (all remaining lines, in order, joined by newline-sequencing).
splitDefs :: String -> Either String ([(String, String)], String)
splitDefs src = do
  (defs, progLines) <- go (lines src)
  pure (defs, intercalate "\n" progLines)
  where
    go [] = Right ([], [])
    go (l : rest)
      | ("def" : _) <- words l = do
          (name, body) <- parseDefLine l
          (ds, ps) <- go rest
          pure ((name, body) : ds, ps)
      | otherwise = do
          (ds, ps) <- go rest
          pure (ds, l : ps)

    parseDefLine l =
      case break (== '=') l of
        (lhs, '=' : body) ->
          case words lhs of
            ["def", name]
              | not (isIntLiteral name) -> Right (name, body)
            _ -> Left $ "Malformed definition: " ++ l
        _ -> Left $ "Malformed definition (missing '='): " ++ l

checkModule :: String -> Either String Module
checkModule src = do
  (defSrcs, mainSrc) <- splitDefs src
  (env', defsRev) <- foldM addDef (primEnv, []) defSrcs
  mainPart <-
    if all isSpace mainSrc
      then pure Nothing
      else do
        term <- parseProgram mainSrc
        arr  <- inferTermIn env' term
        pure (Just (term, arr))
  pure (Module env' (reverse defsRev) mainPart)
  where
    addDef (env, acc) (name, bodySrc) = do
      if M.member name env
        then Left $ "Duplicate definition: " ++ name
        else Right ()
      term <- parseProgram bodySrc
      arr  <- inferTermIn env term
      let sc = generalize env arr
      pure (M.insert name sc env, (name, sc, term) : acc)

--------------------------------------------------------------------------------
-- 11. Interpreter
--
-- Runtime stack is a list of values, front (leftmost wire) first.  Block
-- splitting is arity-directed: each atom consumes the closed prefix of
-- its input type from the front; the leftover (the open remainder) flows
-- through and is appended after all atom outputs, matching
-- Γ1 … Γn ρ ⇒ Δ1 … Δn ρ.
--------------------------------------------------------------------------------

data Value = VInt Int | VBool Bool | VCode Term | VList [Value]
  deriving (Eq)

instance Show Value where
  show (VInt n)      = show n
  show (VBool True)  = "true"
  show (VBool False) = "false"
  show (VCode _)     = "[code]"
  show (VList vs)    = "list(" ++ intercalate ", " (map show vs) ++ ")"

-- Number of concrete wires in a stack type (its closed prefix).
closedArity :: SType -> Int
closedArity (SCons _ rest) = 1 + closedArity rest
closedArity _              = 0

type RunDefs = Map String (Int, Term)   -- name -> (input arity, body)

moduleRunDefs :: Module -> RunDefs
moduleRunDefs m =
  M.fromList
    [ (name, (arityOf sc, term)) | (name, sc, term) <- modDefs m ]
  where
    arityOf (Forall _ _ (Arrow i _)) = closedArity i

-- Evaluate a term: returns the final stack and the print log.
evalTerm :: RunDefs -> Term -> [Value] -> Either String ([Value], [String])
evalTerm defs term st =
  case term of
    Seq t u -> do
      (st1, l1) <- evalTerm defs t st
      (st2, l2) <- evalTerm defs u st1
      pure (st2, l1 ++ l2)
    Tensor ts     -> goAtoms ts st
    p@(Prim _)    -> goAtoms [p] st
    q@(Quote _)   -> goAtoms [q] st
    l@(ListLit _) -> goAtoms [l] st
  where
    goAtoms [] stk = Right (stk, [])   -- leftover remainder flows through last
    goAtoms (a : more) stk = do
      (out, stk', logs) <- applyAtom (null more) a stk
      (outRest, logs') <- goAtoms more stk'
      pure (out ++ outRest, logs ++ logs')

    -- apply is special: its Γ is the stack segment after the code value.
    -- As the final atom that segment is the whole remaining stack; as a
    -- non-final atom it was closed to • by the typechecker.
    applyAtom isFinal (Prim "apply") stk = do
      (args, stk') <- takeWires "apply" 1 stk
      case args of
        [VCode body] -> do
          let seg = if isFinal then stk' else []
          (out, logs) <- evalTerm defs body seg
          pure (out, if isFinal then [] else stk', logs)
        _ ->
          Left "Runtime type error in apply: expected a quotation"
    -- branch has the same segment semantics as apply: Γ is the stack
    -- after the three control wires.
    applyAtom isFinal (Prim "branch") stk = do
      (args, stk') <- takeWires "branch" 3 stk
      case args of
        [VBool c, VCode tThen, VCode tElse] -> do
          let seg = if isFinal then stk' else []
          (out, logs) <- evalTerm defs (if c then tThen else tElse) seg
          pure (out, if isFinal then [] else stk', logs)
        _ ->
          Left "Runtime type error in branch: expected Bool and two quotations"
    applyAtom _ (Prim name) stk
      | isIntLiteral name = Right ([VInt (read name)], stk, [])
      | Just (k, body) <- M.lookup name defs = do
          (args, stk') <- takeWires name k stk
          (out, logs) <- evalTerm defs body args
          pure (out, stk', logs)
      | otherwise = do
          k <- builtinArity name
          (args, stk') <- takeWires name k stk
          (out, logs) <- runBuiltin defs name args
          pure (out, stk', logs)
    applyAtom _ (Quote body) stk = Right ([VCode body], stk, [])
    applyAtom _ (ListLit es) stk = do
      vs <- mapM elemValue es
      pure ([VList vs], stk, [])
      where
        elemValue e = do
          (out, _) <- evalTerm defs e []
          case out of
            [v] -> Right v
            _   -> Left "list element must push exactly one value"
    applyAtom _ t' _ =
      Left $ "Cannot evaluate non-atomic tensor operand: " ++ show t'

    takeWires name k stk
      | length stk >= k = Right (take k stk, drop k stk)
      | otherwise =
          Left $ "Runtime stack underflow in " ++ name
               ++ " (unreachable on typechecked programs)"

builtinArity :: String -> Either String Int
builtinArity name =
  case M.lookup name primEnv of
    Just (Forall _ _ (Arrow i _)) -> Right (closedArity i)
    Nothing -> Left $ "Unknown primitive at runtime: " ++ name

runBuiltin :: RunDefs -> String -> [Value] -> Either String ([Value], [String])
runBuiltin _ "id"    [v]              = Right ([v], [])
runBuiltin _ "swap"  [x, y]           = Right ([y, x], [])
runBuiltin _ "dup"   [v]              = Right ([v, v], [])
runBuiltin _ "drop"  [_]              = Right ([], [])
runBuiltin _ "pass"  []               = Right ([], [])
runBuiltin _ "f"     [VInt n]         = Right ([VInt (n + 1)], [])   -- sample unary: successor
runBuiltin _ "g"     [VInt n]         = Right ([VInt (2 * n)], [])   -- sample unary: double
runBuiltin _ "+"     [VInt x, VInt y] = Right ([VInt (x + y)], [])
runBuiltin _ "*"     [VInt x, VInt y] = Right ([VInt (x * y)], [])
runBuiltin _ "print" [v]              = Right ([], [show v])
runBuiltin _ "true"  []               = Right ([VBool True], [])
runBuiltin _ "false" []               = Right ([VBool False], [])
runBuiltin _ "negative?" [VInt n]     = Right ([VBool (n < 0)], [])
runBuiltin defs "map" [VCode t, VList vs] = do
  rs <- mapM step vs
  pure ([VList (map fst rs)], concatMap snd rs)
  where
    step v = do
      (out, logs) <- evalTerm defs t [v]
      case out of
        [r] -> Right (r, logs)
        _   -> Left "map: code must return exactly one value"
runBuiltin defs "fold" [VCode t, b0, VList vs] = do
  (b, logs) <- foldM step (b0, []) vs
  pure ([b], logs)
  where
    step (b, logs) v = do
      (out, logs') <- evalTerm defs t [b, v]
      case out of
        [b'] -> Right (b', logs ++ logs')
        _    -> Left "fold: code must return exactly one value"
runBuiltin _ name args =
  Left $ "Runtime type error in " ++ name ++ " applied to "
       ++ show args ++ " (unreachable on typechecked programs)"

-- Typecheck and run a whole module; main runs on the empty stack.
runModule :: String -> Either String ([Value], [String])
runModule src = do
  m <- checkModule src
  case modMain m of
    Nothing -> Right ([], [])
    Just (term, arr@(Arrow i _))
      | closedArity i > 0 ->
          Left $ "main requires a nonempty input stack: " ++ show arr
      | otherwise -> evalTerm (moduleRunDefs m) term []
