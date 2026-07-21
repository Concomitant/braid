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

-- Alternatives-row variables (σ): the tail of a sum's alternative list.
-- Same tail-only discipline as stack variables, one level up.
newtype RVar = RV String
  deriving (Eq, Ord)

instance Show RVar where
  show (RV s) = s

-- Element types.  TFn nests whole arrows inside element types, so
-- stack variables can occur inside types — all traversals (occurs
-- checks, substitution, unification) must recurse through it.
data Ty
  = TVarTy TVar
  | TInt
  | TFn Arrow          -- Fn⟨Γ ⇒ Δ⟩: a reified program
  | TList Ty           -- List A: homogeneous list
  | TSum SumRow        -- (Δ₁ | … | Δₙ [| σ]): sum of stacks, one wire
  deriving (Eq, Ord)

-- A sum's alternatives: a row of stacks with an optional row-variable
-- tail.  Rigid (no flattening, no reassociation): nesting is only ever
-- what was written.
data SumRow
  = RNil               -- closed end
  | RTail RVar         -- open end: alternatives-row variable σ
  | RCons SType SumRow -- one alternative (a whole stack), then the rest
  deriving (Eq, Ord)

instance Show SumRow where
  show row = intercalate " | " (go row)
    where
      go RNil           = []
      go (RTail v)      = [show v]
      go (RCons st rest) = show st : go rest

instance Show Ty where
  show (TVarTy a)  = show a
  show TInt        = "Int"
  show (TFn arr) = "Fn⟨" ++ show arr ++ "⟩"
  show (TList t)   = "List " ++ parens t
    where
      parens u@(TList _) = "(" ++ show u ++ ")"
      parens u@(TSum _)  = show u   -- already parenthesized
      parens u           = show u
  show (TSum row)  = "(" ++ show row ++ ")"

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

data Scheme = Forall [TVar] [SVar] [RVar] Arrow
  deriving (Eq, Ord)

instance Show Scheme where
  show (Forall tvars svars rvars arr) =
    "∀ " ++ unwords (map show tvars ++ map show svars ++ map show rvars)
         ++ ". " ++ show arr

type Env = Map String Scheme

--------------------------------------------------------------------------------
-- 3. Substitutions and "apply"
--------------------------------------------------------------------------------

data Subst = Subst
  { tySub  :: Map TVar Ty
  , stSub  :: Map SVar SType
  , rowSub :: Map RVar SumRow
  } deriving (Eq, Show)

emptySubst :: Subst
emptySubst = Subst M.empty M.empty M.empty

-- composeSubst s2 s1 = apply s2 after s1
composeSubst :: Subst -> Subst -> Subst
composeSubst s2 s1 =
  Subst
    { tySub  = M.map (apply s2) (tySub s1) `M.union` tySub s2
    , stSub  = M.map (apply s2) (stSub s1) `M.union` stSub s2
    , rowSub = M.map (apply s2) (rowSub s1) `M.union` rowSub s2
    }

class Substitutable a where
  apply :: Subst -> a -> a

instance Substitutable Ty where
  apply s t@(TVarTy v) =
    case M.lookup v (tySub s) of
      Nothing -> t
      Just t' -> apply s t'   -- chase chains, like the SType instance
  apply _ TInt        = TInt
  apply s (TFn arr) = TFn (apply s arr)
  apply s (TList t)   = TList (apply s t)
  apply s (TSum row)  = TSum (apply s row)

instance Substitutable SType where
  apply _ SEnd = SEnd
  apply s st@(STail v) =
    case M.lookup v (stSub s) of
      Nothing  -> st
      Just st' -> apply s st'
  apply s (SCons ty rest) = SCons (apply s ty) (apply s rest)

instance Substitutable SumRow where
  apply _ RNil = RNil
  apply s r@(RTail v) =
    case M.lookup v (rowSub s) of
      Nothing -> r
      Just r' -> apply s r'
  apply s (RCons st rest) = RCons (apply s st) (apply s rest)

instance Substitutable Arrow where
  apply s (Arrow i o) = Arrow (apply s i) (apply s o)

instance Substitutable Scheme where
  -- Bound variables are removed from the substitution before it touches
  -- the arrow, so quantified names are never captured.
  apply s (Forall tv sv rv arr) =
    let s' = Subst (foldr M.delete (tySub s) tv)
                   (foldr M.delete (stSub s) sv)
                   (foldr M.delete (rowSub s) rv)
    in Forall tv sv rv (apply s' arr)

instance Substitutable Env where
  apply s = M.map (apply s)

--------------------------------------------------------------------------------
-- 4. Constraints and unification
--------------------------------------------------------------------------------

data Constraint
  = CEqTy Ty Ty
  | CEqStack SType SType
  deriving (Eq, Show)

-- All variables (type, stack, row) in order of first appearance,
-- recursing through Fn⟨Γ ⇒ Δ⟩ and (… | …) element types.  The single
-- traversal backing occurs checks, generalization, and normalization.
type Vars = ([TVar], [SVar], [RVar])

varsOfTy :: Ty -> Vars
varsOfTy (TVarTy v)  = ([v], [], [])
varsOfTy TInt        = ([], [], [])
varsOfTy (TFn arr)   = varsOfArrow arr
varsOfTy (TList t)   = varsOfTy t
varsOfTy (TSum row)  = varsOfRow row

varsOfStack :: SType -> Vars
varsOfStack SEnd           = ([], [], [])
varsOfStack (STail v)      = ([], [v], [])
varsOfStack (SCons t rest) = varsOfTy t `catVars` varsOfStack rest

varsOfRow :: SumRow -> Vars
varsOfRow RNil            = ([], [], [])
varsOfRow (RTail v)       = ([], [], [v])
varsOfRow (RCons st rest) = varsOfStack st `catVars` varsOfRow rest

catVars :: Vars -> Vars -> Vars
catVars (t1, s1, r1) (t2, s2, r2) = (t1 ++ t2, s1 ++ s2, r1 ++ r2)

varsOfArrow :: Arrow -> Vars
varsOfArrow (Arrow i o) =
  let (ts, ss, rs) = varsOfStack i `catVars` varsOfStack o
  in (nub ts, nub ss, nub rs)

-- Occurs checks.  Callers (bind*Var) only ever check against
-- fully-applied targets, so a pure structural traversal is sufficient.
occursTy :: TVar -> Ty -> Bool
occursTy a t = let (ts, _, _) = varsOfTy t in a `elem` ts

occursStack :: SVar -> SType -> Bool
occursStack v st = let (_, ss, _) = varsOfStack st in v `elem` ss

occursRow :: RVar -> SumRow -> Bool
occursRow v row = let (_, _, rs) = varsOfRow row in v `elem` rs

-- Unify simple element types
unifyTy :: Subst -> Ty -> Ty -> Either String Subst
unifyTy s t1 t2 =
  let t1' = apply s t1
      t2' = apply s t2
  in case (t1', t2') of
    (TVarTy a, t) -> bindTyVar s a t
    (t, TVarTy a) -> bindTyVar s a t
    (TInt, TInt)  -> Right s
    (TFn (Arrow i1 o1), TFn (Arrow i2 o2)) -> do
      s' <- unifyStack s i1 i2
      unifyStack s' o1 o2
    (TList a1, TList a2) -> unifyTy s a1 a2
    (TSum r1, TSum r2)   -> unifyRow s r1 r2
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

-- Unify sum alternative rows (list unification with an optional row
-- tail — the stack discipline, one level up).  Arity is rigid.
unifyRow :: Subst -> SumRow -> SumRow -> Either String Subst
unifyRow s r1 r2 =
  let r1' = apply s r1
      r2' = apply s r2
  in case (r1', r2') of
    (RNil, RNil) -> Right s
    (RTail v, r) -> bindRowVar s v r
    (r, RTail v) -> bindRowVar s v r
    (RCons st1 rest1, RCons st2 rest2) -> do
      s' <- unifyStack s st1 st2
      unifyRow s' rest1 rest2
    _ -> Left $ "Cannot unify sum alternatives: (" ++ show r1'
              ++ ") vs (" ++ show r2' ++ ")"

bindRowVar :: Subst -> RVar -> SumRow -> Either String Subst
bindRowVar s v row
  | row == RTail v = Right s
  | occursRow v row =
      Left $ "Occurs check failed on sum row: " ++ show v ++ " in " ++ show row
  | otherwise = Right s { rowSub = M.insert v row (rowSub s) }

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

freshRVarName :: Infer RVar
freshRVarName = Infer $ do
  n <- get
  put (n + 1)
  pure (RV ("σ" ++ show n))

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
    goT (TFn arr)  = TFn (substOnce s arr)
    goT (TList t)    = TList (goT t)
    goT (TSum row)   = TSum (goR row)
    goT t            = t

    goR RNil = RNil
    goR row@(RTail v) = fromMaybe row (M.lookup v (rowSub s))
    goR (RCons st rest) = RCons (goS st) (goR rest)

-- Instantiate a polymorphic scheme with fresh type, stack, and row
-- variables (used for the final atom of a tensor chain, which may stay
-- open).
instantiate :: Scheme -> Infer Arrow
instantiate (Forall tvars svars rvars arr) = do
  newTVs <- mapM (const freshTyVarName) tvars
  newSVs <- mapM (const freshSVarName) svars
  newRVs <- mapM (const freshRVarName) rvars
  let tSub = M.fromList (zip tvars (map TVarTy newTVs))
      sSub = M.fromList (zip svars (map STail newSVs))
      rSub = M.fromList (zip rvars (map RTail newRVs))
  pure (substOnce (Subst tSub sSub rSub) arr)

-- Instantiate a scheme *closed* for a non-final tensor atom: only the
-- OUTER TAILS of the arrow are closed (ρ := •) — that is all appendStack
-- needs.  Variables living purely inside element types (Fn⟨…⟩, sums)
-- are freshened like any instantiation: they are the atom's
-- polymorphism, not a remainder.  (Matches the grouped-compound closing
-- policy.)
instantiateClosed :: Scheme -> Infer Arrow
instantiateClosed (Forall tvars svars rvars arr@(Arrow i o)) = do
  newTVs <- mapM (const freshTyVarName) tvars
  let tailVs = [ v | Just v <- [tailVar i, tailVar o] ]
  newSVs <- mapM (\v -> if v `elem` tailVs
                          then pure Nothing
                          else Just <$> freshSVarName) svars
  newRVs <- mapM (const freshRVarName) rvars
  let tSub = M.fromList (zip tvars (map TVarTy newTVs))
      sSub = M.fromList [ (v, maybe SEnd STail mn)
                        | (v, mn) <- zip svars newSVs ]
      rSub = M.fromList (zip rvars (map RTail newRVs))
  pure (substOnce (Subst tSub sSub rSub) arr)

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
  | OpenAbs [String] Term -- (x y -> body): open program with named input
                          -- wires; the body is input-closed (all input
                          -- arrives through the parameters)
  | Alts [Term] Bool      -- (p₁ | … | pₙ [| ...]): code row — the sum
                          -- functor action; one component per
                          -- alternative, residual flag = identity on
                          -- the remaining alternatives
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
  | TokLParen     -- ( (grouping / list literal)
  | TokRParen     -- )
  | TokComma      -- ,
  | TokArrow      -- -> (parameter list separator)
  | TokBar        -- | (code-row / sum alternative separator)
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
    go ('…':cs)         = (TokEllipsis :) <$> go cs   -- U+2026, autocorrect's ...
    go ('.':_)          = Left "Unexpected '.' (did you mean '...'?)"
    go ('[':cs)         = (TokLBrack :) <$> go cs
    go (']':cs)         = (TokRBrack :) <$> go cs
    go ('(':cs)         = (TokLParen :) <$> go cs
    go (')':cs)         = (TokRParen :) <$> go cs
    go (',':cs)         = (TokComma :) <$> go cs
    go ('-':'>':cs)     = (TokArrow :) <$> go cs
    go ('-':cs)         = (TokIdent "-" :) <$> go cs   -- subtraction
    go ('|':cs)         = (TokBar :) <$> go cs
    go (c:cs)
      | isSpace c = go cs
      | isDigit c =
          let (digits, rest) = span isDigit (c:cs)
          in (TokInt (read digits) :) <$> go rest
      | otherwise =
          let (ident, rest) = span isIdentChar (c:cs)
          in (TokIdent ident :) <$> go rest

    isIdentChar ch =
      not (isSpace ch) && ch `notElem` (">.[](),-|\8230" :: String)

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

    isSeqOp t = t == TokSeq || t == TokSeqPass || t == TokBar

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

-- Precedence, loosest to tightest: newline (strict >>), then | (code
-- row), then >> / >>>, then juxtaposition.  So each LINE is a row, and
-- `a >> b | c >> d` is (a >> b) | (c >> d) — mirroring the type grammar,
-- where juxtaposition binds tighter than |.
parseProgram :: String -> Either String Term
parseProgram input = do
  toks <- normalizeToks <$> tokenize input
  (term, rest) <- parseProgramToks toks
  case rest of
    [] -> Right term
    _  -> Left $ "Unexpected tokens at end: " ++ show rest

-- program level: rows joined by newline
parseProgramToks :: [Token] -> Either String (Term, [Token])
parseProgramToks toks = do
  (t0, rest) <- parseRow toks
  loop t0 rest
  where
    loop acc (TokNewline : rest) = do
      (t, rest') <- parseRow rest
      loop (Seq acc t) rest'
    loop acc rest = Right (acc, rest)

-- row level: sequences joined by |, optional trailing `| ...` residual
parseRow :: [Token] -> Either String (Term, [Token])
parseRow toks = do
  (s0, rest) <- parseSeqStmt toks
  loop [desugarStmt s0] rest
  where
    loop acc (TokBar : TokEllipsis : rest)
      | endsRow rest = Right (Alts (reverse acc) True, rest)
      | otherwise    = Left "'| ...' must end its row"
    loop acc (TokBar : rest) = do
      (s, rest') <- parseSeqStmt rest
      loop (desugarStmt s : acc) rest'
    loop [t] rest = Right (t, rest)
    loop acc rest = Right (Alts (reverse acc) False, rest)

    endsRow (TokNewline : _) = True
    endsRow (TokRParen : _)  = True
    endsRow (TokRBrack : _)  = True
    endsRow []               = True
    endsRow _                = False

-- sequence level: stages joined by >> / >>> only
parseSeqStmt :: [Token] -> Either String (Stmt, [Token])
parseSeqStmt toks = do
  (s0, rest) <- parseStage toks
  (ops, rest') <- go [] rest
  Right (Stmt s0 ops, rest')
  where
    go acc (TokSeq : rest')     = next acc StageSeq rest'
    go acc (TokSeqPass : rest') = next acc StageSeqPass rest'
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
    -- [p] reifies; [x y -> p] is shorthand for [(x y -> p)]
    go acc (TokLBrack : rest)     = do
      (t, rest') <- parseDelimited rest
      case rest' of
        (TokRBrack : rest'') -> go (Quote t : acc) rest''
        _ -> Left "Unclosed quotation (expected ']')"
    -- (p): grouping only — the enclosed program is an ordinary atom,
    -- not reified.  (x y -> p): named open abstraction.
    go acc (TokLParen : rest)     = do
      (t, rest') <- parseDelimited rest
      case rest' of
        (TokRParen : rest'') -> go (t : acc) rest''
        _ -> Left "Unclosed group (expected ')')"
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
    isStageTok TokLParen    = True
    isStageTok _            = False

    context []      = " (unexpected end of input)"
    context (t : _) = ", got: " ++ show t

-- The contents of a ( ) or [ ]: an optional `x y ->` parameter prefix
-- (the arrow is required for parameter introduction — bare idents are a
-- tensor stage), then a full program, possibly a |-separated code row.
-- A 1-ary row is plain grouping.  A trailing `| ...` marks the residual:
-- identity on the remaining alternatives (open row).
parseDelimited :: [Token] -> Either String (Term, [Token])
parseDelimited toks =
  case paramsPrefix [] toks of
    Just (ps, rest) -> do
      case [ p | (p, n) <- zip ps [0 :: Int ..]
               , p `elem` take n ps ] of
        (p : _) -> Left $ "Duplicate parameter: " ++ p
        []      -> Right ()
      (body, rest') <- parseProgramToks rest
      pure (OpenAbs ps body, rest')
    Nothing -> parseProgramToks toks
  where
    paramsPrefix acc (TokIdent n : rest) = paramsPrefix (n : acc) rest
    paramsPrefix acc (TokArrow : rest)   = Just (reverse acc, rest)
    paramsPrefix _   _                   = Nothing

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
      (t, rest') <- parseDelimited rest
      case rest' of
        (TokRBrack : rest'') -> Right (Quote t, rest'')
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
infer env p@(Prim _)     = inferOperand env True p
infer env q@(Quote _)    = inferOperand env True q
infer env l@(ListLit _)  = inferOperand env True l
infer env o@(OpenAbs {}) = inferOperand env True o
infer env a@(Alts {})    = inferOperand env True a

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
  | Just n <- injIndex name, not (M.member name env) = pick (injScheme n)

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
inferOperand env _ (ListLit es) = do
  -- Terminal-source constant: • ⇒ List A.  Each element must be a pure
  -- push (• ⇒ A), all at the same A.
  elemTy <- TVarTy <$> freshTyVarName
  results <- mapM (inferOperand env False) es
  let cs = concat
        [ CEqStack i SEnd
            : CEqStack o (SCons elemTy SEnd)
            : csE
        | (Arrow i o, csE) <- results ]
  pure (Arrow SEnd (SCons (TList elemTy) SEnd), cs)
inferOperand env _ (Quote p) = do
  -- Terminal-source constant: • ⇒ Fn⟨…⟩.  The quoted program is inferred
  -- as a whole; its remainder variables stay as metavariables inside
  -- Fn⟨…⟩, solved (monomorphically) at the use site.
  (arrP, cs) <- infer env p
  pure (Arrow SEnd (SCons (TFn arrP) SEnd), cs)
inferOperand env _ (Alts comps residual) = do
  -- Code row (p₁ | … | pₙ [| ...]): the sum functor action.  A one-wire
  -- atom (Δ-in-sum ⇒ Δ-out-sum); component i maps alternative i,
  -- re-tagging into the same position.  The residual `| ...` shares one
  -- row variable between input and output: identity on the rest.
  results <- mapM (infer env) comps
  end <- if residual then RTail <$> freshRVarName else pure RNil
  let arrows = map fst results
      cs     = concatMap snd results
      inRow  = foldr RCons end [ i | Arrow i _ <- arrows ]
      outRow = foldr RCons end [ o | Arrow _ o <- arrows ]
  pure ( Arrow (SCons (TSum inRow) SEnd) (SCons (TSum outRow) SEnd)
       , cs )
inferOperand env _ (OpenAbs ps body) = do
  -- Named open abstraction (x₁ … xₙ -> body).  Each parameter enters
  -- scope as a monomorphic terminal-source producer xᵢ : • ⇒ Aᵢ — the
  -- free metavariable is shared across occurrences, so repeated use is
  -- forced to one consistent type (λ-binding, HM-style).  The body must
  -- be input-closed: all input arrives through the parameters.  The
  -- abstraction is exact in every position: A₁ … Aₙ ⇒ Δ.
  ptys <- mapM (const freshTyVarName) ps
  let paramScheme av = Forall [] [] [] (Arrow SEnd (SCons (TVarTy av) SEnd))
      env' = foldr (\(p, av) -> M.insert p (paramScheme av))
                   env (zip ps ptys)
  (Arrow bi bo, cs) <- infer env' body
  let inS = foldr (SCons . TVarTy) SEnd ptys
  pure (Arrow inS bo, CEqStack bi SEnd : cs)
inferOperand env final t
  | final     = infer env t
  | otherwise = do
      -- A grouped compound program in closed (non-final) position.  Its
      -- closedness is semantic, not syntactic, so: solve its constraints
      -- locally, then close the OUTER tails of the solved arrow (ρ := •).
      -- Sound because after solving, those tails are unconstrained free
      -- variables — e.g. (pass >> drop) solves to A ρ ⇒ ρ and closes to
      -- A ⇒ •.  Element-internal variables (inside Fn⟨…⟩) stay open,
      -- matching how closed quote operands behave.
      (arr, cs) <- infer env t
      case solve cs of
        Left _ ->
          -- Ill-typed subprogram: emit a dummy closed arrow so appendStack
          -- stays total; the constraints flow up and the global solve
          -- reports the real error.
          pure (Arrow SEnd SEnd, cs)
        Right s ->
          let arr'@(Arrow i o) = apply s arr
              tails = nub ([ v | Just v <- [tailVar i] ]
                        ++ [ v | Just v <- [tailVar o] ])
              sm = M.fromList [ (v, SEnd) | v <- tails ]
          in pure (substOnce (Subst M.empty sm M.empty) arr', [])

-- The tail variable of a stack, if it is open.
tailVar :: SType -> Maybe SVar
tailVar (STail v)    = Just v
tailVar (SCons _ r)  = tailVar r
tailVar SEnd         = Nothing

isIntLiteral :: String -> Bool
isIntLiteral name = not (null name) && all isDigit name

-- The lexical injection family: in1, in2, … — position fixed, width
-- open via the row tail.
injIndex :: String -> Maybe Int
injIndex "here"  = Just 1         -- here ≡ in1: start a sum at the front
injIndex "again" = Just 1         -- loop protocol: continue with new state
injIndex "done"  = Just 2         -- loop protocol: exit with this result
injIndex ('i':'n':ds)
  | not (null ds), all isDigit ds, n >= 1 = Just n
  where n = read ds
injIndex _ = Nothing

-- inN : ∀ Δ₁…Δₙ σ. Δₙ ⇒ (Δ₁ | … | Δₙ | σ) — bundle the whole input
-- segment, tagged at position N; other alternatives are placeholders.
injScheme :: Int -> Scheme
injScheme n =
  let d   = SV "Δ"
      ps  = [ SV ("Δ" ++ show i) | i <- [1 .. n - 1] ]
      rv  = RV "σ"
      row = foldr (RCons . STail) (RCons (STail d) (RTail rv)) ps
  in Forall [] (ps ++ [d]) [rv]
       (Arrow (STail d) (SCons (TSum row) SEnd))

-- Integer literals are terminal-source: • ⇒ Int.  Constants have NO
-- implicit remainder — pushing onto a nonempty stack requires explicit
-- `...` (e.g. `1 ...` : ρ ⇒ Int ρ).  See spec-update-exponentials.md.
intLitScheme :: Scheme
intLitScheme = Forall [] [] [] (Arrow SEnd (SCons TInt SEnd))

--------------------------------------------------------------------------------
-- 7. The primitive environment
--
-- Everything is exact: operations consume and produce exactly the wires
-- written, constants source from •.  There are NO implicit remainders —
-- the remainder is always explicit (pass / ... / >>>).  A stack variable
-- appears only in `pass` (identity on an unknown remainder) and as the
-- consumed/produced segments Γ, Δ of the higher-order eliminators.
--------------------------------------------------------------------------------

--  id    : ∀A. A ⇒ A
--  swap  : ∀A B. A B ⇒ B A
--  dup   : ∀A. A ⇒ A A
--  drop  : ∀A. A ⇒ •
--  pass  : ∀ρ. ρ ⇒ ρ
--  f, g  : Int ⇒ Int
--  +, *  : Int Int ⇒ Int
--  print : ∀A. A ⇒ •
--  true, false : • ⇒ (• | •)
--  routers (predicates keep and route; hit = track 1):
--    negative?, even?, odd?, zero? : Int ⇒ (Int | Int)
--    lt? : Int Int ⇒ (Int Int | Int Int); eq? : ∀A. A A ⇒ (A A | A A)
--  apply : ∀Γ Δ. Fn⟨Γ ⇒ Δ⟩ Γ ⇒ Δ   (Γ is consumed, not passed)
--  guard machine: if / elif / otherwise / endif; loop (Elgot iteration)
--  map   : ∀A B. Fn⟨A ⇒ B⟩ List A ⇒ List B
--  fold  : ∀A B. Fn⟨B A ⇒ B⟩ B List A ⇒ B
--  (integer literals are handled by rule: • ⇒ Int)
primEnv :: Env
primEnv =
  let rho = SV "ρ"
      a   = TV "A"
      b   = TV "B"
      ta  = TVarTy a
      tb  = TVarTy b
      gam = SV "Γ"
      del = SV "Δ"
      one t = SCons t SEnd
      fnGD = TFn (Arrow (STail gam) (STail del))
      applyTy = Forall [] [gam, del] []
        (Arrow (SCons fnGD (STail gam)) (STail del))
      mapTy = Forall [a, b] [] []
        (Arrow (SCons (TFn (Arrow (one ta) (one tb)))
                 (one (TList ta)))
               (one (TList tb)))
      foldTy = Forall [a, b] [] []
        (Arrow (SCons (TFn (Arrow (SCons tb (one ta)) (one tb)))
                 (SCons tb (one (TList ta))))
               (one tb))
      -- merge : (Θ | Θ) ⇒ Θ — the binary codiagonal ∇
      mergeTy = Forall [] [SV "Θ"] []
        (Arrow (SCons (TSum (RCons (STail (SV "Θ"))
                       (RCons (STail (SV "Θ")) RNil))) SEnd)
               (STail (SV "Θ")))
      -- there : (σ) ⇒ (Δ | σ) — widen a sum with a new front track
      -- (tags shift by one; here ≡ in1, inN ≡ here >> there^(n-1))
      thereTy = Forall [] [SV "Δ"] [RV "σ"]
        (Arrow (SCons (TSum (RTail (RV "σ"))) SEnd)
               (SCons (TSum (RCons (STail (SV "Δ")) (RTail (RV "σ")))) SEnd))
      -- Guard machine (if/elif/otherwise/endif); state (Θ | Σ).
      -- if : Σ ⇒ (Θ | Σ) — entry: the value starts on the residual track
      ifTy =
        let th = SV "Θ"; sg = SV "Σ"
        in Forall [] [th, sg] []
             (Arrow (STail sg)
                    (one (TSum (RCons (STail th)
                          (RCons (STail sg) RNil)))))
      -- elif : (Θ | (Σh|Σm) Fn⟨Σh⇒Θ⟩) ⇒ (Θ | Σm) — fold one clause;
      -- asymmetric routers welcome (pattern-matching clauses)
      elifTy =
        let th = SV "Θ"; sh = SV "Σh"; sm = SV "Σm"
            dec = TSum (RCons (STail sh) (RCons (STail sm) RNil))
            act = TFn (Arrow (STail sh) (STail th))
        in Forall [] [th, sh, sm] []
             (Arrow (one (TSum (RCons (STail th)
                          (RCons (SCons act (one dec)) RNil))))
                    (one (TSum (RCons (STail th)
                          (RCons (STail sm) RNil)))))
      -- otherwise : Σ ⇒ (Σ | ()) — the always-hit router: the unit iso
      -- Σ ≅ Σ+0; its miss track carries the empty sum (uninhabited)
      voidW = one (TSum RNil)
      otherwiseTy =
        let sg = SV "Σ"
        in Forall [] [sg] []
             (Arrow (STail sg)
                    (one (TSum (RCons (STail sg) (RCons voidW RNil)))))
      -- endif : (Θ | (Σ | ()) Fn⟨Σ⇒Θ⟩) ⇒ Θ — fold-and-close; demands the
      -- uninhabited miss track: the otherwise-clause is statically
      -- mandatory.  The dead branch is the absurdity map 0 ⇒ Θ.
      endifTy =
        let th = SV "Θ"; sh = SV "Σ"
            dec = TSum (RCons (STail sh) (RCons voidW RNil))
            act = TFn (Arrow (STail sh) (STail th))
        in Forall [] [th, sh] []
             (Arrow (one (TSum (RCons (STail th)
                          (RCons (SCons act (one dec)) RNil))))
                    (STail th))
      -- loop : Fn⟨Σ ⇒ (Σ | Θ)⟩ Σ ⇒ Θ — Elgot iteration: the body routes
      -- to continue (re-enter) or done (exit)
      loopTy =
        let sg = SV "Σ"; th = SV "Θ"
            body = TFn (Arrow (STail sg)
                     (one (TSum (RCons (STail sg)
                           (RCons (STail th) RNil)))))
        in Forall [] [sg, th] []
             (Arrow (SCons body (STail sg)) (STail th))
      -- routers: predicates keep and route their input (hit = track 1)
      intRouter = Forall [] [] []
        (Arrow (one TInt)
               (one (TSum (RCons (one TInt) (RCons (one TInt) RNil)))))
      int2 = SCons TInt (one TInt)
      int2Router = Forall [] [] []
        (Arrow int2
               (one (TSum (RCons int2 (RCons int2 RNil)))))
      eqTy = Forall [a] [] []
        (let aa = SCons ta (one ta)
         in Arrow aa (one (TSum (RCons aa (RCons aa RNil)))))
      -- uncons : List A ⇒ (• | A List A) — the asymmetric list router
      unconsTy = Forall [a] [] []
        (Arrow (one (TList ta))
               (one (TSum (RCons SEnd
                     (RCons (SCons ta (one (TList ta))) RNil)))))
      unaryTy  = Forall [] [] [] (Arrow (one TInt) (one TInt))
      binIntTy = Forall [] [] []
        (Arrow (SCons TInt (one TInt)) (one TInt))
      -- Bool ≡ (• | •): two payload-free tracks; true = in1, false = in2
      tBool    = TSum (RCons SEnd (RCons SEnd RNil))
      boolLit  = Forall [] [] [] (Arrow SEnd (one tBool))
  in M.fromList
       [ ("id",    Forall [a]    [] [] (Arrow (one ta) (one ta)))
       , ("_",     Forall [a]    [] [] (Arrow (one ta) (one ta)))  -- hole: id
       , ("swap",  Forall [a, b] [] []
           (Arrow (SCons ta (one tb)) (SCons tb (one ta))))
       , ("dup",   Forall [a]    [] [] (Arrow (one ta) (SCons ta (one ta))))
       , ("drop",  Forall [a]    [] [] (Arrow (one ta) SEnd))
       , ("pass",  Forall []     [rho] [] (Arrow (STail rho) (STail rho)))
       , ("f",     unaryTy)
       , ("g",     unaryTy)
       , ("+",     binIntTy)
       , ("*",     binIntTy)
       , ("print", Forall [a]    [] [] (Arrow (one ta) SEnd))
       , ("true",  boolLit)
       , ("false", boolLit)
       , ("negative?", intRouter)
       , ("even?",     intRouter)
       , ("odd?",      intRouter)
       , ("zero?",     intRouter)
       , ("eq?",       eqTy)
       , ("lt?",       int2Router)
       , ("-",         binIntTy)
       , ("apply",     applyTy)
       , ("there",     thereTy)
       , ("merge",     mergeTy)
       , ("if",        ifTy)
       , ("elif",      elifTy)
       , ("otherwise", otherwiseTy)
       , ("endif",     endifTy)
       , ("loop",      loopTy)
       , ("uncons",    unconsTy)
       , ("map",       mapTy)
       , ("fold",      foldTy)
       ]

--------------------------------------------------------------------------------
-- 8. Driver: parse + infer + solve
--------------------------------------------------------------------------------

primsIn :: Term -> [String]
primsIn (Prim n)        = [n]
primsIn (Tensor ts)     = concatMap primsIn ts
primsIn (Seq t u)       = primsIn t ++ primsIn u
primsIn (Quote t)       = primsIn t
primsIn (ListLit es)    = concatMap primsIn es
primsIn (OpenAbs ps t)  = [ n | n <- primsIn t, n `notElem` ps ]
primsIn (Alts comps _)  = concatMap primsIn comps

-- Replace the def-local keyword `recurse` with the def's own name
-- (parse-time, shadow-aware) — anonymous self-reference in def bodies.
substRecurse :: String -> Term -> Term
substRecurse nm = go
  where
    go (Prim "recurse") = Prim nm
    go t@(Prim _)       = t
    go (Tensor ts)      = Tensor (map go ts)
    go (Seq a b)        = Seq (go a) (go b)
    go (Quote t)        = Quote (go t)
    go (ListLit es)     = ListLit (map go es)
    go (Alts cs r)      = Alts (map go cs) r
    go t@(OpenAbs ps b)
      | "recurse" `elem` ps = t
      | otherwise           = OpenAbs ps (go b)

-- Infer a term's principal arrow in a given environment.
inferTermIn :: Env -> Term -> Either String Arrow
inferTermIn env term =
  case nub [ n | n <- primsIn term
               , not (isIntLiteral n)
               , not (M.member n env)
               , Nothing <- [injIndex n] ] of
    (n : _) -> Left $ "Unknown primitive: " ++ n
    [] -> do
      let (arr, cs) = runInfer0 (infer env term)
      s <- solve cs
      pure (apply s arr)

-- Infer a definition body, allowing MONOMORPHIC self-reference: the
-- name is bound at a fresh monomorphic arrow while inferring, the
-- recursive uses share its metavariables (like abstraction parameters),
-- and two constraints tie the knot.  Generalization happens afterwards
-- in the caller.  (Polymorphic recursion is undecidable — not offered.)
inferDefTermIn :: String -> Env -> Term -> Either String Arrow
inferDefTermIn name env term
  | name `notElem` primsIn term = inferTermIn env term
  | otherwise =
      case nub [ n | n <- primsIn term
                   , n /= name
                   , not (isIntLiteral n)
                   , not (M.member n env)
                   , Nothing <- [injIndex n] ] of
        (n : _) -> Left $ "Unknown primitive: " ++ n
        [] -> do
          let (arr, cs) = runInfer0 $ do
                fi <- freshSVarName
                fo <- freshSVarName
                let mono = Forall [] [] []
                             (Arrow (STail fi) (STail fo))
                (a@(Arrow bi bo), cs') <-
                  infer (M.insert name mono env) term
                pure (a, cs' ++ [ CEqStack bi (STail fi)
                                , CEqStack bo (STail fo) ])
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
  let (tvs, svs, rvs) = varsOfArrow arr
      tm = M.fromList
             (zip tvs [ TVarTy (TV ("a" ++ show n)) | n <- [0 :: Int ..] ])
      sm = M.fromList
             (zip svs [ STail (SV ("ρ" ++ show n)) | n <- [0 :: Int ..] ])
      rm = M.fromList
             (zip rvs [ RTail (RV ("σ" ++ show n)) | n <- [0 :: Int ..] ])
  in substOnce (Subst tm sm rm) arr

-- Infer and alpha-normalize; the workhorse for tests.
inferNormalized :: String -> Either String Arrow
inferNormalized = fmap normalizeArrow . inferProgram

--------------------------------------------------------------------------------
-- 10. Definitions (def name = program) with let-polymorphism
--------------------------------------------------------------------------------

-- Every variable in a bare arrow is free.
freeVarsArrow :: Arrow -> Vars
freeVarsArrow = varsOfArrow

freeVarsScheme :: Scheme -> Vars
freeVarsScheme (Forall tv sv rv arr) =
  let (ft, fs, fr) = freeVarsArrow arr
  in (ft \\ tv, fs \\ sv, fr \\ rv)

freeVarsEnv :: Env -> Vars
freeVarsEnv env =
  foldr (catVars . freeVarsScheme) ([], [], []) (M.elems env)

-- Generalize all free type, stack, and row variables not fixed by the
-- environment.
generalize :: Env -> Arrow -> Scheme
generalize env arr =
  let (ftv, fsv, frv) = freeVarsArrow arr
      (etv, esv, erv) = freeVarsEnv env
  in Forall (ftv \\ etv) (fsv \\ esv) (frv \\ erv) arr

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
          if all isSpace body
            then do
              -- block body: the following indented lines (blank ends it)
              let indented ln = not (all isSpace ln) && isSpace (head ln)
                  (block, rest') = span indented rest
              if null block
                then Left $ "Empty definition body: " ++ name
                else do
                  (ds, ps) <- go rest'
                  pure ((name, intercalate "\n" block) : ds, ps)
            else do
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
checkModule = checkModuleWith primEnv

-- Check a module starting from a given environment (REPL sessions grow
-- the environment incrementally).
checkModuleWith :: Env -> String -> Either String Module
checkModuleWith env0 src = do
  (defSrcs, mainSrc) <- splitDefs src
  (env', defsRev) <- foldM addDef (env0, []) defSrcs
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
      term0 <- parseProgram bodySrc
      let term = substRecurse name term0
      arr  <- inferDefTermIn name env term
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

-- Runtime variable environment: named-abstraction parameters in scope.
type VarEnv = Map String Value

-- A function value captures the variable environment at reification, so
-- quotations inside abstraction bodies are closures over the parameters.
data Value
  = VInt Int
  | VFn VarEnv Term
  | VList [Value]
  | VSum Int [Value]   -- tag (0-based) + the alternative's wire bundle
  deriving (Eq)

instance Show Value where
  show (VInt n)      = show n
  show (VFn _ _)     = "[fn]"
  show (VList vs)    = "list(" ++ intercalate ", " (map show vs) ++ ")"
  show (VSum i vs)   =
    "in" ++ show (i + 1) ++ "(" ++ intercalate ", " (map show vs) ++ ")"

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
    arityOf (Forall _ _ _ (Arrow i _)) = closedArity i

-- Evaluate a term: returns the final stack and the print log.  The Env
-- is needed to compute closed arities of grouped compound operands; the
-- VarEnv holds named-abstraction parameters in scope.
evalTerm :: Env -> RunDefs -> VarEnv -> Term -> [Value]
         -> Either String ([Value], [String])
evalTerm env defs vars term st =
  case term of
    Seq t u -> do
      (st1, l1) <- evalTerm env defs vars t st
      (st2, l2) <- evalTerm env defs vars u st1
      pure (st2, l1 ++ l2)
    Tensor ts      -> goAtoms ts st
    p@(Prim _)     -> goAtoms [p] st
    q@(Quote _)    -> goAtoms [q] st
    l@(ListLit _)  -> goAtoms [l] st
    o@(OpenAbs {}) -> goAtoms [o] st
    a@(Alts {})    -> goAtoms [a] st
  where
    goAtoms [] stk = Right (stk, [])   -- leftover remainder flows through last
    goAtoms (a : more) stk = do
      (out, stk', logs) <- applyAtom (null more) a stk
      (outRest, logs') <- goAtoms more stk'
      pure (out ++ outRest, logs ++ logs')

    -- apply is special: its Γ is the stack segment after the code value.
    -- As the final atom that segment is the whole remaining stack; as a
    -- non-final atom it was closed to • by the typechecker.  (Parameters
    -- shadow the special forms, hence the vars guards.)
    applyAtom isFinal (Prim "apply") stk
      | not (M.member "apply" vars) = do
          (args, stk') <- takeWires "apply" 1 stk
          case args of
            [VFn cvars body] -> do
              let seg = if isFinal then stk' else []
              (out, logs) <- evalTerm env defs cvars body seg
              pure (out, if isFinal then [] else stk', logs)
            _ ->
              Left "Runtime type error in apply: expected a quotation"
    -- if / otherwise: segment-consuming entries into the guard machine
    -- (positional semantics like apply: whole stack in final position).
    applyAtom isFinal (Prim "if") stk
      | not (M.member "if" vars), not (M.member "if" defs) =
          if isFinal
            then Right ([VSum 1 stk], [], [])
            else Right ([VSum 1 []], stk, [])
    applyAtom isFinal (Prim "otherwise") stk
      | not (M.member "otherwise" vars), not (M.member "otherwise" defs) =
          if isFinal
            then Right ([VSum 0 stk], [], [])
            else Right ([VSum 0 []], stk, [])
    -- loop: Elgot iteration — run the body on the segment; the continue
    -- track re-enters, the done track exits.
    applyAtom isFinal (Prim "loop") stk
      | not (M.member "loop" vars), not (M.member "loop" defs) = do
          (args, stk') <- takeWires "loop" 1 stk
          case args of
            [VFn cv body] -> do
              let seg0 = if isFinal then stk' else []
                  go seg logs = do
                    (out, lg) <- evalTerm env defs cv body seg
                    case out of
                      [VSum 0 bundle] -> go bundle (logs ++ lg)
                      [VSum 1 bundle] -> Right (bundle, logs ++ lg)
                      _ -> Left "Runtime type error in loop: body must return a (continue | done) decision"
              (result, logs) <- go seg0 []
              pure (result, if isFinal then [] else stk', logs)
            _ -> Left "Runtime type error in loop: expected a body quotation"
    applyAtom isFinal (Prim name) stk
      | Just n <- injIndex name
      , not (M.member name vars)
      , not (M.member name defs) =
          if isFinal
            then Right ([VSum (n - 1) stk], [], [])
            else Right ([VSum (n - 1) []], stk, [])
    applyAtom _ (Prim name) stk
      | Just v <- M.lookup name vars = Right ([v], stk, [])
      | isIntLiteral name = Right ([VInt (read name)], stk, [])
      | Just (k, body) <- M.lookup name defs = do
          (args, stk') <- takeWires name k stk
          (out, logs) <- evalTerm env defs M.empty body args
          pure (out, stk', logs)
      | otherwise = do
          k <- builtinArity name
          (args, stk') <- takeWires name k stk
          (out, logs) <- runBuiltin env defs name args
          pure (out, stk', logs)
    applyAtom _ (Quote body) stk = Right ([VFn vars body], stk, [])
    applyAtom _ (ListLit es) stk = do
      vs <- mapM elemValue es
      pure ([VList vs], stk, [])
      where
        elemValue e = do
          (out, _) <- evalTerm env defs vars e []
          case out of
            [v] -> Right v
            _   -> Left "list element must push exactly one value"
    -- Code row: consume the sum wire, dispatch on the tag, run the
    -- matching component on the bundle, re-tag the result.  Tags past
    -- the components fall to the residual (identity).
    applyAtom _ (Alts comps residual) stk = do
      (args, stk') <- takeWires "code row" 1 stk
      case args of
        [VSum tag bundle]
          | tag < length comps -> do
              (out, logs) <- evalTerm env defs vars (comps !! tag) bundle
              pure ([VSum tag out], stk', logs)
          | residual ->
              pure ([VSum tag bundle], stk', [])
          | otherwise ->
              Left "Runtime error in code row: tag out of range"
        _ -> Left "Runtime type error in code row: expected a sum value"
    -- Named abstraction: bind the parameter wires (left to right), run
    -- the body on the empty stack in the extended scope.
    applyAtom _ (OpenAbs ps body) stk = do
      (args, stk') <- takeWires "abstraction" (length ps) stk
      let vars' = M.fromList (zip ps args) `M.union` vars
      (out, logs) <- evalTerm env defs vars' body []
      pure (out, stk', logs)
    -- Grouped compound operand (Seq/Tensor as an atom).  Final: evaluate
    -- on the whole remaining stack (its open tail carries the remainder).
    -- Non-final: it was typed closed, so take exactly its inferred arity.
    applyAtom isFinal t' stk
      | isFinal = do
          (out, logs) <- evalTerm env defs vars t' stk
          pure (out, [], logs)
      | otherwise = do
          -- Arity inference must see the in-scope parameters; their
          -- element types don't affect wire counts, so polymorphic
          -- dummies suffice.
          let dummy = TV "_param"
              dummyScheme =
                Forall [dummy] [] [] (Arrow SEnd (SCons (TVarTy dummy) SEnd))
              arityEnv = foldr (\n -> M.insert n dummyScheme)
                               env (M.keys vars)
          Arrow i _ <- inferTermIn arityEnv t'
          let k = closedArity i
          (args, stk') <- takeWires "grouped program" k stk
          (out, logs) <- evalTerm env defs vars t' args
          pure (out, stk', logs)

    takeWires name k stk
      | length stk >= k = Right (take k stk, drop k stk)
      | otherwise =
          Left $ "Runtime stack underflow in " ++ name
               ++ " (unreachable on typechecked programs)"

builtinArity :: String -> Either String Int
builtinArity name =
  case M.lookup name primEnv of
    Just (Forall _ _ _ (Arrow i _)) -> Right (closedArity i)
    Nothing -> Left $ "Unknown primitive at runtime: " ++ name

runBuiltin :: Env -> RunDefs -> String -> [Value]
           -> Either String ([Value], [String])
runBuiltin _ _ "id"    [v]              = Right ([v], [])
runBuiltin _ _ "_"     [v]              = Right ([v], [])
runBuiltin _ _ "swap"  [x, y]           = Right ([y, x], [])
runBuiltin _ _ "dup"   [v]              = Right ([v, v], [])
runBuiltin _ _ "drop"  [_]              = Right ([], [])
runBuiltin _ _ "pass"  []               = Right ([], [])
runBuiltin _ _ "f"     [VInt n]         = Right ([VInt (n + 1)], [])   -- sample unary: successor
runBuiltin _ _ "g"     [VInt n]         = Right ([VInt (2 * n)], [])   -- sample unary: double
runBuiltin _ _ "+"     [VInt x, VInt y] = Right ([VInt (x + y)], [])
runBuiltin _ _ "*"     [VInt x, VInt y] = Right ([VInt (x * y)], [])
runBuiltin _ _ "print" [v]              = Right ([], [show v])
runBuiltin _ _ "true"  []               = Right ([VSum 0 []], [])
runBuiltin _ _ "false" []               = Right ([VSum 1 []], [])
runBuiltin _ _ "negative?" [VInt n]     = Right ([VSum (if n < 0 then 0 else 1) [VInt n]], [])
runBuiltin _ _ "even?" [VInt n]         = Right ([VSum (if even n then 0 else 1) [VInt n]], [])
runBuiltin _ _ "odd?"  [VInt n]         = Right ([VSum (if odd n then 0 else 1) [VInt n]], [])
runBuiltin _ _ "zero?" [VInt n]         = Right ([VSum (if n == 0 then 0 else 1) [VInt n]], [])
runBuiltin _ _ "eq?"  [x, y]            = Right ([VSum (if x == y then 0 else 1) [x, y]], [])
runBuiltin _ _ "lt?"  [VInt x, VInt y]  = Right ([VSum (if x < y then 0 else 1) [VInt x, VInt y]], [])
runBuiltin _ _ "-"    [VInt x, VInt y]  = Right ([VInt (x - y)], [])
runBuiltin _ _ "uncons" [VList []]      = Right ([VSum 0 []], [])
runBuiltin _ _ "uncons" [VList (v:vs)]  = Right ([VSum 1 [v, VList vs]], [])
-- elif: fold one guard clause into the (Θ | Σ) state
runBuiltin env defs "elif" [VSum 0 done'] = Right ([VSum 0 done'], [])
runBuiltin env defs "elif" [VSum 1 [VFn cv act, VSum d payload]]
  | d == 0 = do
      (out, lg) <- evalTerm env defs cv act payload
      Right ([VSum 0 out], lg)               -- hit: action ran, done track
  | otherwise = Right ([VSum 1 payload], []) -- miss: payload to residual
-- endif: fold the final clause and close; the miss branch is the
-- absurdity map (its track is uninhabited) — defensive error only
runBuiltin env defs "endif" [VSum 0 done'] = Right (done', [])
runBuiltin env defs "endif" [VSum 1 [VFn cv act, VSum 0 payload]] =
  evalTerm env defs cv act payload
runBuiltin _ _ "endif" [VSum 1 _] =
  Left "endif: absurd (unreachable: the otherwise-clause cannot miss)"
runBuiltin _ _ "there" [VSum t bundle]  = Right ([VSum (t + 1) bundle], [])
runBuiltin _ _ "merge" [VSum _ bundle]  = Right (bundle, [])
runBuiltin env defs "map" [VFn cv t, VList vs] = do
  rs <- mapM step vs
  pure ([VList (map fst rs)], concatMap snd rs)
  where
    step v = do
      (out, logs) <- evalTerm env defs cv t [v]
      case out of
        [r] -> Right (r, logs)
        _   -> Left "map: code must return exactly one value"
runBuiltin env defs "fold" [VFn cv t, b0, VList vs] = do
  (b, logs) <- foldM step (b0, []) vs
  pure ([b], logs)
  where
    step (b, logs) v = do
      (out, logs') <- evalTerm env defs cv t [b, v]
      case out of
        [b'] -> Right (b', logs ++ logs')
        _    -> Left "fold: code must return exactly one value"
runBuiltin _ _ name args =
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
      | otherwise -> evalTerm (modEnv m) (moduleRunDefs m) M.empty term []
