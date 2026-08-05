{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module MiniConcatTypechecker where

import qualified Data.Map as M
import Data.Map (Map)
import Data.Maybe (fromMaybe, isNothing, isJust, fromJust)
import Data.List (nub, intercalate, elemIndex, (\\))
import Control.Monad.State
import Control.Monad.Except (ExceptT, runExceptT, throwError, liftEither)
import Control.Monad.IO.Class (liftIO)
import Control.Exception (try, IOException, evaluate)
import Control.Monad (foldM)
import Data.Char (isDigit, isSpace)
import Data.Bifunctor (first)

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

-- Exponent variables (n): type-level widths, kind Nat.  Unary naturals
-- only — zero and successor, no arithmetic (design-exponents.md).
newtype NVar = NV String
  deriving (Eq, Ord)

instance Show NVar where
  show (NV s) = s

-- An exponent in canonical form: k successors over a variable or zero.
-- `Exp 2 (Just n)` is S(S(n)); `Exp 3 Nothing` is the literal 3.
data Exp = Exp Int (Maybe NVar)
  deriving (Eq, Ord)

instance Show Exp where
  show (Exp k Nothing)  = show k
  show (Exp 0 (Just n)) = show n
  show (Exp k (Just n)) = show n ++ "+" ++ show k

-- Element types.  TFn nests whole arrows inside element types, so
-- stack variables can occur inside types — all traversals (occurs
-- checks, substitution, unification) must recurse through it.
data Ty
  = TVarTy TVar
  | TInt
  | TStr               -- text
  | TSym               -- interned symbol: .name literals
  | TFn Arrow          -- Fn⟨Γ ⇒ Δ⟩: a reified program
  | TSum SumRow        -- (Δ₁ | … | Δₙ [| σ]): sum of stacks, one wire
  | TData String [SType] -- a declared nominal type: Name(arg-stacks)
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
  show TStr        = "Str"
  show TSym        = "Sym"
  show (TFn arr) = "Fn⟨" ++ show arr ++ "⟩"
  show (TSum row)  = "(" ++ show row ++ ")"
  show (TData n []) = n
  show (TData n as) =
    n ++ "(" ++ intercalate ", " (map show as) ++ ")"   -- args are stacks

-- Stack types: front (leftmost) wire first, optional tail variable at the end
data SType
  = SEnd             -- closed end: empty stack •
  | STail SVar       -- open end: remainder variable ρ
  | SCons Ty SType   -- τ Σ (τ is the leftmost wire)
  | SSplice SVar SType -- a stack variable spliced before a closed suffix
  | SExp SType Exp SType -- base^e: a CLOSED segment repeated e times, then rest
  deriving (Eq, Ord)

-- smart constructor: a splice before nothing is just a tail
ssplice :: SVar -> SType -> SType
ssplice v SEnd = STail v
ssplice v r    = SSplice v r

-- smart constructor, canonical form: a concrete exponent expands away,
-- and a concrete OFFSET (base^(n+k)) expands into k real copies before
-- an offset-free exponent — so equal stacks are structurally equal.
-- The base's element vars are SHARED across copies (Aⁿ is n copies of
-- the same A).
sexp :: SType -> Exp -> SType -> SType
sexp base (Exp k Nothing) rest = expandCopies k base rest
sexp base (Exp k mv) rest
  | k > 0     = expandCopies k base (SExp base (Exp 0 mv) rest)
  | otherwise = SExp base (Exp 0 mv) rest

expandCopies :: Int -> SType -> SType -> SType
expandCopies 0 _    rest = rest
expandCopies k base rest = appendS base (expandCopies (k - 1) base rest)

-- number of wires in one copy of a base segment (bases are closed)
segArity :: SType -> Int
segArity = closedArity

-- total append: an open front becomes a splice
appendS :: SType -> SType -> SType
appendS SEnd r           = r
appendS (SCons t s) r    = SCons t (appendS s r)
appendS (STail v) r      = ssplice v r
appendS (SSplice v s) r  = SSplice v (appendS s r)
appendS (SExp b e s) r   = SExp b e (appendS s r)

-- superscript display: Intⁿ, Int³, (A B)ⁿ; caret fallback for exotic names
supScript :: String -> Maybe String
supScript = mapM sup
  where
    sup c = lookup c (zip "0123456789nmkij" "⁰¹²³⁴⁵⁶⁷⁸⁹ⁿᵐᵏⁱʲ")

showExpAt :: SType -> Exp -> String
showExpAt base e =
  baseStr ++ fromMaybe ("^" ++ show e) (supScript (show e))
  where
    baseStr = case base of
      SCons _ SEnd -> show base            -- single wire: Intⁿ
      _            -> "(" ++ show base ++ ")"

instance Show SType where
  show SEnd       = "•"
  show (STail v)  = show v
  show st         = unwords (go st)
    where
      go SEnd             = []
      go (STail v)        = [show v]
      go (SCons t rest)   = show t : go rest
      go (SSplice v rest) = show v : go rest
      go (SExp b e rest)  = showExpAt b e : go rest

-- Arrows: stack transformers Σ_in ⇒ Σ_out
data Arrow = Arrow SType SType
  deriving (Eq, Ord)

instance Show Arrow where
  show (Arrow s1 s2) = show s1 ++ " ⇒ " ++ show s2

--------------------------------------------------------------------------------
-- 2. Schemes and environments (only polymorphism over stack vars & type vars)
--------------------------------------------------------------------------------

data Scheme = Forall [TVar] [SVar] [RVar] [NVar] Arrow
  deriving (Eq, Ord)

instance Show Scheme where
  show (Forall tvars svars rvars nvars arr) =
    "∀ " ++ unwords (map show tvars ++ map show svars ++ map show rvars
                       ++ map show nvars)
         ++ ". " ++ show arr

type Env = Map String Scheme

--------------------------------------------------------------------------------
-- 3. Substitutions and "apply"
--------------------------------------------------------------------------------

data Subst = Subst
  { tySub  :: Map TVar Ty
  , stSub  :: Map SVar SType
  , rowSub :: Map RVar SumRow
  , expSub :: Map NVar Exp
  } deriving (Eq, Show)

emptySubst :: Subst
emptySubst = Subst M.empty M.empty M.empty M.empty

-- composeSubst s2 s1 = apply s2 after s1
composeSubst :: Subst -> Subst -> Subst
composeSubst s2 s1 =
  Subst
    { tySub  = M.map (apply s2) (tySub s1) `M.union` tySub s2
    , stSub  = M.map (apply s2) (stSub s1) `M.union` stSub s2
    , rowSub = M.map (apply s2) (rowSub s1) `M.union` rowSub s2
    , expSub = M.map (apply s2) (expSub s1) `M.union` expSub s2
    }

class Substitutable a where
  apply :: Subst -> a -> a

instance Substitutable Ty where
  apply s t@(TVarTy v) =
    case M.lookup v (tySub s) of
      Nothing -> t
      Just t' -> apply s t'   -- chase chains, like the SType instance
  apply _ TInt        = TInt
  apply _ TStr        = TStr
  apply _ TSym        = TSym
  apply s (TFn arr) = TFn (apply s arr)
  apply s (TData n as) = TData n (map (apply s) as)
  apply s (TSum row)  = TSum (apply s row)

instance Substitutable Exp where
  apply s e@(Exp k mv) =
    case mv of
      Nothing -> e
      Just n  -> case M.lookup n (expSub s) of
        Nothing          -> e
        Just e'          -> let Exp k' mv' = apply s e' in Exp (k + k') mv'

instance Substitutable SType where
  apply _ SEnd = SEnd
  apply s st@(STail v) =
    case M.lookup v (stSub s) of
      Nothing  -> st
      Just st' -> apply s st'
  apply s (SCons ty rest) = SCons (apply s ty) (apply s rest)
  apply s (SSplice v rest) =
    case M.lookup v (stSub s) of
      Nothing  -> SSplice v (apply s rest)
      Just st' -> appendS (apply s st') (apply s rest)
  -- sexp normalizes: a concrete exponent expands into copies
  apply s (SExp b e rest) = sexp (apply s b) (apply s e) (apply s rest)

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
  apply s (Forall tv sv rv nv arr) =
    let s' = Subst (foldr M.delete (tySub s) tv)
                   (foldr M.delete (stSub s) sv)
                   (foldr M.delete (rowSub s) rv)
                   (foldr M.delete (expSub s) nv)
    in Forall tv sv rv nv (apply s' arr)

instance Substitutable Env where
  apply s = M.map (apply s)

--------------------------------------------------------------------------------
-- 4. Constraints and unification
--------------------------------------------------------------------------------

data Constraint
  = CEqTy Ty Ty
  | CEqStack SType SType
  | CFail String   -- carry a deferred inference error to the solver
  deriving (Eq, Show)

-- All variables (type, stack, row, exponent) in order of first
-- appearance, recursing through Fn⟨Γ ⇒ Δ⟩ and (… | …) element types.
-- The single traversal backing occurs checks, generalization, and
-- normalization.
type Vars = ([TVar], [SVar], [RVar], [NVar])

noVars :: Vars
noVars = ([], [], [], [])

varsOfTy :: Ty -> Vars
varsOfTy (TVarTy v)  = ([v], [], [], [])
varsOfTy TInt        = noVars
varsOfTy TStr        = noVars
varsOfTy TSym        = noVars
varsOfTy (TFn arr)   = varsOfArrow arr
varsOfTy (TSum row)  = varsOfRow row
varsOfTy (TData _ as) = foldr (catVars . varsOfStack) noVars as

varsOfStack :: SType -> Vars
varsOfStack SEnd             = noVars
varsOfStack (STail v)        = ([], [v], [], [])
varsOfStack (SCons t rest)   = varsOfTy t `catVars` varsOfStack rest
varsOfStack (SSplice v rest) = ([], [v], [], []) `catVars` varsOfStack rest
varsOfStack (SExp b e rest)  =
  varsOfStack b `catVars` varsOfExp e `catVars` varsOfStack rest

varsOfExp :: Exp -> Vars
varsOfExp (Exp _ (Just n)) = ([], [], [], [n])
varsOfExp _                = noVars

varsOfRow :: SumRow -> Vars
varsOfRow RNil            = noVars
varsOfRow (RTail v)       = ([], [], [v], [])
varsOfRow (RCons st rest) = varsOfStack st `catVars` varsOfRow rest

catVars :: Vars -> Vars -> Vars
catVars (t1, s1, r1, n1) (t2, s2, r2, n2) =
  (t1 ++ t2, s1 ++ s2, r1 ++ r2, n1 ++ n2)

varsOfArrow :: Arrow -> Vars
varsOfArrow (Arrow i o) =
  let (ts, ss, rs, ns) = varsOfStack i `catVars` varsOfStack o
  in (nub ts, nub ss, nub rs, nub ns)

-- Occurs checks.  Callers (bind*Var) only ever check against
-- fully-applied targets, so a pure structural traversal is sufficient.
occursTy :: TVar -> Ty -> Bool
occursTy a t = let (ts, _, _, _) = varsOfTy t in a `elem` ts

occursStack :: SVar -> SType -> Bool
occursStack v st = let (_, ss, _, _) = varsOfStack st in v `elem` ss

occursRow :: RVar -> SumRow -> Bool
occursRow v row = let (_, _, rs, _) = varsOfRow row in v `elem` rs

-- Unify simple element types
unifyTy :: Subst -> Ty -> Ty -> Either String Subst
unifyTy s t1 t2 =
  let t1' = apply s t1
      t2' = apply s t2
  in case (t1', t2') of
    (TVarTy a, t) -> bindTyVar s a t
    (t, TVarTy a) -> bindTyVar s a t
    (TInt, TInt)  -> Right s
    (TStr, TStr)  -> Right s
    (TSym, TSym)  -> Right s
    (TFn (Arrow i1 o1), TFn (Arrow i2 o2)) -> do
      s' <- unifyStack s i1 i2
      unifyStack s' o1 o2
    (TSum r1, TSum r2)   -> unifyRow s r1 r2
    (TData n1 as1, TData n2 as2)
      | n1 == n2 && length as1 == length as2 ->
          foldM (\acc (x, y) -> unifyStack acc x y) s (zip as1 as2)
    _             -> Left $ "Cannot unify types: " ++ show t1' ++ " vs " ++ show t2'

bindTyVar :: Subst -> TVar -> Ty -> Either String Subst
bindTyVar s a t
  | t == TVarTy a = Right s
  | occursTy a t = Left $ "Occurs check failed: " ++ show a ++ " in " ++ show t
  | otherwise     = Right s { tySub = M.insert a t (tySub s) }

-- Unify exponents (unary naturals in canonical form k + var?)
unifyExp :: Subst -> Exp -> Exp -> Either String Subst
unifyExp s e1 e2 =
  let e1' = apply s e1
      e2' = apply s e2
  in case (e1', e2') of
    (Exp k1 Nothing, Exp k2 Nothing)
      | k1 == k2  -> Right s
      | otherwise -> Left $ "Cannot unify exponents: "
                          ++ show e1' ++ " vs " ++ show e2'
    (Exp k1 (Just n), Exp k2 mv) -> bindNVar s n k1 (Exp k2 mv)
    (Exp k1 mv, Exp k2 (Just n)) -> bindNVar s n k2 (Exp k1 mv)

-- solve k + n = e for n
bindNVar :: Subst -> NVar -> Int -> Exp -> Either String Subst
bindNVar s n k (Exp k' mv')
  | mv' == Just n =
      if k == k' then Right s
      else Left $ "Occurs check failed on exponent: " ++ show n
  | k' < k =
      case mv' of
        Just m ->  -- k + n = k' + m, k' < k: bind m := n + (k - k')
          Right s { expSub = M.insert m (Exp (k - k') (Just n)) (expSub s) }
        Nothing -> Left $ "Cannot unify exponents: "
                        ++ show (Exp k (Just n)) ++ " vs " ++ show (Exp k' mv')
  | otherwise =
      Right s { expSub = M.insert n (Exp (k' - k) mv') (expSub s) }

-- Unify stack types (plain list unification with an optional tail variable)
unifyStack :: Subst -> SType -> SType -> Either String Subst
unifyStack s st1 st2 =
  let st1' = apply s st1
      st2' = apply s st2
  in case (st1', st2') of
    (SEnd, SEnd) -> Right s
    (STail v, st) -> bindStackVar s v st
    (st, STail v) -> bindStackVar s v st
    -- exponents: same-shape bases unify pointwise (widths correlate)
    (SExp b1 e1 r1, SExp b2 e2 r2)
      | segArity b1 == segArity b2 -> do
          s1 <- unifyStack s b1 b2
          s2 <- unifyExp s1 e1 e2
          unifyStack s2 r1 r2
    (SExp b e r, st) -> expSplit s b e r st
    (st, SExp b e r) -> expSplit s b e r st
    (SSplice v1 r1, SSplice v2 r2) ->
      let m1 = closedArity r1
          m2 = closedArity r2
      in if m1 == m2
           then do s' <- unifyStack s r1 r2
                   unifyStack s' (STail v1) (STail v2)
           else if m1 < m2
             then spliceSplit s v2 r2 (SSplice v1 r1)
             else spliceSplit s v1 r1 (SSplice v2 r2)
    (SSplice v r, st) -> spliceSplit s v r st
    (st, SSplice v r) -> spliceSplit s v r st
    (SCons t1 r1, SCons t2 r2) -> do
      s'  <- unifyTy s t1 t2
      unifyStack s' r1 r2
    _ -> Left $ "Cannot unify stacks: " ++ show st1' ++ " vs " ++ show st2'
  where
    -- base^e ⧺ rest ~ other.  Copies are peeled off the FRONT of other
    -- one segment-width at a time (each peel refines e by one
    -- successor); the copies share the base's element vars, so all
    -- chunks are forced equal.  rest must be closed (right-anchoring —
    -- "one open exponent per segment region", design-exponents.md).
    expSplit s0 base e rest other
      | bw == 0 || openTailedS base =
          Left $ "Cannot unify stacks (exponent base): "
               ++ show (SExp base e rest) ++ " vs " ++ show other
      -- the linear case: k exponents over ONE variable n (bases may
      -- differ — aⁿ bⁿ), then a closed tail, against a closed stack:
      -- k·n·|b| = w is solvable by division.  Covers addN (ℝⁿ ℝⁿ) and
      -- zip (aⁿ bⁿ); multi-VARIABLE regions stay rejected (ambiguous).
      | Just (perCopy, chainEnd) <- sameVarChain e rest
      , not (openTailedS chainEnd), not (openTailedS other) =
          let w = closedArity other - closedArity chainEnd
          in if w < 0 || w `mod` perCopy /= 0
               then Left $ "Cannot unify stacks (exponent split): "
                         ++ show (SExp base e rest) ++ " vs " ++ show other
               else do
                 s1 <- unifyExp s0 e (Exp (w `div` perCopy) Nothing)
                 unifyStack s1 (apply s1 (SExp base e rest)) (apply s1 other)
      | openTailedS rest =
          Left $ "Cannot unify stacks (open tail after exponent): "
               ++ show (SExp base e rest) ++ " vs " ++ show other
      | otherwise = go s0 e other
      where
        bw = segArity base
        -- a run of ≥2 exponents all over the same variable, offset-free
        sameVarChain (Exp 0 (Just n)) r0 = chase (1 :: Int) bw r0
          where
            chase k acc (SExp b' (Exp 0 (Just n')) r')
              | n' == n, not (openTailedS b') =
                  chase (k + 1) (acc + segArity b') r'
            chase k acc r'
              | k >= 2    = Just (acc, r')
              | otherwise = Nothing
        sameVarChain _ _ = Nothing
        rw = closedArity rest
        err oth = Left $ "Cannot unify stacks (exponent split): "
                       ++ show (SExp base e rest) ++ " vs " ++ show oth
        go s1 e1 oth
          | not (openTailedS oth) =
              let w = closedArity oth - rw
              in if w < 0 || w `mod` bw /= 0
                   then err oth
                   else if w == 0
                     then do s2 <- unifyExp s1 e1 (Exp 0 Nothing)
                             unifyStack s2 rest oth
                     else peel s1 e1 oth
          | closedArity oth >= bw = peel s1 e1 oth
          | otherwise =
              case oth of
                STail u -> bindStackVar s1 u (sexp base e1 rest)
                SSplice u suffix
                  | closedArity oth == 0 && not (openTailedS suffix)
                  , rw >= closedArity suffix ->
                      let (rf, rb) = splitStackAt (rw - closedArity suffix) rest
                      in do s2 <- unifyStack s1 rb suffix
                            bindStackVar s2 u (sexp base e1 rf)
                _ -> err oth
        peel s1 e1 oth = do
          (e2, s2) <- peelExp s1 e1
          let (chunk, oth') = splitStackAt bw oth
          s3 <- unifyStack s2 base chunk
          go s3 (apply s3 e2) oth'
        -- e ≥ 1: strip one successor, refining an open exponent if needed
        peelExp s1 (Exp k mv) | k > 0 = Right (Exp (k - 1) mv, s1)
        peelExp s1 (Exp 0 (Just n)) =
          let m = NV (show n ++ "'")
          in Right ( Exp 0 (Just m)
                   , s1 { expSub = M.insert n (Exp 1 (Just m)) (expSub s1) } )
        peelExp _ (Exp 0 Nothing) =
          Left $ "Cannot unify stacks (exponent split): "
               ++ show (SExp base e rest) ++ " vs " ++ show other

    -- (v ⧺ suffix) ~ other: right-anchored split.  Closed other: the
    -- last |suffix| positions unify with suffix, the prefix binds v.
    -- Open-tailed other (P ⧺ t): bind v := P ⧺ b and t := b ⧺ suffix
    -- with a fresh bridge b — sound (not complete in adversarial
    -- corners where suffix could also match inside P).
    spliceSplit s0 v suffix other
      | openTailedS suffix =
          Left $ "Cannot unify stacks (splice split): "
               ++ show (SSplice v suffix) ++ " vs " ++ show other
      | not (openTailedS other) =
          let m = closedArity suffix
              n = closedArity other
          in if n < m
               then Left $ "Cannot unify stacks (splice split): "
                         ++ show (SSplice v suffix) ++ " vs " ++ show other
               else do
                 let (prefix, rest) = splitStackAt (n - m) other
                 s1 <- unifyStack s0 suffix rest
                 unifyStack s1 (STail v) prefix
      | otherwise =
          case openVarsS other of
            [t] ->
              let n = closedArity other
                  (prefix, _) = splitStackAt n other
                  b = SV (show t ++ "'")
              in do
                s1 <- unifyStack s0 (STail t) (ssplice b suffix)
                unifyStack s1 (STail v) (appendS prefix (STail b))
            _ -> Left $ "Cannot unify stacks (splice split): "
                      ++ show (SSplice v suffix) ++ " vs " ++ show other

splitStackAt :: Int -> SType -> (SType, SType)
splitStackAt 0 st = (SEnd, st)
splitStackAt k (SCons t rest) =
  let (pre, post) = splitStackAt (k - 1) rest
  in (SCons t pre, post)
splitStackAt _ st = (SEnd, st)

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
    step _ (CFail msg)        = Left msg

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

freshNVarName :: Infer NVar
freshNVarName = Infer $ do
  n <- get
  put (n + 1)
  pure (NV ("n" ++ show n))

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
    goS (SSplice v rest) =
      appendS (fromMaybe (STail v) (M.lookup v (stSub s))) (goS rest)
    goS (SExp b e rest) = SExp (goS b) (goE e) (goS rest)

    goE e@(Exp k mv) = case mv of
      Just n | Just (Exp k' mv') <- M.lookup n (expSub s) -> Exp (k + k') mv'
      _ -> e

    goT t@(TVarTy v) = fromMaybe t (M.lookup v (tySub s))
    goT (TFn arr)  = TFn (substOnce s arr)
    goT (TSum row)   = TSum (goR row)
    goT (TData n as) = TData n (map goS as)
    goT t            = t

    goR RNil = RNil
    goR row@(RTail v) = fromMaybe row (M.lookup v (rowSub s))
    goR (RCons st rest) = RCons (goS st) (goR rest)

-- Instantiate a polymorphic scheme with fresh type, stack, and row
-- variables (used for the final atom of a tensor chain, which may stay
-- open).
instantiate :: Scheme -> Infer Arrow
instantiate (Forall tvars svars rvars nvars arr) = do
  newTVs <- mapM (const freshTyVarName) tvars
  newSVs <- mapM (const freshSVarName) svars
  newRVs <- mapM (const freshRVarName) rvars
  newNVs <- mapM (const freshNVarName) nvars
  let tSub = M.fromList (zip tvars (map TVarTy newTVs))
      sSub = M.fromList (zip svars (map STail newSVs))
      rSub = M.fromList (zip rvars (map RTail newRVs))
      nSub = M.fromList (zip nvars (map (Exp 0 . Just) newNVs))
  pure (substOnce (Subst tSub sSub rSub nSub) arr)

-- Instantiate a scheme *closed* for a non-final tensor atom: only the
-- OUTER TAILS of the arrow are closed (ρ := •) — that is all appendStack
-- needs.  Variables living purely inside element types (Fn⟨…⟩, sums)
-- are freshened like any instantiation: they are the atom's
-- polymorphism, not a remainder.  (Matches the grouped-compound closing
-- policy.)
instantiateClosed :: Scheme -> Infer Arrow
instantiateClosed (Forall tvars svars rvars nvars arr@(Arrow i o)) = do
  newTVs <- mapM (const freshTyVarName) tvars
  let tailVs = openVarsS i ++ openVarsS o
  newSVs <- mapM (\v -> if v `elem` tailVs
                          then pure Nothing
                          else Just <$> freshSVarName) svars
  newRVs <- mapM (const freshRVarName) rvars
  -- exponents in SPINE position are widths of the atom's own segment:
  -- close them (n := 0), like ρ := •.  Exponents living inside element
  -- types are the atom's polymorphism: freshen.
  let spineNVs = spineExpVars i ++ spineExpVars o
  newNVs <- mapM (\v -> if v `elem` spineNVs
                          then pure Nothing
                          else Just <$> freshNVarName) nvars
  let tSub = M.fromList (zip tvars (map TVarTy newTVs))
      sSub = M.fromList [ (v, maybe SEnd STail mn)
                        | (v, mn) <- zip svars newSVs ]
      rSub = M.fromList (zip rvars (map RTail newRVs))
      nSub = M.fromList [ (v, maybe (Exp 0 Nothing) (Exp 0 . Just) mn)
                        | (v, mn) <- zip nvars newNVs ]
  pure (substOnce (Subst tSub sSub rSub nSub) arr)

-- exponent variables on a stack's spine (not inside element types)
spineExpVars :: SType -> [NVar]
spineExpVars (SExp _ (Exp _ (Just n)) r) = n : spineExpVars r
spineExpVars (SExp _ _ r)                = spineExpVars r
spineExpVars (SCons _ r)                 = spineExpVars r
spineExpVars (SSplice _ r)               = spineExpVars r
spineExpVars _                           = []

--------------------------------------------------------------------------------
-- 6. Terms
--------------------------------------------------------------------------------

data Term
  = Prim String
  | Tensor [Term]         -- n-ary tensor chain, atoms aligned with wires left to right
  | Seq Term Term         -- t >> u
  | Quote Term            -- [p]: push the reified program p
                          -- must be a pure push (• ⇒ A)
  | OpenAbs [Maybe String] Bool Term
                          -- (x _ z [...] -> body): ONE SLOT PER CONSUMED
                          -- WIRE, aligned with wires exactly as atoms are
                          -- in a tensor stage (leftmost = deepest).  A
                          -- parameter list uses the stage vocabulary:
                          -- `Just n` (a name) consumes one wire and binds
                          -- it; `Nothing` (`_`) consumes one wire and
                          -- hands it to the BODY; the flag says the params
                          -- end in `...` (hand the body the whole rest).
                          -- The body's input is the unnamed slots, in
                          -- order, then the rest.  All-named and no `...`
                          -- = input-closed: the original behaviour.
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
  | TokKleisli    -- >=> (Kleisli composition in the sum monad)
  | TokOrElse     -- >?> (the dual: chain along the miss track)
  | TokOrClose    -- >!> (close a >?> chain with a total default)
  | TokCaret      -- ^ (exponent in type expressions: Int^3, (A B)^n)
  | TokBarBar     -- || (vertical list literal: || e1 || e2 || … )
  | TokLAngle     -- ⟨ (open a Fn type: Fn⟨Σ ⇒ Θ⟩)
  | TokRAngle     -- ⟩ (close a Fn type)
  | TokFatArrow   -- ⇒ (the arrow inside a Fn type)
  deriving (Eq, Show)

tokenize :: String -> Either String [Token]
tokenize = go
  where
    go [] = Right []
    go ('\r':'\n':cs) = (TokNewline :) <$> go cs
    go ('\n':cs)      = (TokNewline :) <$> go cs
    go ('#':cs)         = go (dropWhile (/= '\n') cs)  -- comment to EOL
    go ('"':cs)         = do
      (str, rest) <- lexStr cs
      (TokIdent ('"' : str) :) <$> go rest
    go ('>':'=':'>':cs) = (TokKleisli :) <$> go cs
    go ('>':'?':'>':cs) = (TokOrElse :) <$> go cs
    go ('>':'!':'>':cs) = (TokOrClose :) <$> go cs
    go ('>':'>':'>':cs) = (TokSeqPass :) <$> go cs
    go ('>':'>':cs)     = (TokSeq :) <$> go cs
    go ('>':_)          = Left "Unexpected '>' without matching '>>'"
    go ('.':'.':'.':cs) = (TokEllipsis :) <$> go cs
    go ('.':cs)
      | (nm, rest) <- span isIdentChar cs
      , not (null nm) = (TokIdent ('.' : nm) :) <$> go rest
    go ('…':cs)         = (TokEllipsis :) <$> go cs   -- U+2026, autocorrect's ...
    go ('.':_)          = Left "Unexpected '.' (did you mean '...'?)"
    go ('[':cs)         = (TokLBrack :) <$> go cs
    go (']':cs)         = (TokRBrack :) <$> go cs
    go ('(':cs)         = (TokLParen :) <$> go cs
    go (')':cs)         = (TokRParen :) <$> go cs
    go (',':cs)         = (TokComma :) <$> go cs
    go ('-':'>':cs)     = (TokArrow :) <$> go cs
    go ('-':cs)
      | (ds@(_:_), rest) <- span isDigit cs =
          (TokIdent ('-' : ds) :) <$> go rest          -- negative literal
      | otherwise = (TokIdent "-" :) <$> go cs         -- subtraction
    go ('|':'|':cs)     = (TokBarBar :) <$> go cs
    go ('|':cs)         = (TokBar :) <$> go cs
    go ('^':cs)         = (TokCaret :) <$> go cs
    go (';':cs)         = (TokSeq :) <$> go cs   -- ; is a synonym for >>
    go ('⟨':cs)         = (TokLAngle :) <$> go cs     -- Fn⟨…⟩ type brackets
    go ('⟩':cs)         = (TokRAngle :) <$> go cs
    go ('⇒':cs)         = (TokFatArrow :) <$> go cs

    go (c:cs)
      | isSpace c = go cs
      -- Unicode superscripts lex as ^ + the translated exponent
      | Just _ <- unSup c =
          let (sups, rest) = span (isJust . unSup) (c:cs)
              plain = map (fromJust . unSup) sups
          in ((TokCaret :) . (supTok plain :)) <$> go rest
      | isDigit c =
          let (digits, rest) = span isDigit (c:cs)
          in (TokInt (read digits) :) <$> go rest
      | otherwise =
          let (ident, rest) = span isIdentChar (c:cs)
          in (TokIdent ident :) <$> go rest

    supTok plain
      | all isDigit plain = TokInt (read plain)
      | otherwise         = TokIdent plain

    unSup ch = lookup ch (zip "⁰¹²³⁴⁵⁶⁷⁸⁹ⁿᵐᵏⁱʲ" "0123456789nmkij")

    isIdentChar ch =
      not (isSpace ch) && isNothing (unSup ch)
        && ch `notElem` (">.[](),-|#\"^;\8230\10216\10217\8658" :: String)

    -- string literal body: minimal escapes \" \\ \n
    lexStr ('\\':'"':cs)  = first ('"' :)  <$> lexStr cs
    lexStr ('\\':'\\':cs) = first ('\\' :) <$> lexStr cs
    lexStr ('\\':'n':cs)  = first ('\n' :) <$> lexStr cs
    lexStr ('"':cs)       = Right ("", cs)
    lexStr (c:cs)         = first (c :) <$> lexStr cs
    lexStr []             = Left "Unterminated string literal"

-- Collapse newline runs, drop leading/trailing newlines, and absorb
-- newlines adjacent to an explicit >> / >>> (the operator wins).
normalizeToks :: [Token] -> [Token]
normalizeToks = trim . collapse
  where
    -- A newline is a strict `>>`.  It is absorbed only next to an
    -- operator a newline cannot itself express: the railway operators
    -- (`>=>`, `>?>`, `>!>`) and the `||` list-literal continuation.
    -- `>>` and `|` never absorb — a newline
    -- already *is* `>>`, and the row separator `|` must stay put so
    -- aligned track-columns work (`f |` ⏎ `| g` is two rows, not one
    -- collided `| |`).
    collapse [] = []
    collapse (TokNewline : ts) =
      case dropWhile (== TokNewline) ts of
        rest@(t : _) | absorbs t -> collapse rest
        rest                     -> TokNewline : collapse rest
    collapse (t : ts)
      | absorbs t = t : collapse (dropWhile (== TokNewline) ts)
      | otherwise = t : collapse ts

    trim = dropWhile (== TokNewline) . dropTrailing
    dropTrailing = reverse . dropWhile (== TokNewline) . reverse

    absorbs t =
      t == TokKleisli || t == TokOrElse || t == TokOrClose
        || t == TokBarBar

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
-- row), then >=> (Kleisli), then >> / >>>, then juxtaposition.  So each
-- LINE is a row, `a >> b | c >> d` is (a >> b) | (c >> d) — mirroring
-- the type grammar, where juxtaposition binds tighter than | — and
-- `p >=> a >> b >=> q` Kleisli-composes whole >>-chains.
parseProgram :: String -> Either String Term
parseProgram input = do
  toks <- normalizeToks <$> tokenize input
  (term, rest) <- parseProgramToks toks
  case rest of
    [] -> Right term
    _  -> Left $ "Unexpected tokens at end: " ++ show rest

-- program level: rows joined by newline
-- `x y z ->` is a postfix binder: it names the top wires and the REST
-- of the current scope is the body (an OpenAbs over those names).  It
-- may open a scope (`def f = x y -> …`) or appear as a pipeline stage
-- after a newline (`… \n x y -> …` ≡ `… >> (x y -> …)`).  A run of
-- identifiers immediately followed by `->` is a binder.
parseProgramToks :: [Token] -> Either String (Term, [Token])
parseProgramToks toks =
  case binderPrefix toks of
    Just (ps, rest) -> mkAbs ps rest
    Nothing -> do
      (t0, rest) <- parseRow toks
      loop t0 rest
  where
    loop acc (TokNewline : rest)
      | Just (ps, r) <- binderPrefix rest = do
          (abs', r') <- mkAbs ps r
          Right (Seq acc abs', r')
      | otherwise = do
          (t, rest') <- parseRow rest
          loop (Seq acc t) rest'
    loop acc rest = Right (acc, rest)

    mkAbs toks0 rest = do
      -- split the parameter list into names, `_` passthroughs and a
      -- trailing `...`.  The stage vocabulary applies, with one
      -- ordering rule: names come first (they sit deepest), then any
      -- `_`, then at most one `...` last.
      (slots, hasRest) <- classifyParams toks0
      let ns = [ n | Just n <- slots ]
      case [ p | (p, n) <- zip ns [0 :: Int ..], p `elem` take n ns ] of
        (p : _) -> Left $ "Duplicate parameter: " ++ p
        []      -> Right ()
      (body, rest') <- parseProgramToks rest
      Right (OpenAbs slots hasRest body, rest')

    -- slots in written order; `_` is an unnamed slot, `...` (last only)
    -- opens the body's input
    classifyParams = go []
      where
        go acc []                 = Right (reverse acc, False)
        go acc [TokEllipsis]      = Right (reverse acc, True)
        go _   (TokEllipsis : _)  =
          Left "'...' must be the last parameter of a binder"
        go acc (TokIdent "_" : r) = go (Nothing : acc) r
        go acc (TokIdent n : r)   = go (Just n : acc) r
        go _   _                  = Left "Malformed parameter list"

    -- a maximal run of identifiers (and `_`/`...`) immediately followed
    -- by `->`; the newline(s) after the arrow are absorbed so the body
    -- may start on the next line (`x y ->` on its own pipeline stage)
    binderPrefix ts =
      case span isParamTok ts of
        (ids@(_ : _), TokArrow : r) ->
          Just (ids, dropWhile (== TokNewline) r)
        _                           -> Nothing
    isParamTok (TokIdent _) = True
    isParamTok TokEllipsis  = True
    isParamTok _            = False

-- row level: sequences joined by |, optional trailing `| ...` residual
parseRow :: [Token] -> Either String (Term, [Token])
parseRow toks =
  case toks of
    -- a leading `|` defaults the first alternative to identity:
    -- `(| f)` ≡ `(pass | f)`, `(| f | g)` ≡ `(pass | f | g)`.  Lets a
    -- vertical row put every arm on a `|`-led line.
    (TokBar : _) -> loop [Prim "pass"] toks
    _            -> do (t0, rest) <- parseKleisli toks
                       loop [t0] rest
  where
    loop acc (TokBar : TokEllipsis : rest)
      | endsRow rest = Right (Alts (reverse acc) True, rest)
      | otherwise    = Left "'| ...' must end its row"
    -- a trailing `|` defaults the LAST alternative to identity:
    -- `(f |)` ≡ `(f | pass)`
    loop acc (TokBar : rest)
      | endsRow rest = Right (Alts (reverse (Prim "pass" : acc)) False, rest)
    loop acc (TokBar : rest) = do
      (t, rest') <- parseKleisli rest
      loop (t : acc) rest'
    loop [t] rest = Right (t, rest)
    loop acc rest = Right (Alts (reverse acc) False, rest)

    endsRow (TokNewline : _) = True
    endsRow (TokRParen : _)  = True
    endsRow (TokRBrack : _)  = True
    endsRow []               = True
    endsRow _                = False

-- kleisli level: >>-sequences joined by >=>.  Pure parse-time sugar for
-- composition in the sum monad — the desugaring is the `and` idiom:
--   t1 >=> t2   ≡   t1 >> (t2 | in2) >> merge
-- (t2 runs on the hit track; the miss track re-injects untouched).
parseKleisli :: [Token] -> Either String (Term, [Token])
parseKleisli toks = do
  (s0, rest) <- parseSeqStmt toks
  loop (desugarStmt s0) rest
  where
    loop acc (TokKleisli : rest) = do
      (s, rest') <- parseSeqStmt rest
      loop (kleisli acc (desugarStmt s)) rest'
    loop acc (TokOrElse : rest) = do
      (s, rest') <- parseSeqStmt rest
      loop (orElse acc (desugarStmt s)) rest'
    loop acc (TokOrClose : rest) = do
      (s, rest') <- parseSeqStmt rest
      loop (orClose acc (desugarStmt s)) rest'
    loop acc rest = Right (acc, rest)

    -- >=> threads the hit track (bind of (·|E)); >?> threads the miss
    -- track (bind of (B|·)): keep an answer, else try the next stage
    kleisli t1 t2 =
      Seq t1 (Seq (Alts [t2, Prim "in2"] False) (Prim "merge"))
    orElse t1 t2 =
      Seq t1 (Seq (Alts [Prim "in1", t2] False) (Prim "merge"))
    orClose t1 t2 =
      Seq t1 (Seq (Alts [Prim "pass", t2] False) (Prim "merge"))

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

-- || e1 || e2 || … : a vertical list literal (a product of lanes).
-- Each lane is a single juxtaposition stage (the user writes [P] [F]
-- for guards); the whole thing is ONE list value, built by nil/cons.
-- Keeps `|` (TokBar) entirely for sums.  This is the ONLY list
-- literal — the flat form is (e1 e2 … ; pack).
parseBarBarList :: [Token] -> Either String (Term, [Token])
parseBarBarList (TokBarBar : rest) = do
  (lane, rest') <- parseStage rest
  go [stageAtoms lane] rest'
  where
    go acc (TokBarBar : r) = do
      (lane, r') <- parseStage r
      go (stageAtoms lane : acc) r'
    go acc r = Right (desugarList (reverse acc), r)
parseBarBarList ts = Left $ "Expected '||' to start a list, got: " ++ show ts

-- build a list value from lanes with nil/cons (the || desugaring)
desugarList :: [[Term]] -> Term
desugarList es = foldl step (Prim "nil") (reverse es)
  where
    step acc atoms = Seq acc (Seq (Tensor (atoms ++ [Prim "pass"]))
                                  (Prim "cons"))

parseStage :: [Token] -> Either String (Stage, [Token])
parseStage = go []
  where
    go [] ts@(TokBarBar : _) = do
      (lst, rest') <- parseBarBarList ts
      go [lst] rest'
    -- case(b1, …, bn): eliminate a right-nested sum (X1 | (X2 | … | Xn))
    -- by one handler per track, all landing on a common result.  Each
    -- branch is a full program spliced BARE onto its arm (no quoting,
    -- like the >=> desugar); the desugaring is the nested rows + merge.
    go acc (TokIdent "case" : TokLParen : rest) = do
      (branches, rest') <- parseCaseBranches rest
      go (desugarCase branches : acc) rest'
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
-- A delimited scope (group or quote body).  Binder recognition lives
-- in parseProgramToks now, so `(x y -> body)` and `[x y -> body]` are
-- handled there (a leading binder in the delimited scope).
parseDelimited :: [Token] -> Either String (Term, [Token])
parseDelimited = parseProgramToks

-- case(b1, …, bn): the coproduct eliminator for a right-nested sum.
--   case(a)          = a
--   case(a, b, …)    = (a | case(b, …)) >> merge
-- so case(a, b, c) is (a | (b | c) >> merge) >> merge, mapping the
-- nested sum (A | (B | (C))) onto the arms' common result.
desugarCase :: [Term] -> Term
desugarCase []       = Prim "pass"
desugarCase [b]      = b
desugarCase (b : bs) = Seq (Alts [b, desugarCase bs] False) (Prim "merge")

-- Branches of case(…): comma-separated FULL programs (unlike list(…)
-- elements, which are bare juxtapositions).  parseProgramToks stops at
-- the comma / close paren, so a branch may use >>, rows, binders, etc.
parseCaseBranches :: [Token] -> Either String ([Term], [Token])
parseCaseBranches (TokRParen : rest) = Right ([], rest)
parseCaseBranches toks = do
  (b, rest) <- parseProgramToks toks
  case rest of
    (TokComma : rest')  -> do
      (bs, rest'') <- parseCaseBranches rest'
      Right (b : bs, rest'')
    (TokRParen : rest') -> Right ([b], rest')
    _ -> Left "Expected ',' or ')' in case(…)"

--------------------------------------------------------------------------------
-- 6.5 Type aliases (stage 1: transparent, display-only)
--
-- `type Name = rhs` / `type Name(p, q) = rhs` declares a name for an
-- element-type structure (typically a sum). Aliases never touch
-- inference or unification: they are expanded away at declaration time
-- (alias references in a RHS) and folded back at display time.  Bodies
-- are closed (no stack/row tails); parameters range over single
-- element types; Fn⟨…⟩ is not expressible in stage-1 type syntax.
--------------------------------------------------------------------------------

data Alias = Alias
  { aName   :: String
  , aParams :: [SVar]
  , aBody   :: Ty
  } deriving (Eq, Show)

-- A recursive `type` declaration: a NOMINAL data type.  Name(args)
-- unifies only with itself (argwise), never with its unfolding; the
-- generated coercions `Name` (roll) and `Name?` (unroll) are the only
-- doors, and both are runtime no-ops.
data DataDecl = DataDecl
  { dName   :: String
  , dParams :: [SVar]
  , dBody   :: Ty
  } deriving (Eq, Show)

dataSig :: DataDecl -> (String, Int)
dataSig d = (dName d, length (dParams d))

-- The schemes and runtime entries a data declaration contributes:
--   Name   : ∀params. body ⇒ Name(params)      (roll)
--   unName : ∀params. Name(params) ⇒ body      (unroll)
dataDeclArtifacts :: DataDecl
                  -> ([(String, Scheme)], [(String, (Int, Bool, Term))])
dataDeclArtifacts d =
  ( [ (dName d,          Forall [] ps [] [] (Arrow bodyStack namedStack))
    , ("un" ++ dName d,  Forall [] ps [] [] (Arrow namedStack bodyStack)) ]
      ++ mergeSchemes
  , [ (dName d,         (rollArity, rollOpen, rollTerm))
    , ("un" ++ dName d, (1, False, unrollTerm)) ]
      ++ mergeRuns )
  where
    ps         = dParams d
    namedStack = SCons (TData (dName d) (map STail ps)) SEnd
    rollOpen   = openTailedS bodyStack
    -- an n-ary uniform collapse for this declaration's arity: the
    -- runtime merge strips any tag; only the SCHEME is arity-specific,
    -- so we generate it per declaration (the counting-theorem dodge)
    (mergeSchemes, mergeRuns) =
      case dBody d of
        TSum row | k >= 2 ->
          ( [ ("merge" ++ dName d
            , Forall [] [SV "ρ"] [] []
                (Arrow (SCons (TSum uniformRow) SEnd) (STail (SV "ρ")))) ]
          , [ ("merge" ++ dName d, (1, False, Prim "merge")) ] )
          where
            k = rowLen row
            uniformRow =
              foldr RCons RNil (replicate k (STail (SV "ρ")))
            rowLen RNil        = 0
            rowLen (RTail _)   = 0
            rowLen (RCons _ r) = 1 + rowLen r
        _ -> ([], [])
    -- single-alternative bodies get doors against the field stack
    -- (Person : Str Int => Person); multi-alternative bodies coerce
    -- the sum wire itself.
    (bodyStack, rollArity, rollTerm, unrollTerm) =
      case dBody d of
        TSum (RCons st RNil) ->
          (st, closedArity st, Prim "in1", Prim "merge")
        _ ->
          (SCons (dBody d) SEnd, 1, Prim "id", Prim "id")
    -- (rollOpen marks splice-shaped field stacks segment-consuming)

-- Generated eliminator: definition by points.  For
--   type Name(ps) = (alt1 | … | altk)
-- emit (as ordinary Braid source, name and body):
--   foldName = (f1 … fk t -> t >> unName >> (C1 | … | Ck) >> merge)
-- where Ci applies fi to alternative i's payload with every recursive
-- slot (an element exactly Name(ps)) already folded.  Bodies that are
-- not sums get no fold; recursion nested under other constructors
-- (e.g. List(Rose(a))) is passed to the case untransformed.
dataFoldSrc :: DataDecl -> Maybe (String, String)
dataFoldSrc d =
  case dBody d of
    TSum row -> do
      alts <- rowAlts row
      let k      = length alts
          fs     = [ "f" ++ show i | i <- [1 .. k] ]
          selfTy = TData (dName d) (map STail (dParams d))
          fname  = "fold" ++ dName d

          -- closed alternative: recursive slots at known positions,
          -- pre-fold in place (classic; cases see payload order)
          compClosed fi payload
            | null payload = Just (fi ++ " ... >> apply")
            | otherwise =
                let xs = [ "x" ++ show j | j <- [1 .. length payload] ]
                    slot (x, ty)
                      | ty == selfTy =
                          "(" ++ unwords (fs ++ [x]) ++ " >> " ++ fname ++ ")"
                      | otherwise = "(" ++ x ++ ")"
                    slots  = map slot (zip xs payload)
                    stages =
                      head slots
                        : [ unwords (replicate n "_") ++ " " ++ sl
                          | (n, sl) <- zip [1 :: Int ..] (tail slots) ]
                    body = intercalate " >> " stages
                             ++ " >> " ++ fi ++ " ... >> apply"
                in Just ("(" ++ unwords xs ++ " -> " ++ body ++ ")")

          -- splice alternative (v ⧺ … self): supported shape is a
          -- single trailing recursive slot; rotLast brings it to the
          -- front, it pre-folds, and the case sees FOLDED FIRST then
          -- the element wires
          -- the eta-restrictor (r2 -> r2) pins the fold result to one
          -- wire, closing the wrapper's output so the recursive knot
          -- assembles (splice folds have single-wire results)
          compSplice fi st =
            case st of
              SSplice _ (SCons ty SEnd)
                | ty == selfTy ->
                    Just ("rotLast >> (t2 -> "
                            ++ unwords (fs ++ ["t2"]) ++ " >> " ++ fname
                            ++ " >> (r2 -> r2)) ... >> " ++ fi
                            ++ " ... >> apply")
              _ -> Nothing

          comp (fi, st)
            | not (hasSplice st) = compClosed fi (stackElems st)
            | otherwise          = compSplice fi st

      cs <- mapM comp (zip fs alts)
      let src = case cs of
            [c] -> "(" ++ unwords (fs ++ ["t"]) ++ " -> t >> un"
                     ++ dName d ++ " >> " ++ c ++ ")"
            _   -> "(" ++ unwords (fs ++ ["t"]) ++ " -> t >> un"
                     ++ dName d ++ " >> ("
                     ++ intercalate " | " cs ++ ") >> merge"
                     ++ dName d ++ ")"
      pure (fname, src)
    _ -> Nothing
  where
    rowAlts RNil          = Just []
    rowAlts (RTail _)     = Nothing
    rowAlts (RCons st r)  = (st :) <$> rowAlts r
    hasSplice (SSplice _ _) = True
    hasSplice (SCons _ r)   = hasSplice r
    hasSplice _             = False
    stackElems SEnd          = []
    stackElems (STail _)     = []
    stackElems (SSplice _ r) = stackElems r
    stackElems (SCons t st)  = t : stackElems st

occursData :: String -> Ty -> Bool
occursData n = goT
  where
    goT (TData m as)        = m == n || any goS as
    goT (TSum r)            = goR r
    goT (TFn (Arrow i o))   = goS i || goS o  -- recursion THROUGH a Fn is codata
    goT _                   = False
    goR (RCons st r) = goS st || goR r
    goR _            = False
    goS (SCons t st)   = goT t || goS st
    goS (SSplice _ st) = goS st
    goS _              = False

lookupAlias :: String -> [Alias] -> Maybe Alias
lookupAlias n = go
  where
    go [] = Nothing
    go (al : rest) | aName al == n = Just al
                   | otherwise     = go rest

-- Parse a whole `type …` declaration line (aliases and data types in
-- scope are needed to resolve references in the RHS; the declared name
-- itself is in scope for self-reference, which makes the declaration a
-- nominal data type rather than a transparent alias).
parseTypeLine :: [Alias] -> [(String, Int)] -> String
              -> Either String (Either Alias DataDecl)
parseTypeLine aliases dataSigs line =
  case break (== '=') line of
    (lhs, '=' : rhs) -> do
      (kw, name, params) <- parseHead lhs
      let sigs = (name, length params) : dataSigs
      body <- parseTyBody aliases sigs params rhs
      if all (\p -> p `elem` tyParams body) params
        then Right ()
        else Left $ "Type alias " ++ name
                 ++ ": every parameter must occur in the body"
      -- one-splice discipline: a stack may mention at most one param
      case [ st | st <- stacksOf body
               , length (filter (`elem` params) (openVarsS st)) > 1 ] of
        (st : _) -> Left $ "Type " ++ name
                       ++ ": ambiguous product split — the stack '"
                       ++ show st ++ "' mentions more than one parameter"
        []       -> Right ()
      -- `data` is always nominal; `type` is a transparent alias unless
      -- self-recursive (which forces nominality)
      pure $ if kw == "data" || occursData name body
               then Right (DataDecl name params body)
               else Left  (Alias name params body)
    _ -> Left $ "Malformed type declaration (missing '='): " ++ line
  where
    parseHead lhs = do
      toks <- normalizeToks <$> tokenize lhs
      case toks of
        [TokIdent kw, TokIdent name]
          | kw `elem` ["type", "data"], validName name ->
              Right (kw, name, [])
        (TokIdent kw : TokIdent name : TokLParen : rest)
          | kw `elem` ["type", "data"], validName name ->
              (,,) kw name <$> paramList rest
        _ -> Left $ "Malformed type declaration: " ++ line
    paramList (TokIdent p : TokComma : rest) = (SV p :) <$> paramList rest
    paramList [TokIdent p, TokRParen]        = Right [SV p]
    paramList _ = Left "Malformed type parameter list"
    validName n = n `notElem` ["Int", "Str", "Sym", "Fn", "type", "data", "•"]
    tyParams t = let (_, ss, _, _) = varsOfTy t in ss
    -- every stack appearing anywhere in a type body
    stacksOf :: Ty -> [SType]
    stacksOf (TSum r)     = rowStacks r
    stacksOf (TData _ as) = as ++ concatMap stackInner as
    stacksOf _            = []
    rowStacks RNil         = []
    rowStacks (RTail _)    = []
    rowStacks (RCons st r) = st : stackInner st ++ rowStacks r
    stackInner (SCons t st)   = stacksOf t ++ stackInner st
    stackInner (SSplice _ st) = stackInner st
    stackInner _              = []

-- Parse a full RHS: one element-type expression, nothing left over.
parseTyBody :: [Alias] -> [(String, Int)] -> [SVar] -> String
            -> Either String Ty
parseTyBody aliases dataSigs params src = do
  toks <- normalizeToks <$> tokenize src
  (t, rest) <- parseTyElem aliases dataSigs params toks
  case rest of
    [] -> Right t
    _  -> Left $ "Unexpected tokens after type expression: " ++ show rest

parseTyElem :: [Alias] -> [(String, Int)] -> [SVar] -> [Token]
            -> Either String (Ty, [Token])
parseTyElem aliases dataSigs params toks = case toks of
  -- Fn⟨Σ ⇒ Θ⟩ (Unicode, mirrors :t output) or Fn(Σ -> Θ) (ASCII): a
  -- reified program as an element type.  The inner stacks parse like
  -- any type stack (params splice, • is empty, Fn nests).
  (TokIdent "Fn" : TokLAngle : rest) -> parseFn TokRAngle rest
  (TokIdent "Fn" : TokLParen : rest) -> parseFn TokRParen rest
  (TokIdent "Fn" : _) ->
    Left "Fn must be written Fn⟨Σ ⇒ Θ⟩ (or Fn(Σ -> Θ))"
  (TokLParen : rest) -> do
    (alts, rest') <- goAlts rest
    pure (TSum (foldr RCons RNil alts), rest')
  (TokIdent "Int" : rest) -> pure (TInt, rest)
  (TokIdent "Str" : rest) -> pure (TStr, rest)
  (TokIdent "Sym" : rest) -> pure (TSym, rest)
  (TokIdent name : TokLParen : rest)
    | Just arity <- lookup name dataSigs -> do
        (args, rest') <- goArgs rest
        if length args == arity
          then pure (TData name args, rest')
          else Left $ "Type " ++ name ++ " expects "
                   ++ show arity ++ " argument(s)"
    | Just al <- lookupAlias name aliases -> do
        (args, rest') <- goArgs rest
        body <- applyAlias al args
        pure (body, rest')
  (TokIdent name : rest)
    | SV name `elem` params ->
        Left $ "Type parameter " ++ name
             ++ " is a stack: it cannot sit inside another element"
    | Just 0 <- lookup name dataSigs -> pure (TData name [], rest)
    | Just _ <- lookup name dataSigs ->
        Left $ "Type " ++ name ++ " expects arguments"
    | Just al <- lookupAlias name aliases ->
        if null (aParams al)
          then pure (aBody al, rest)
          else Left $ "Type alias " ++ name ++ " expects arguments"
    | otherwise -> Left $ "Unknown type name: " ++ name
  _ -> Left "Expected a type expression"
  where
    -- sum alternatives: stack (| stack)* )
    goAlts ts = do
      (st, rest) <- goStack ts
      case rest of
        (TokBar : rest')    -> do
          (alts, rest'') <- goAlts rest'
          pure (st : alts, rest'')
        (TokRParen : rest') -> pure ([st], rest')
        _ -> Left "Expected '|' or ')' in sum type"
    -- a stack: • or a run of elements; a parameter occurrence splices
    goStack (TokIdent "•" : rest) = pure (SEnd, rest)
    goStack ts@(TokIdent name : rest)
      | SV name `elem` params = do
          (suffix, rest') <- goStackEnd rest
          pure (ssplice (SV name) suffix, rest')
      | otherwise = goStackElem ts
    goStack ts = goStackElem ts
    goStackElem ts = do
      (t, rest) <- parseTyElem aliases dataSigs params ts
      case rest of
        -- exponent: T^3 repeats one wire; (A B)^3 repeats a segment
        -- (a 1-ary parenthesized "sum" before ^ is read as a segment).
        (TokCaret : rest1) -> do
          (e, rest2) <- expLit rest1
          base <- case t of
            TSum (RCons st RNil) -> Right st
            _                    -> Right (SCons t SEnd)
          if openTailedS base
            then Left "Exponent base must be a closed segment"
            else do
              (suffix, rest') <- goStackEnd rest2
              pure (sexp base e suffix, rest')
        _ -> do
          (suffix, rest') <- goStackEnd rest
          pure (SCons t suffix, rest')
    -- stage 3: literal exponents only.  Exponent VARIABLES arrive with
    -- exponent parameters (design-exponents.md); reject with direction.
    expLit (TokInt k : rest) | k >= 0 = Right (Exp k Nothing, rest)
    expLit (TokIdent nm : _) =
      Left $ "Exponent variables (^" ++ nm ++ ") are not yet supported in "
           ++ "type declarations — only literal exponents (Int^3)"
    expLit _ = Left "Expected an exponent (a number) after '^'"
    goStackEnd rest = case rest of
      (TokBar : _)      -> pure (SEnd, rest)
      (TokRParen : _)   -> pure (SEnd, rest)
      (TokComma : _)    -> pure (SEnd, rest)
      (TokFatArrow : _) -> pure (SEnd, rest)   -- Fn⟨Σ ⇒ …⟩ boundary
      (TokArrow : _)    -> pure (SEnd, rest)   -- Fn(Σ -> …) boundary
      (TokRAngle : _)   -> pure (SEnd, rest)   -- Fn⟨… ⇒ Θ⟩ close
      []                -> pure (SEnd, [])
      _                 -> goStack rest
    -- Fn⟨Σ ⇒ Θ⟩ / Fn(Σ -> Θ): two stacks around an arrow, then `close`
    parseFn close ts = do
      (inSt, rest1) <- goStack ts
      rest2 <- case rest1 of
                 (TokFatArrow : r) -> Right r
                 (TokArrow : r)    -> Right r
                 _ -> Left "Expected '⇒' (or '->') inside a Fn type"
      (outSt, rest3) <- goStack rest2
      case rest3 of
        (t : r) | t == close -> Right (TFn (Arrow inSt outSt), r)
        _ -> Left $ "Expected '"
                 ++ (if close == TokRAngle then "⟩" else ")")
                 ++ "' to close the Fn type"
    -- constructor/alias arguments: each argument is a STACK
    goArgs ts = do
      (st, rest) <- goStack ts
      case rest of
        (TokComma : rest')  -> do
          (args, rest'') <- goArgs rest'
          pure (st : args, rest'')
        (TokRParen : rest') -> pure ([st], rest')
        _ -> Left "Expected ',' or ')' in type arguments"

applyAlias :: Alias -> [SType] -> Either String Ty
applyAlias al args
  | length args /= length (aParams al) =
      Left $ "Type alias " ++ aName al ++ " expects "
           ++ show (length (aParams al)) ++ " argument(s)"
  | otherwise = Right (substStackVars (M.fromList (zip (aParams al) args))
                                      (aBody al))

substStackVars :: Map SVar SType -> Ty -> Ty
substStackVars m = goT
  where
    goT t@(TVarTy _) = t
    goT TInt         = TInt
    goT TStr         = TStr
    goT TSym         = TSym
    goT (TFn (Arrow i o)) = TFn (Arrow (goS i) (goS o))  -- substitute inside Fn
    goT (TSum r)     = TSum (goR r)
    goT (TData n as) = TData n (map goS as)
    goR RNil         = RNil
    goR t@(RTail _)  = t
    goR (RCons s r)  = RCons (goS s) (goR r)
    goS SEnd            = SEnd
    goS t@(STail v)     = M.findWithDefault t v m
    goS (SSplice v s)   =
      appendS (M.findWithDefault (STail v) v m) (goS s)
    goS (SCons t s)     = SCons (goT t) (goS s)

-- One-way match of an alias body against a concrete element type.
-- Parameters bind single element types (nonlinear occurrences must
-- agree); closed rows/stacks only match same-shape closed structure.
matchAlias :: Alias -> Ty -> Maybe [SType]
matchAlias al t = do
  binds <- goT (aBody al) t M.empty
  mapM (`M.lookup` binds) (aParams al)
  where
    goT TInt TInt m = Just m
    goT TStr TStr m = Just m
    goT TSym TSym m = Just m
    goT (TSum rb) (TSum rx) m = goR rb rx m
    goT (TData nb bs) (TData nx xs) m
      | nb == nx && length bs == length xs =
          foldM (\acc (b, x) -> goS b x acc) m (zip bs xs)
    goT (TFn (Arrow ib ob)) (TFn (Arrow ix ox)) m =
      goS ib ix m >>= goS ob ox
    goT _ _ _ = Nothing
    goR RNil RNil m = Just m
    goR (RCons sb rb) (RCons sx rx) m = goS sb sx m >>= goR rb rx
    goR _ _ _ = Nothing
    bindS p x m
      | openTailedS x = Nothing
      | otherwise =
          case M.lookup p m of
            Nothing -> Just (M.insert p x m)
            Just y  -> if x == y then Just m else Nothing
    goS (STail p) x m
      | p `elem` aParams al = bindS p x m
    goS (SSplice p suf) x m
      | p `elem` aParams al =
          let mm = closedArity suf
              n  = closedArity x
          in if openTailedS x || n < mm then Nothing
             else let (pre, post) = splitStackAt (n - mm) x
                  in goS suf post m >>= bindS p pre
    goS SEnd SEnd m = Just m
    goS (SCons tb sb) (SCons tx sx) m = goT tb tx m >>= goS sb sx
    goS _ _ _ = Nothing

-- Folded display: try to rewrite structure back into declared names.
-- Fewest parameters wins; ties go to the earliest alias in the list
-- (callers order user-latest-first, then prelude).
bestAlias :: [Alias] -> Ty -> Maybe (Alias, [SType])
bestAlias aliases t =
  case [ (al, args) | al <- aliases, Just args <- [matchAlias al t] ] of
    [] -> Nothing
    cs -> Just (minimumOn (length . aParams . fst) cs)
  where
    minimumOn f (x : xs) = go x xs
      where go best []       = best
            go best (y : ys) = go (if f y < f best then y else best) ys
    minimumOn _ [] = error "bestAlias: impossible"

showTyA :: [Alias] -> Ty -> String
showTyA as t =
  case bestAlias as t of
    Just (al, args)
      | null args -> aName al
      | otherwise ->
          aName al ++ "(" ++ intercalate ", " (map (showStackA as) args) ++ ")"
    Nothing -> case t of
      TVarTy a  -> show a
      TInt      -> "Int"
      TStr      -> "Str"
      TSym      -> "Sym"
      TFn arr   -> "Fn⟨" ++ showArrowA as arr ++ "⟩"
      TSum row  -> "(" ++ showRowA as row ++ ")"
      TData n [] -> n
      TData n args ->
        n ++ "(" ++ intercalate ", " (map (showStackA as) args) ++ ")"

showRowA :: [Alias] -> SumRow -> String
showRowA as row = intercalate " | " (go row)
  where
    go RNil            = []
    go (RTail v)       = [show v]
    go (RCons st rest) = showStackA as st : go rest

showStackA :: [Alias] -> SType -> String
showStackA _  SEnd        = "•"
showStackA _  (STail v)   = show v
showStackA as st          = unwords (go st)
  where
    go SEnd             = []
    go (STail v)        = [show v]
    go (SCons t rest)   = showTyA as t : go rest
    go (SSplice v rest) = show v : go rest
    go (SExp b e rest)  = showExpAt b e : go rest

showArrowA :: [Alias] -> Arrow -> String
showArrowA as (Arrow s1 s2) = showStackA as s1 ++ " ⇒ " ++ showStackA as s2

showSchemeA :: [Alias] -> Scheme -> String
showSchemeA as (Forall tvars svars rvars nvars arr) =
  "∀ " ++ unwords (map show tvars ++ map show svars ++ map show rvars
                     ++ map show nvars)
       ++ ". " ++ showArrowA as arr

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
appendStack (SExp b e r) s2   = SExp b e (appendStack r s2)
appendStack (STail v) _ =
  error $ "appendStack: open stack " ++ show v
       ++ " in non-final tensor position (remainder discipline violation)"

-- Inference: given an Env and a Term, produce an Arrow and constraints
infer :: Env -> Term -> Infer (Arrow, [Constraint])
infer env p@(Prim _)     = inferOperand env True p
infer env q@(Quote _)    = inferOperand env True q
infer env o@(OpenAbs {}) = inferOperand env True o
infer env a@(Alts {})    = inferOperand env True a

infer env (Tensor ts) = do
  let n = length ts
  results <- sequence
    [ inferOperand env (ix == n - 1) t | (ix, t) <- zip [0 ..] ts ]
  -- Non-final operands are instantiated closed — EXCEPT a recursive
  -- self-reference, whose knot shares open metavariables that nothing
  -- may close.  Report the placement rule instead of panicking in
  -- appendStack (dummy-arrow pattern, cf. ill-typed groups).
  let arrows0 = map fst results
      cs0     = concatMap snd results
      openNonFinal =
        [ () | (Arrow i o, ix) <- zip arrows0 [0 :: Int ..]
             , ix /= n - 1
             , openTailedS i || openTailedS o ]
      (arrows, cs) =
        if null openNonFinal
          then (arrows0, cs0)
          else ( [ if ix == n - 1 || not (openTailedS i || openTailedS o)
                     then a else Arrow SEnd SEnd
                 | (a@(Arrow i o), ix) <- zip arrows0 [0 :: Int ..] ]
               , CFail ("A recursive call (or other open-arity atom) must \
                        \be the final atom of its tensor stage") : cs0 )
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
  | isStrLiteral name =
      pick (Forall [] [] [] [] (Arrow SEnd (SCons TStr SEnd)))
  | isSymLiteral name =
      pick (Forall [] [] [] [] (Arrow SEnd (SCons TSym SEnd)))
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
inferOperand env _ (OpenAbs slots hasRest body) = do
  -- Named open abstraction (x₁ … xₙ [_ …] [...] -> body).  Each name
  -- enters scope as a monomorphic terminal-source producer xᵢ : • ⇒ Aᵢ —
  -- the free metavariable is shared across occurrences, so repeated use
  -- is forced to one consistent type (λ-binding, HM-style).
  --
  -- Slots align with wires positionally (leftmost = deepest, exactly as
  -- atoms align in a tensor stage).  Whatever a slot does NOT name goes
  -- to the body: `_` contributes one wire, `...` an open tail.  So
  --    (x     -> body) : A ⇒ Δ        body :  •  ⇒ Δ   (input-closed)
  --    (x _   -> body) : A B ⇒ Δ      body :  B  ⇒ Δ
  --    (x _ z -> body) : A B C ⇒ Δ    body :  B  ⇒ Δ   (interleaved)
  --    (x ... -> body) : A ρ ⇒ Δ      body :  ρ  ⇒ Δ   (open)
  -- The remainder is handed TO the body (so it can place it with `...`),
  -- unlike `(x -> body) ...`, which routes it around the binder.
  stys <- mapM (const freshTyVarName) slots
  let paramScheme av = Forall [] [] [] [] (Arrow SEnd (SCons (TVarTy av) SEnd))
      env' = foldr (\(p, av) -> M.insert p (paramScheme av)) env
                   [ (n, av) | (Just n, av) <- zip slots stys ]
  (Arrow bi bo, cs) <- infer env' body
  restS <- if hasRest then STail <$> freshSVarName else pure SEnd
  let bodyIn = foldr (SCons . TVarTy) restS
                     [ av | (Nothing, av) <- zip slots stys ]
      inS    = foldr (SCons . TVarTy) restS stys
  pure (Arrow inS bo, CEqStack bi bodyIn : cs)
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
      --
      -- The constraints are PROPAGATED, not discarded: the local solve
      -- only exists to find the closable tails, but the group may
      -- constrain OUTER metavariables (a binder parameter used inside —
      -- (x >> negative) forces x : Int), and dropping cs would lose
      -- that link (the old soundness hole: sign typed a0 ⇒ Str and
      -- crashed on "oops" >> sign).  Re-solving them globally is
      -- redundant for the interior but preserves every outer binding.
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
          in pure (substOnce (Subst M.empty sm M.empty M.empty) arr', cs)

-- The open stack variables of a stack: the tail, plus any splices.
openVarsS :: SType -> [SVar]
openVarsS (STail v)      = [v]
openVarsS (SCons _ r)    = openVarsS r
openVarsS (SSplice v r)  = v : openVarsS r
openVarsS (SExp _ _ r)   = openVarsS r
openVarsS SEnd           = []

tailVar :: SType -> Maybe SVar
tailVar (STail v)    = Just v
tailVar (SCons _ r)  = tailVar r
tailVar _            = Nothing

isIntLiteral :: String -> Bool
isIntLiteral ('-' : ds) = not (null ds) && all isDigit ds
isIntLiteral name       = not (null name) && all isDigit name

isStrLiteral :: String -> Bool
isStrLiteral ('"' : _) = True
isStrLiteral _         = False

isSymLiteral :: String -> Bool
isSymLiteral ('.' : _ : _) = True
isSymLiteral _             = False

-- The lexical injection family: in1, in2, … — position fixed, width
-- open via the row tail.
injIndex :: String -> Maybe Int
injIndex "here"  = Just 1         -- here ≡ in1: start a sum at the front
injIndex "ok"    = Just 1         -- ok ≡ in1: return of the sum monad
injIndex "miss"  = Just 2         -- miss ≡ in2: stay on the miss track
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
  in Forall [] (ps ++ [d]) [rv] []
       (Arrow (STail d) (SCons (TSum row) SEnd))

-- Integer literals are terminal-source: • ⇒ Int.  Constants have NO
-- implicit remainder — pushing onto a nonempty stack requires explicit
-- `...` (e.g. `1 ...` : ρ ⇒ Int ρ).  See spec-update-exponentials.md.
intLitScheme :: Scheme
intLitScheme = Forall [] [] [] [] (Arrow SEnd (SCons TInt SEnd))

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
      applyTy = Forall [] [gam, del] [] []
        (Arrow (SCons fnGD (STail gam)) (STail del))
      -- merge : (Θ | Θ) ⇒ Θ — the binary codiagonal ∇
      mergeTy = Forall [] [SV "Θ"] [] []
        (Arrow (SCons (TSum (RCons (STail (SV "Θ"))
                       (RCons (STail (SV "Θ")) RNil))) SEnd)
               (STail (SV "Θ")))
      -- there : (σ) ⇒ (Δ | σ) — widen a sum with a new front track
      -- (tags shift by one; here ≡ in1, inN ≡ here >> there^(n-1))
      thereTy = Forall [] [SV "Δ"] [RV "σ"] []
        (Arrow (SCons (TSum (RTail (RV "σ"))) SEnd)
               (SCons (TSum (RCons (STail (SV "Δ")) (RTail (RV "σ")))) SEnd))
      -- loop : Fn⟨Σ ⇒ (Σ | Θ)⟩ Σ ⇒ Θ — Elgot iteration: the body routes
      -- to continue (re-enter) or done (exit)
      loopTy =
        let sg = SV "Σ"; th = SV "Θ"
            body = TFn (Arrow (STail sg)
                     (one (TSum (RCons (STail sg)
                           (RCons (STail th) RNil)))))
        in Forall [] [sg, th] [] []
             (Arrow (SCons body (STail sg)) (STail th))
      int2 = SCons TInt (one TInt)
      codeStructTy =
        TData "List"
          [SCons (TData "List" [SCons (TData "Atom" []) SEnd]) SEnd]
      int2Router = Forall [] [] [] []
        (Arrow int2
               (one (TSum (RCons int2 (RCons int2 RNil)))))
      eqTy = Forall [a] [] [] []
        (let aa = SCons ta (one ta)
         in Arrow aa (one (TSum (RCons aa (RCons aa RNil)))))
      binIntTy = Forall [] [] [] []
        (Arrow (SCons TInt (one TInt)) (one TInt))
      -- Bool ≡ (• | •): two payload-free tracks; true = in1, false = in2
      tBool    = TSum (RCons SEnd (RCons SEnd RNil))
      boolLit  = Forall [] [] [] [] (Arrow SEnd (one tBool))
      -- foldExp: the eliminator of an exponent bundle aⁿ (the stack-level
      -- foldList).  n is erased; at runtime the bundle is the final
      -- segment and its width is the witness.
      nExp = Exp 0 (Just (NV "n"))
      foldExpTy =
        let stepArr = Arrow (SCons tb (one ta)) (one tb)
        in Forall [a, b] [] [] [NV "n"]
             (Arrow (SCons (TFn stepArr)
                      (SCons tb (SExp (one ta) nExp SEnd)))
                    (one tb))
      -- foldExp2: the two-wide twin — eliminate a bundle of PAIRS
      -- (a c)ⁿ; the step sees [acc, a, c]
      foldExp2Ty =
        let c  = TV "c"
            tc = TVarTy c
            stepArr = Arrow (SCons tb (SCons ta (one tc))) (one tb)
        in Forall [a, b, c] [] [] [NV "n"]
             (Arrow (SCons (TFn stepArr)
                      (SCons tb (SExp (SCons ta (one tc)) nExp SEnd)))
                    (one tb))
      -- GLA generators, width-polymorphic in n (design-exponents.md)
      dupNTy = Forall [a] [] [] [NV "n"]
        (Arrow (SExp (one ta) nExp SEnd)
               (SExp (one ta) nExp (SExp (one ta) nExp SEnd)))
      addNTy = Forall [] [] [] [NV "n"]
        (Arrow (SExp (one TInt) nExp (SExp (one TInt) nExp SEnd))
               (SExp (one TInt) nExp SEnd))
      zipNTy = Forall [a, b] [] [] [NV "n"]
        (Arrow (SExp (one ta) nExp (SExp (one tb) nExp SEnd))
               (SExp (SCons ta (one tb)) nExp SEnd))
      scaleNTy = Forall [] [] [] [NV "n"]
        (Arrow (SCons TInt (SExp (one TInt) nExp SEnd))
               (SExp (one TInt) nExp SEnd))
  in M.fromList
       [ ("id",    Forall [a]    [] [] [] (Arrow (one ta) (one ta)))
       , ("_",     Forall [a]    [] [] [] (Arrow (one ta) (one ta)))  -- hole: id
       , ("swap",  Forall [a, b] [] [] []
           (Arrow (SCons ta (one tb)) (SCons tb (one ta))))
       , ("dup",   Forall [a]    [] [] [] (Arrow (one ta) (SCons ta (one ta))))
       , ("drop",  Forall [a]    [] [] [] (Arrow (one ta) SEnd))
       , ("pass",  Forall []     [rho] [] [] (Arrow (STail rho) (STail rho)))
         -- the terminal morphism: forget the whole segment
       , ("forget", Forall []    [rho] [] [] (Arrow (STail rho) SEnd))
         -- rotate the LAST wire of the segment to the front: the
         -- reach-the-end primitive, typed via a splice
       , ("rotLast", Forall [a]  [rho] [] []
           (Arrow (SSplice rho (SCons ta SEnd))
                  (SCons ta (STail rho))))
       , ("+",     binIntTy)
       , ("*",     binIntTy)
       , ("print", Forall [a]    [] [] [] (Arrow (one ta) SEnd))
       , ("true",  boolLit)
       , ("false", boolLit)
       , ("eq?",       eqTy)
       , ("lt?",       int2Router)
       , ("-",         binIntTy)
       , ("div",       binIntTy)
       , ("mod",       binIntTy)
       , ("gt?",       int2Router)
       , ("gte?",      int2Router)
       , ("lte?",      int2Router)
       , ("cat",       Forall [] [] [] []
           (Arrow (SCons TStr (one TStr)) (one TStr)))
       , ("toStr",     Forall [a] [] [] [] (Arrow (one ta) (one TStr)))
       , ("asInt?",    Forall [] [] [] []
           (Arrow (one TStr)
                  (one (TSum (RCons (one TInt)
                        (RCons (one TStr) RNil))))))
       , ("symStr",    Forall [] [] [] [] (Arrow (one TSym) (one TStr)))
       , ("unparse",   Forall [] [] [] []
           (Arrow (SCons codeStructTy SEnd) (one TStr)))
       , ("parse",     Forall [] [] [] []
           (Arrow (one TStr)
                  (one (TSum (RCons (one codeStructTy)
                        (RCons (one TStr) RNil))))))
       , ("readFile",  Forall [] [] [] []
           (Arrow (one TStr)
                  (one (TSum (RCons (one TStr) (RCons (one TStr) RNil))))))
       , ("writeFile", Forall [] [] [] []
           (Arrow (SCons TStr (one TStr))
                  (one (TSum (RCons SEnd (RCons (one TStr) RNil))))))
       , ("evalCode",  Forall [] [gam, del] [] []
           (Arrow (SCons codeStructTy (STail gam))
                  (one (TSum (RCons (STail del)
                        (RCons (SCons TStr (STail gam)) RNil))))))
       , ("reflect",   Forall [] [gam, del] [] []
           (Arrow (one (TFn (Arrow (STail gam) (STail del))))
                  (one (TSum (RCons (one codeStructTy)
                        (RCons (one TStr) RNil))))))
       , ("apply",     applyTy)
       , ("there",     thereTy)
       , ("merge",     mergeTy)
       , ("loop",      loopTy)
       , ("foldExp",   foldExpTy)
       , ("foldExp2",  foldExp2Ty)
       , ("dupN",      dupNTy)
       , ("addN",      addNTy)
       , ("zipN",      zipNTy)
       , ("scaleN",    scaleNTy)
       ]

--------------------------------------------------------------------------------
-- 8. Driver: parse + infer + solve
--------------------------------------------------------------------------------

primsIn :: Term -> [String]
primsIn (Prim n)        = [n]
primsIn (Tensor ts)     = concatMap primsIn ts
primsIn (Seq t u)       = primsIn t ++ primsIn u
primsIn (Quote t)       = primsIn t
primsIn (OpenAbs slots _ t) =
  [ n | n <- primsIn t, n `notElem` [ x | Just x <- slots ] ]
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
    go (Alts cs r)      = Alts (map go cs) r
    go t@(OpenAbs slots hasRest b)
      | Just "recurse" `elem` slots = t
      | otherwise                   = OpenAbs slots hasRest (go b)

-- Infer a term's principal arrow in a given environment.
inferTermIn :: Env -> Term -> Either String Arrow
inferTermIn env term =
  case nub [ n | n <- primsIn term
               , not (isIntLiteral n)
               , not (isStrLiteral n)
               , not (isSymLiteral n)
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
                   , not (isStrLiteral n)
                   , not (isSymLiteral n)
                   , not (M.member n env)
                   , Nothing <- [injIndex n] ] of
        (n : _) -> Left $ "Unknown primitive: " ++ n
        [] -> do
          let (arr, cs) = runInfer0 $ do
                fi <- freshSVarName
                fo <- freshSVarName
                let mono = Forall [] [] [] []
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
  let (tvs, svs, rvs, nvs) = varsOfArrow arr
      tm = M.fromList
             (zip tvs [ TVarTy (TV ("a" ++ show n)) | n <- [0 :: Int ..] ])
      sm = M.fromList
             (zip svs [ STail (SV ("ρ" ++ show n)) | n <- [0 :: Int ..] ])
      rm = M.fromList
             (zip rvs [ RTail (RV ("σ" ++ show n)) | n <- [0 :: Int ..] ])
      nm = M.fromList
             (zip nvs [ Exp 0 (Just (NV ("n" ++ show n))) | n <- [0 :: Int ..] ])
  in substOnce (Subst tm sm rm nm) arr

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
freeVarsScheme (Forall tv sv rv nv arr) =
  let (ft, fs, fr, fn) = freeVarsArrow arr
  in (ft \\ tv, fs \\ sv, fr \\ rv, fn \\ nv)

freeVarsEnv :: Env -> Vars
freeVarsEnv env =
  foldr (catVars . freeVarsScheme) noVars (M.elems env)

-- Generalize all free type, stack, row, and exponent variables not
-- fixed by the environment.
generalize :: Env -> Arrow -> Scheme
generalize env arr =
  let (ftv, fsv, frv, fnv) = freeVarsArrow arr
      (etv, esv, erv, env') = freeVarsEnv env
  in Forall (ftv \\ etv) (fsv \\ esv) (frv \\ erv) (fnv \\ env') arr

-- A checked module: definitions in order, plus an optional main program.
data Module = Module
  { modEnv     :: Env
  , modDefs    :: [(String, Scheme, Term)]
  , modAliases :: [Alias]          -- match order: latest first
  , modDatas   :: [DataDecl]       -- recursive (nominal) declarations
  , modDocs    :: Map String String -- ## doc comments, by def/type name
  , modMain    :: Maybe (Term, Arrow)
  }

-- Split source into `def name = body` lines, `type …` declaration
-- lines, and the main program (all remaining lines, in order, joined
-- by newline-sequencing).  A `## text` line is a doc comment: it binds
-- to the next def or type line (consecutive doc lines join); doc text
-- preceding a plain program line is dropped.
splitDefs :: String
          -> Either String ( [(String, String, Maybe String)]
                           , [(String, Maybe String)]
                           , String )
splitDefs src = do
  (defs, tys, progLines) <- go Nothing (lines src)
  pure (defs, tys, intercalate "\n" progLines)
  where
    go _ [] = Right ([], [], [])
    go doc (l : rest)
      | Just d <- docLine l =
          go (Just (maybe d (\p -> p ++ " " ++ d) doc)) rest
      | (kw : _) <- words l, kw `elem` ["type", "data"] = do
          (ds, ts, ps) <- go Nothing rest
          pure (ds, (l, doc) : ts, ps)
      | ("def" : _) <- words l = do
          (name, body) <- parseDefLine l
          -- a `#` comment on the `=` line is not code: treat a
          -- comment-only body as blank so the block-body form triggers
          if all isSpace (takeWhile (/= '#') body)
            then do
              -- block body: the following indented lines (blank ends it)
              let indented ln = not (all isSpace ln) && isSpace (head ln)
                  (block, rest') = span indented rest
              if null block
                then Left $ "Empty definition body: " ++ name
                else do
                  (ds, ts, ps) <- go Nothing rest'
                  pure ((name, intercalate "\n" block, doc) : ds, ts, ps)
            else do
              (ds, ts, ps) <- go Nothing rest
              pure ((name, body, doc) : ds, ts, ps)
      | otherwise = do
          (ds, ts, ps) <- go Nothing rest
          pure (ds, ts, l : ps)

    docLine l =
      case dropWhile isSpace l of
        '#' : '#' : txt -> Just (dropWhile isSpace txt)
        _               -> Nothing

    parseDefLine l =
      case break (== '=') l of
        (lhs, '=' : body) ->
          case words lhs of
            ["def", name]
              | not (isIntLiteral name) -> Right (name, body)
            _ -> Left $ "Malformed definition: " ++ l
        _ -> Left $ "Malformed definition (missing '='): " ++ l

-- Check a module against the prelude: user defs and type aliases may
-- shadow prelude ones (once each); the prelude's defs, aliases, and
-- docs are folded into the result so the runtime and printer see them.
checkModule :: String -> Either String Module
checkModule src = do
  m <- checkModuleWith (modEnv preludeModule) preludeNames
                       (modAliases preludeModule)
                       (modDatas preludeModule) src
  let shadowed = map aName (modAliases m) ++ map dName (modDatas m)
      keptPreludeAl =
        [ al | al <- modAliases preludeModule, aName al `notElem` shadowed ]
      keptPreludeDt =
        [ d | d <- modDatas preludeModule, dName d `notElem` shadowed ]
  pure m { modDefs    = modDefs preludeModule ++ modDefs m
         , modAliases = modAliases m ++ keptPreludeAl
         , modDatas   = modDatas m ++ keptPreludeDt
         , modDocs    = modDocs m `M.union` modDocs preludeModule }

-- Check a module starting from a given environment (REPL sessions grow
-- the environment incrementally).  Names in `shadowable` may be
-- redefined once (prelude shadowing); all other redefinition is an
-- error.  `aliases0` are type aliases in scope for RHS references (and
-- shadowable by user `type` lines); only the module's OWN aliases are
-- returned in modAliases (latest first).
checkModuleWith :: Env -> [String] -> [Alias] -> [DataDecl] -> String
                -> Either String Module
checkModuleWith env0 shadow0 aliases0 datas0 src = do
  (defSrcs, tyLines, mainSrc) <- splitDefs src
  (env1, _, _, ownAliases, ownDatas, docs0) <-
    foldM addType (env0, aliases0, datas0, [], [], M.empty) tyLines
  let genDefs =
        [ (fn, body, Just ("definition by points: one quoted case per "
                           ++ "constructor of " ++ dName dd
                           ++ ", recursive slots pre-folded"))
        | dd <- reverse ownDatas, Just (fn, body) <- [dataFoldSrc dd] ]
  (env', _, defsRev, docs) <-
    foldM addDef (env1, shadow0, [], docs0) (genDefs ++ defSrcs)
  mainPart <-
    if all isSpace mainSrc
      then pure Nothing
      else do
        term <- parseProgram mainSrc
        arr  <- inferTermIn env' term
        pure (Just (term, arr))
  -- own lists are built latest-first, which is exactly the match order
  pure (Module env' (reverse defsRev) ownAliases ownDatas docs mainPart)
  where
    preludeTypeNames = map aName aliases0 ++ map dName datas0

    addType (env, aliasesIn, datasIn, ownAl, ownDt, docs) (line, doc) = do
      decl <- parseTypeLine aliasesIn (map dataSig datasIn) line
      let n = either aName dName decl
      if any ((== n) . aName) ownAl || any ((== n) . dName) ownDt
        then Left $ "Duplicate type declaration: " ++ n
        else Right ()
      if n `elem` preludeTypeNames
           || not (any ((== n) . aName) aliasesIn
                   || any ((== n) . dName) datasIn)
        then Right ()
        else Left $ "Duplicate type declaration: " ++ n
      let docs' = maybe docs (\d -> M.insert n d docs) doc
      case decl of
        Left al ->
          pure ( env
               , al : filter ((/= n) . aName) aliasesIn
               , datasIn, al : ownAl, ownDt, docs' )
        Right dd -> do
          -- shadowing a prelude data type replaces its constructors
          let envC
                | n `elem` preludeTypeNames =
                    foldr M.delete env [n, "un" ++ n, "merge" ++ n]
                | otherwise = env
          if M.member n envC || M.member ("un" ++ n) envC
               || M.member ("merge" ++ n) envC
            then Left $ "Type " ++ n
                     ++ ": constructor name collides with an existing definition"
            else Right ()
          let (scs, _) = dataDeclArtifacts dd
          pure ( foldr (uncurry M.insert) envC scs
               , filter ((/= n) . aName) aliasesIn
               , dd : filter ((/= n) . dName) datasIn
               , ownAl, dd : ownDt, docs' )
    addDef (env, shadow, acc, docs) (name, bodySrc, doc) = do
      if M.member name env && name `notElem` shadow
        then Left $ "Duplicate definition: " ++ name
        else Right ()
      term0 <- either (Left . inDef) Right (parseProgram bodySrc)
      let term = substRecurse name term0
          env1 = M.delete name env   -- a shadowed def must not leak in
      arr  <- either (Left . inDef) Right (inferDefTermIn name env1 term)
      let sc = generalize env1 arr
      pure ( M.insert name sc env
           , filter (/= name) shadow
           , (name, sc, term) : acc
           , maybe docs (\d -> M.insert name d docs) doc )
      where inDef e = "in def " ++ name ++ ": " ++ e

--------------------------------------------------------------------------------
-- 10.5 Prelude: derived definitions available in every module and REPL
-- session.  All user code — the primitive set stays minimal.  User defs
-- shadow prelude defs silently.
--------------------------------------------------------------------------------

preludeSrc :: String
preludeSrc = unlines
  [ "## the boolean object: a bare two-way decision"
  , "type Bool = (• | •)"
  , "## an optional value: empty or one element"
  , "type Maybe(a) = (• | a)"
  , "## the list: initial algebra of (• | a X); foldList is generated"
  , "type List(a) = (• | a List(a))"
  , "## the empty list"
  , "def nil = in1 >> List"
  , "## prepend an element"
  , "def cons = in2 >> List"
  , "## open one layer: the asymmetric list router"
  , "def uncons = unList"
  , "## left fold: step sees [acc, elem], list consumed left to right"
  , "def fold = (f b l -> l >> unList >> (b | (x r -> f b x >> apply >> f _ r >> fold)) >> merge)"
  , "## a reflected atom: prim | int | str | sym | quote | row | group"
  , "data Atom = (Sym | Int | Str | Sym | List(List(Atom)) | List(List(List(Atom))) Bool | List(List(Atom)))"
  , "## code is a chain of tensor stages of atoms (spine normal form)"
  , "type Stage = List(Atom)"
  , "type Code = List(Stage)"

  , "## apply a quoted function to every element"
  , "def map = (f l -> l >> [nil] [(r x -> f x >> apply >> _ r >> cons)] ... >> foldList)"
  , "## invert a router: swap the hit and miss tracks"
  , "def not = (miss | ok) >> merge"
  , "## keep only a router's decision: collapse both payloads to nothing"
  , "def verdict = (forget | forget)"
  , "## long-form comparisons forget their input and answer Bool"
  , "def equals = eq? >> verdict"
  , "def less = lt? >> verdict"
  , "## long-form predicates, from arithmetic and the comparators"
  , "def odd = _ 2 >> mod >> 1 _ >> equals"
  , "def even = _ 2 >> mod >> 0 _ >> equals"
  , "def zero = 0 _ >> equals"
  , "def negative = _ 0 >> less"
  , "## routers, DERIVED: decide with the Bool, then re-route the kept"
  , "## value onto the winning track — the (n | n) pattern"
  , "def odd? = (n -> n >> odd >> (n | n))"
  , "def even? = (n -> n >> even >> (n | n))"
  , "def zero? = (n -> n >> zero >> (n | n))"
  , "def negative? = (n -> n >> negative >> (n | n))"
  , "## re-nest a sum leftward: (A | (B | C)) => ((A | B) | C)"
  , "def assocL = (in1 >> in1 | (in2 >> in1 | in2) >> merge) >> merge"
  , "## re-nest a sum rightward: ((A | B) | C) => (A | (B | C))"
  , "def assocR = ((in1 | in1 >> in2) >> merge | in2 >> in2) >> merge"
  , "## negate a quoted router, as a value"
  , "def negate = (p -> [p ... >> apply >> (miss | ok) >> merge])"
  , "## and on quoted routers: hit iff both hit; q runs only on p's hit"
  , "def both = (p q -> [p ... >> apply >> (q ... >> apply | miss) >> merge])"
  , "## or on quoted routers: hit if p hits, otherwise q decides"
  , "def either = (p q -> [p ... >> apply >> (ok | q ... >> apply) >> merge])"
  , "## compare two wires with eq?, route the first, drop the second"
  , "def equals? = eq? >> (_ drop | _ drop)"
  , "## compare two wires with lt?, route the first, drop the second"
  , "def less? = lt? >> (_ drop | _ drop)"
  , "## predicate factory: k >> equalsTo is a quoted equals-k router"
  , "def equalsTo = (k -> [_ k >> equals?])"
  , "## predicate factory: k >> lessThan is a quoted below-k router"
  , "def lessThan = (k -> [_ k >> less?])"
  , "## reverse a list"
  , "def reverse = [swap >> cons] nil ... >> fold"
  , "## append two lists"
  , "def append = swap >> _ reverse >> [swap >> cons] ... >> fold"
  , "## flatten one layer: join of the list monad"
  , "def concat = [append] nil ... >> fold"
  , "## one-element list: return of the list monad"
  , "def single = _ nil >> cons"
  , "## map then flatten: bind of the list monad"
  , "def flatMap = map >> concat"
  , "## box a bundle as a list, DERIVED from its own eliminator:"
  , "## pack : aⁿ ⇒ List(a) — the flat list constructor; groups delimit"
  , "def pack = [(l x -> x l >> cons)] nil ... >> foldExp >> reverse"
  , "## two-wire elements: (a b)ⁿ ⇒ List(a b).  reverse/append are"
  , "## single-wire words, so order is kept Church-style: fold up a"
  , "## FUNCTION, then apply it to nil"
  , "def pack2 = [(f x y -> [(l -> f (x y l >> cons) >> apply)])] [pass] ... >> foldExp2 >> _ nil >> apply"
  , "## first-match over a clause list: each clause is [router] [action];"
  , "## the first router that hits runs its action on x, else the default."
  , "def matchWith = (x default clauses -> clauses >> [x >> default ... >> apply] [(rest p f -> x >> p ... >> apply >> (f ... >> apply | drop >> rest) >> merge)] ... >> foldList)"
  , "## the always-hit router: the last lane of a || guard list"
  , "def else? = in1"
  , "## probe a clause list (|| lanes or pack2): run the first hit;"
  , "## in1(result) on a hit, in2(input) if none hit"
  , "def choose = (x clauses -> clauses >> [x >> in2] [(rest p f -> x >> p ... >> apply >> (f ... >> apply >> in1 | drop >> rest) >> merge)] ... >> foldList)"
  , "## commute List over the sum monad: all hits, or the first miss"
  , "def sequence = [nil >> ok] [(r x -> x >> ((y -> r >> (y ... >> cons | ...)) | miss) >> merge)] ... >> foldList"
  , "## keep the elements a quoted router hits"
  , "def filter = (p -> [p ... >> apply >> (single | drop >> nil) >> merge]) ... >> flatMap"
  , "## a Bool selects one of two quotations"
  , "def condFn = (b t e -> b >> (t | e) >> merge)"
  , "## a Bool selects a quotation; apply runs it on the rest of the stack"
  , "def cond = condFn ... >> apply"
  , "def whenFn = (b t -> b >> (t | [...]) >> merge)"
  , "## run the quotation only when the Bool hits"
  , "def when = whenFn ... >> apply"
  , "def unlessFn = (b t -> b >> ([...] | t) >> merge)"
  , "## run the quotation only when the Bool misses"
  , "def unless = unlessFn ... >> apply"
  , "## the length of a list"
  , "def len = [0] [_ drop >> 1 ... >> +] ... >> foldList"
  , "## sum and product of an Int list"
  , "def sum = [+] 0 ... >> fold"
  , "def product = [*] 1 ... >> fold"
  , "def downFrom = (n -> n >> zero? >> (drop >> nil | (m -> (m 1 >> -) >> downFrom >> (m 1 >> -) ... >> cons)) >> merge)"
  , "## list(0, 1, …, n-1)"
  , "def range = downFrom >> reverse"
  , "## conditionally swap two wires (the Fredkin gate): reversible routing"
  , "def swapIf = (c a b -> c [b a] [a b] ... >> cond)"
  , "## the multiplexer: pick one of two already-computed values"
  , "def select = (c a b -> c [a] [b] ... >> cond)"
  , "## the boolean connectives: two Bool wires in, one out"
  , "## (each is a mux instance: and = select(a, b, false), etc.)"
  , "def and = (a b -> a [b] [false] ... >> cond)"
  , "def or = (a b -> a [true] [b] ... >> cond)"
  , "def xor = (a b -> a [b >> not] [b] ... >> cond)"
  , "def implies = (a b -> a [b] [true] ... >> cond)"
  , "## take the first n elements; skip drops them instead"
  , "def take = (n l -> n >> zero? >> (drop >> nil | (m -> l >> unList >> (nil | (x r -> (m 1 >> -) r >> take >> x ... >> cons)) >> merge)) >> merge)"
  , "def skip = (n l -> n >> zero? >> ((z -> l) | (m -> l >> unList >> (nil | (x r -> (m 1 >> -) r >> skip)) >> merge)) >> merge)"
  , "## zip two lists into flat two-wire elements: List(a) List(b) => List(a b)"
  , "def zip = (l r -> l >> unList >> (nil | (x xs -> r >> unList >> (nil | (y ys -> xs ys >> zip >> x y ... >> cons)) >> merge)) >> merge)"
  , "## conjunction / disjunction over a Bool list"
  , "def all = [true] [and] ... >> foldList"
  , "def any = [false] [or] ... >> foldList"
  , "## split a list of sums into two lists (hits, misses) — two wires,"
  , "## no bundling: our products are the stack itself"
  , "def partitionSum = (l -> l >> unList >> ((nil) (nil) | (x r -> r >> partitionSum >> (as bs -> x >> ((v -> (v as >> cons) bs) | (w -> as (w bs >> cons))) >> merge))) >> merge)"
  , "## print every element, front to back"
  , "def printAll = [(b x -> x >> print >> b)] 0 ... >> fold >> drop"
  , "## guard ladders as first-class words, one guard per line.  A lane"
  , "## is a bare Bool condition and an answer (any value — quote only"
  , "## if the answer does work).  `if` opens the ladder, `elif` probes"
  , "## only while still undecided, `else` closes with a default value"
  , "## (`otherwise` closes with a quoted, lazy default).  The running"
  , "## wire is (decided | •): a decision, once made, rides through."
  , "##     x ->"
  , "##     (x >> negative) \"neg\"  >> if"
  , "##     _ (x >> zero)   \"zero\" >> elif"
  , "##     _ (x >> toStr)         >> else"
  , "def if   = (b f -> b [f >> in1] [in2] >> cond)"
  , "def elif = (acc b f -> acc >> (in1 | (b [f >> in1] [in2] >> cond)) >> merge)"
  , "def else = (acc d -> acc >> (pass | d) >> merge)"
  , "## close a ladder with a quoted default: runs only if nothing hit."
  , "## (Also the total default for ifRoute/elifRoute ladders, where the"
  , "## undecided track still carries the routed value.)"
  , "def otherwise = (s a -> s >> (pass | a ... >> apply) >> merge)"
  , "## fold a product of decisions accumulated line by line with `...`:"
  , "##     (cond1) answer1 ...      <- each lane line pushes UNDER the"
  , "##     (cond2) answer2 ...         product (remainder on top), so"
  , "##     default         ...         lanes stack reversed and the"
  , "##     decide                      overwrite fold makes the FIRST-"
  , "## written true lane win.  a ((•|•) a)ⁿ ⇒ a — answers are values;"
  , "## quote them and `decide >> apply` when an answer does work."
  , "def decide = [(acc b f -> b f acc >> select)] ... >> foldExp2"
  , "## routing guards: the condition must be a router, and its hit VALUE"
  , "## flows into the action (so the action sees the routed/refined type)."
  , "def ifRoute   = (x p a -> x >> p ... >> apply >> (a ... >> apply | pass))"
  , "def elifRoute = (s p a -> s >> (in1 | p ... >> apply >> (a ... >> apply | pass)) >> merge)"
  , "## box a Code value as a runnable Fn WITHOUT running it: the"
  , "## deferred half of reflect's round trip.  The dynamic check rides"
  , "## the railway at apply time: ρ ⇒ (result | Str ρ)."
  , "def box = (cd -> [(cd) ... >> evalCode])"
  , "## sum an Int bundle: the variadic +"
  , "def sumN = [+] 0 ... >> foldExp"
  , "## guard lanes as a bare product: (Bool Fn)^n lanes, default Fn on"
  , "## top.  All conditions are pre-evaluated (probe every lane); the"
  , "## FIRST true lane's action runs, else the default — exactly one"
  , "## action ever runs (the fold selects quotes, applies once).  The"
  , "## accumulator is (decided | default): a true lane decides once;"
  , "## later lanes leave a decision alone."
  , "def firstTrue = rotLast >> (d -> d >> in2) ... >> [(acc b f -> acc >> (in1 | (g -> b [f >> in1] [g >> in2] >> cond)) >> merge)] ... >> foldExp2 >> merge >> apply"
  , "## assemble a loop body from a quoted predicate and step"
  , "def whileFn = (p f -> [p ... >> apply >> (f ... >> apply >> again | done) >> merge])"
  , "## run step while predicate hits; exit with the miss payload"
  , "def while = whileFn ... >> loop"
  , "## assemble a loop body that exits on the predicate's hit"
  , "def untilFn = (p f -> [p ... >> apply >> (done | f ... >> apply >> again) >> merge])"
  , "## run step until predicate hits; exit with the hit payload"
  , "def until = untilFn ... >> loop"
  ]

preludeModule :: Module
preludeModule =
  case checkModuleWith primEnv [] [] [] preludeSrc of
    Left err -> error ("prelude failed to check: " ++ err)
    Right m  -> m

preludeNames :: [String]
preludeNames = [ n | (n, _, _) <- modDefs preludeModule ]

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
  | VStr String
  | VSym String
  | VFn RunDefs VarEnv Term   -- a quote closes over BOTH its binder values
                              -- (VarEnv) and the def-scope it was written in
                              -- (RunDefs), so free def-names resolve where the
                              -- quote was DEFINED, not where it is applied —
                              -- the closure discipline early binding requires
  | VSum Int [Value]   -- tag (0-based) + the alternative's wire bundle

-- Equality ignores a quote's captured scope: two quotes are equal when
-- their binder values and bodies match.  (Comparing scopes would be
-- meaningless for `eq?` and would loop on the recursive self-knot.)
instance Eq Value where
  VInt a     == VInt b     = a == b
  VStr a     == VStr b     = a == b
  VSym a     == VSym b     = a == b
  VFn _ va a == VFn _ vb b = va == vb && a == b
  VSum i vs  == VSum j ws  = i == j && vs == ws
  _          == _          = False

-- Cons-shaped sum spines (in2(x, in2(y, … in1()))) display as
-- list(x, y, …); a bare in1() stays in1().
listView :: Value -> Maybe [Value]
listView (VSum 1 [x, rest]) = (x :) <$> end rest
  where
    end (VSum 0 [])          = Just []
    end (VSum 1 [y, more])   = (y :) <$> end more
    end _                    = Nothing
listView _ = Nothing

instance Show Value where
  show v@(VSum _ _)
    | Just vs <- listView v =
        "list(" ++ intercalate ", " (map show vs) ++ ")"
  show (VInt n)      = show n
  show (VStr t)      = t
  show (VSym t)      = t
  show (VFn _ _ _)   = "[fn]"
  show (VSum i vs)   =
    "in" ++ show (i + 1) ++ "(" ++ intercalate ", " (map show vs) ++ ")"

-- Number of concrete wires in a stack type (its closed prefix).
closedArity :: SType -> Int
closedArity (SCons _ rest) = 1 + closedArity rest
closedArity _              = 0

-- A runtime definition: closed input arity, whether the input has an
-- open tail (segment-consuming as a final atom, like apply/loop), the
-- body term, and — crucially — the SCOPE the body resolves names
-- against.  The scope is a SNAPSHOT taken when the def was introduced:
-- the environment as it stood then, plus the def itself (a lazy knot
-- for recursion).  This makes name resolution EARLY-bound — later
-- shadowing cannot reach into an existing body — matching how the
-- typechecker checks each def against the env as it stood at that
-- point.  (Dynamically spliced code via `evalCode` still resolves
-- against the live environment; see its clause.)
data DefEntry = DefEntry
  { deArity :: !Int
  , deOpen  :: !Bool
  , deBody  :: Term
  , deScope :: RunDefs
  }

type RunDefs = Map String DefEntry

-- Extend `base` with defs in definition order; each body snapshots
-- base + all-earlier-defs + itself.  Braid has no forward references
-- (the typechecker's left fold rejects them), so "earlier defs" is the
-- exact set a body may legally mention besides itself.
extendRunDefs :: RunDefs -> [(String, Int, Bool, Term)] -> RunDefs
extendRunDefs = foldl step
  where
    step acc (name, ar, op, body) =
      let scope = M.insert name entry acc   -- self-knot: recursion sees `entry`
          entry = DefEntry ar op body scope
      in scope

moduleRunDefs :: Module -> RunDefs
moduleRunDefs = buildRunDefs M.empty

-- Fold a module's data artifacts and defs onto a base environment.
-- Data-artifact bodies are prim-only (constructors, unrollers, merge),
-- so their scope is inert; defs follow, in order, and capture it.
buildRunDefs :: RunDefs -> Module -> RunDefs
buildRunDefs base m =
  extendRunDefs base
    (  [ (name, ar, op, term)
       | d <- modDatas m, (name, (ar, op, term)) <- snd (dataDeclArtifacts d) ]
    ++ [ (name, arityOf sc, openOf sc, term)
       | (name, sc, term) <- modDefs m ] )
  where
    arityOf (Forall _ _ _ _ (Arrow i _)) = closedArity i
    openOf  (Forall _ _ _ _ (Arrow i _)) = openTailed i
    openTailed (SCons _ rest) = openTailed rest
    openTailed (STail _)      = True
    openTailed (SSplice _ _)  = True
    openTailed (SExp _ _ _)   = True   -- erased width: needs the whole segment
    openTailed SEnd           = False

-- Evaluate a term: returns the final stack and the print log.  The Env
-- is needed to compute closed arities of grouped compound operands; the
-- VarEnv holds named-abstraction parameters in scope.
type Eval = ExceptT String IO

evalTerm :: Env -> RunDefs -> VarEnv -> Term -> [Value]
         -> Eval ([Value], [String])
evalTerm env defs vars term st =
  case term of
    Seq t u -> do
      (st1, l1) <- evalTerm env defs vars t st
      (st2, l2) <- evalTerm env defs vars u st1
      pure (st2, l1 ++ l2)
    Tensor ts      -> goAtoms ts st
    p@(Prim _)     -> goAtoms [p] st
    q@(Quote _)    -> goAtoms [q] st
    o@(OpenAbs {}) -> goAtoms [o] st
    a@(Alts {})    -> goAtoms [a] st
  where
    goAtoms [] stk = pure (stk, [])   -- leftover remainder flows through last
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
            [VFn scope cvars body] -> do
              let seg = if isFinal then stk' else []
              (out, logs) <- evalTerm env scope cvars body seg
              pure (out, if isFinal then [] else stk', logs)
            _ ->
              throwError "Runtime type error in apply: expected a quotation"
    -- evalCode: dynamically-checked splice.  Rebuild the term, infer
    -- its type in-process, run it on the segment; failures ride the
    -- miss track WITH the untouched segment as evidence.
    applyAtom isFinal (Prim "evalCode") stk
      | not (M.member "evalCode" vars), not (M.member "evalCode" defs) = do
          (args, stk') <- takeWires "evalCode" 1 stk
          let seg = if isFinal then stk' else []
              keep = if isFinal then [] else stk'
              missWith msg = pure ([VSum 1 (VStr msg : seg)], keep, [])
          case args of
            [c] ->
              case codeToTermV c of
                Left e -> missWith e
                Right term ->
                  case inferTermIn env term of
                    Left e -> missWith e
                    Right _ -> do
                      r <- liftIO (runExceptT
                             (evalTerm env defs M.empty term seg))
                      case r of
                        Left e -> missWith e
                        Right (out, logs) ->
                          pure ([VSum 0 out], keep, logs)
            _ -> throwError "evalCode: expected a Code value"
    -- IO edges, in print's mold: effects with honest railway types
    applyAtom _ (Prim "readFile") stk
      | not (M.member "readFile" vars), not (M.member "readFile" defs) = do
          (args, stk') <- takeWires "readFile" 1 stk
          case args of
            [VStr path] -> do
              r <- liftIO (try (do t <- readFile path
                                   _ <- evaluate (length t)
                                   pure t))
              case r of
                Left e  ->
                  pure ([VSum 1 [VStr (show (e :: IOException))]], stk', [])
                Right t -> pure ([VSum 0 [VStr t]], stk', [])
            _ -> throwError "readFile: expected a Str path"
    applyAtom _ (Prim "writeFile") stk
      | not (M.member "writeFile" vars), not (M.member "writeFile" defs) = do
          (args, stk') <- takeWires "writeFile" 2 stk
          case args of
            [VStr path, VStr contents] -> do
              r <- liftIO (try (writeFile path contents))
              case r of
                Left e  ->
                  pure ([VSum 1 [VStr (show (e :: IOException))]], stk', [])
                Right () -> pure ([VSum 0 []], stk', [])
            _ -> throwError "writeFile: expected Str path and contents"
    -- rotLast: whole segment; move its last value to the front
    applyAtom isFinal (Prim "rotLast") stk
      | not (M.member "rotLast" vars), not (M.member "rotLast" defs) =
          if isFinal
            then case reverse stk of
              (lastV : rs) -> pure (lastV : reverse rs, [], [])
              []           -> throwError "rotLast: empty segment"
            else case stk of
              (v : rest) -> pure ([v], rest, [])   -- closed: 1-wide segment
              []         -> throwError "rotLast: empty stack"
    -- forget: the terminal morphism — consume the segment, emit nothing
    applyAtom isFinal (Prim "forget") stk
      | not (M.member "forget" vars), not (M.member "forget" defs) =
          if isFinal
            then pure ([], [], [])
            else pure ([], stk, [])
    -- loop: Elgot iteration — run the body on the segment; the continue
    -- track re-enters, the done track exits.
    applyAtom isFinal (Prim "loop") stk
      | not (M.member "loop" vars), not (M.member "loop" defs) = do
          (args, stk') <- takeWires "loop" 1 stk
          case args of
            [VFn scope cv body] -> do
              let seg0 = if isFinal then stk' else []
                  go seg logs = do
                    (out, lg) <- evalTerm env scope cv body seg
                    case out of
                      [VSum 0 bundle] -> go bundle (logs ++ lg)
                      [VSum 1 bundle] -> pure (bundle, logs ++ lg)
                      _ -> throwError "Runtime type error in loop: body must return a (continue | done) decision"
              (result, logs) <- go seg0 []
              pure (result, if isFinal then [] else stk', logs)
            _ -> throwError "Runtime type error in loop: expected a body quotation"
    -- foldExp: eliminate an exponent bundle aⁿ.  n is erased, so the
    -- bundle is the final segment and its runtime width is the witness
    -- (the forget/rotLast convention).  Non-final was typed at n := 0.
    applyAtom isFinal (Prim "foldExp") stk
      | not (M.member "foldExp" vars), not (M.member "foldExp" defs) = do
          (args, stk') <- takeWires "foldExp" 2 stk
          case args of
            [VFn scope cv body, b0] -> do
              let bundle = if isFinal then stk' else []
                  go acc [] logs = pure (acc, logs)
                  go acc (x : xs) logs = do
                    (out, lg) <- evalTerm env scope cv body [acc, x]
                    case out of
                      [acc'] -> go acc' xs (logs ++ lg)
                      _ -> throwError "Runtime type error in foldExp: the step must return exactly the accumulator"
              (result, logs) <- go b0 bundle []
              pure ([result], if isFinal then [] else stk', logs)
            _ -> throwError "Runtime type error in foldExp: expected a step quotation and an initial accumulator"
    -- foldExp2: the pair-bundle twin — chunk the segment in twos
    applyAtom isFinal (Prim "foldExp2") stk
      | not (M.member "foldExp2" vars), not (M.member "foldExp2" defs) = do
          (args, stk') <- takeWires "foldExp2" 2 stk
          case args of
            [VFn scope cv body, b0] -> do
              let bundle = if isFinal then stk' else []
                  go acc (x : y : xs) logs = do
                    (out, lg) <- evalTerm env scope cv body [acc, x, y]
                    case out of
                      [acc'] -> go acc' xs (logs ++ lg)
                      _ -> throwError "Runtime type error in foldExp2: the step must return exactly the accumulator"
                  go acc [] logs = pure (acc, logs)
                  go _ _ _ = throwError "foldExp2: odd segment (unreachable on typechecked programs)"
              (result, logs) <- go b0 bundle []
              pure ([result], if isFinal then [] else stk', logs)
            _ -> throwError "Runtime type error in foldExp2: expected a step quotation and an initial accumulator"
    -- GLA generators: width-polymorphic wiring; the segment IS the witness
    applyAtom isFinal (Prim "dupN") stk
      | not (M.member "dupN" vars), not (M.member "dupN" defs) =
          if isFinal then pure (stk ++ stk, [], [])
                     else pure ([], stk, [])
    applyAtom isFinal (Prim "addN") stk
      | not (M.member "addN" vars), not (M.member "addN" defs) =
          if not isFinal then pure ([], stk, [])
          else do
            let m = length stk
                (xs, ys) = splitAt (m `div` 2) stk
                add (VInt x) (VInt y) = pure (VInt (x + y))
                add _ _ = throwError "Runtime type error in addN: expected Int wires"
            if odd m then throwError "addN: odd segment (unreachable on typechecked programs)"
                     else do out <- sequence (zipWith add xs ys)
                             pure (out, [], [])
    applyAtom isFinal (Prim "zipN") stk
      | not (M.member "zipN" vars), not (M.member "zipN" defs) =
          if not isFinal then pure ([], stk, [])
          else if odd (length stk)
            then throwError "zipN: odd segment (unreachable on typechecked programs)"
            else let (xs, ys) = splitAt (length stk `div` 2) stk
                 in pure (concat (zipWith (\x y -> [x, y]) xs ys), [], [])
    applyAtom isFinal (Prim "scaleN") stk
      | not (M.member "scaleN" vars), not (M.member "scaleN" defs) = do
          (args, stk') <- takeWires "scaleN" 1 stk
          case args of
            [VInt k] -> do
              let bundle = if isFinal then stk' else []
                  scale (VInt x) = pure (VInt (k * x))
                  scale _ = throwError "Runtime type error in scaleN: expected Int wires"
              out <- mapM scale bundle
              pure (out, if isFinal then [] else stk', [])
            _ -> throwError "Runtime type error in scaleN: expected an Int scalar"
    applyAtom isFinal (Prim name) stk
      | Just n <- injIndex name
      , not (M.member name vars)
      , not (M.member name defs) =
          if isFinal
            then pure ([VSum (n - 1) stk], [], [])
            else pure ([VSum (n - 1) []], stk, [])
    applyAtom isFinal (Prim name) stk
      | Just v <- M.lookup name vars = pure ([v], stk, [])
      | isIntLiteral name = pure ([VInt (read name)], stk, [])
      | isStrLiteral name = pure ([VStr (drop 1 name)], stk, [])
      | isSymLiteral name = pure ([VSym name], stk, [])
      | Just entry <- M.lookup name defs =
          -- jump into the def's body under ITS captured scope, not the
          -- caller's — early binding (see DefEntry)
          let k     = deArity entry
              open  = deOpen  entry
              body  = deBody  entry
              scope = deScope entry
          in if open && isFinal
            then do
              (out, logs) <- evalTerm env scope M.empty body stk
              pure (out, [], logs)
            else do
              (args, stk') <- takeWires name k stk
              (out, logs) <- evalTerm env scope M.empty body args
              pure (out, stk', logs)
      | otherwise = do
          k <- liftEither (builtinArity name)
          (args, stk') <- takeWires name k stk
          (out, logs) <- liftEither (runBuiltin env defs name args)
          pure (out, stk', logs)
    applyAtom _ (Quote body) stk = pure ([VFn defs vars body], stk, [])
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
              throwError "Runtime error in code row: tag out of range"
        _ -> throwError "Runtime type error in code row: expected a sum value"
    -- Named abstraction: bind the named wires (left to right, deepest
    -- first), then run the body on ITS input — the `_` wires, plus the
    -- whole remaining segment when the params end in `...` (an open
    -- binder is segment-consuming, like any open-arity word, so it must
    -- be the final atom of its stage).
    applyAtom isFinal (OpenAbs slots hasRest body) stk = do
      (args, stk') <- takeWires "abstraction" (length slots) stk
      let vars' = M.fromList [ (n, v) | (Just n, v) <- zip slots args ]
                    `M.union` vars
          anonVals = [ v | (Nothing, v) <- zip slots args ]
          open  = hasRest && isFinal
          seg   = if open then stk' else []
      (out, logs) <- evalTerm env defs vars' body (anonVals ++ seg)
      pure (out, if open then [] else stk', logs)
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
                Forall [dummy] [] [] [] (Arrow SEnd (SCons (TVarTy dummy) SEnd))
              arityEnv = foldr (\n -> M.insert n dummyScheme)
                               env (M.keys vars)
          Arrow i _ <- liftEither (inferTermIn arityEnv t')
          let k = closedArity i
          (args, stk') <- takeWires "grouped program" k stk
          (out, logs) <- evalTerm env defs vars t' args
          pure (out, stk', logs)

    takeWires name k stk
      | length stk >= k = pure (take k stk, drop k stk)
      | otherwise =
          throwError $ "Runtime stack underflow in " ++ name
               ++ " (unreachable on typechecked programs)"

builtinArity :: String -> Either String Int
builtinArity name =
  case M.lookup name primEnv of
    Just (Forall _ _ _ _ (Arrow i _)) -> Right (closedArity i)
    Nothing -> Left $ "Unknown primitive at runtime: " ++ name

runBuiltin :: Env -> RunDefs -> String -> [Value]
           -> Either String ([Value], [String])
runBuiltin _ _ "id"    [v]              = Right ([v], [])
runBuiltin _ _ "_"     [v]              = Right ([v], [])
runBuiltin _ _ "swap"  [x, y]           = Right ([y, x], [])
runBuiltin _ _ "dup"   [v]              = Right ([v, v], [])
runBuiltin _ _ "drop"  [_]              = Right ([], [])
runBuiltin _ _ "pass"  []               = Right ([], [])
runBuiltin _ _ "+"     [VInt x, VInt y] = Right ([VInt (x + y)], [])
runBuiltin _ _ "*"     [VInt x, VInt y] = Right ([VInt (x * y)], [])
runBuiltin _ _ "print" [v]              = Right ([], [show v])
runBuiltin _ _ "true"  []               = Right ([VSum 0 []], [])
runBuiltin _ _ "false" []               = Right ([VSum 1 []], [])
runBuiltin _ _ "eq?"  [x, y]            = Right ([VSum (if x == y then 0 else 1) [x, y]], [])
runBuiltin _ _ "lt?"  [VInt x, VInt y]  = Right ([VSum (if x < y then 0 else 1) [VInt x, VInt y]], [])
runBuiltin _ _ "-"    [VInt x, VInt y]  = Right ([VInt (x - y)], [])
runBuiltin _ _ "div"  [VInt _, VInt 0]  = Left "division by zero"
runBuiltin _ _ "div"  [VInt x, VInt y]  = Right ([VInt (x `div` y)], [])
runBuiltin _ _ "mod"  [VInt _, VInt 0]  = Left "modulo by zero"
runBuiltin _ _ "mod"  [VInt x, VInt y]  = Right ([VInt (x `mod` y)], [])
runBuiltin _ _ "gt?"  [VInt x, VInt y]  = Right ([VSum (if x > y then 0 else 1) [VInt x, VInt y]], [])
runBuiltin _ _ "gte?" [VInt x, VInt y]  = Right ([VSum (if x >= y then 0 else 1) [VInt x, VInt y]], [])
runBuiltin _ _ "lte?" [VInt x, VInt y]  = Right ([VSum (if x <= y then 0 else 1) [VInt x, VInt y]], [])
runBuiltin _ _ "cat"  [VStr x, VStr y]  = Right ([VStr (x ++ y)], [])
runBuiltin _ _ "toStr" [v]              = Right ([VStr (show v)], [])
runBuiltin _ _ "symStr" [VSym t]        = Right ([VStr (drop 1 t)], [])
runBuiltin _ _ "unparse" [c]            = do
  t <- codeToTermV c
  Right ([VStr (renderTerm t)], [])
runBuiltin env _ "parse" [VStr src]     =
  case parseProgram src >>= reflectPure env of
    Right c -> Right ([VSum 0 [c]], [])
    Left e  -> Right ([VSum 1 [VStr e]], [])
runBuiltin env _ "reflect" [VFn _ cv t] =
  case reflectFn env cv t of
    Right c -> Right ([VSum 0 [c]], [])
    Left e  -> Right ([VSum 1 [VStr e]], [])
runBuiltin _ _ "asInt?" [VStr t]        =
  case reads t :: [(Int, String)] of
    [(n, "")] -> Right ([VSum 0 [VInt n]], [])
    _         -> Right ([VSum 1 [VStr t]], [])
runBuiltin _ _ "there" [VSum t bundle]  = Right ([VSum (t + 1) bundle], [])
runBuiltin _ _ "merge" [VSum _ bundle]  = Right (bundle, [])
runBuiltin _ _ name args =
  Left $ "Runtime type error in " ++ name ++ " applied to "
       ++ show args ++ " (unreachable on typechecked programs)"

--------------------------------------------------------------------------------
-- 11.5 Code reflection (spine normal form) and abstraction elimination
--
-- Code = data (List(List(Atom))); Atom = (prim | int | str | sym |
-- quote | row | group), encoded as VSum tags 0..6.  reflect grounds a
-- closure's captured values into literal-pushing code and compiles
-- named abstractions away into pure wiring (parameters as leading
-- input wires, a parameter block threaded at the BACK of the stack).
-- v1 gate: bodies whose atoms all have closed arities (wiring,
-- arithmetic, literals, groups, closed rows, exact defs).  Parameters
-- captured in quotations or row components (true closures) and
-- segment-consuming atoms (apply, injections, merge, loop, …) are
-- rejected onto the miss track with an explanation.
--------------------------------------------------------------------------------

encodeListV :: [Value] -> Value
encodeListV = foldr (\v r -> VSum 1 [v, r]) (VSum 0 [])

decodeListV :: Value -> Either String [Value]
decodeListV (VSum 0 [])     = Right []
decodeListV (VSum 1 [v, r]) = (v :) <$> decodeListV r
decodeListV v = Left $ "malformed list value: " ++ show v

encodeBoolV :: Bool -> Value
encodeBoolV b = VSum (if b then 0 else 1) []

-- spine normal form of a term: stages of atoms
spineOf :: Term -> [[Term]]
spineOf (Seq a b)  = spineOf a ++ spineOf b
spineOf (Tensor ts) = [ts]
spineOf t          = [[t]]

chainTerm :: [[Term]] -> Term
chainTerm ss =
  case map stageT (filter (not . null) ss) of
    [] -> Prim "pass"
    ts -> foldr1 Seq ts
  where
    stageT [t] = t
    stageT ts' = Tensor ts'

-- render code back to source text (inverse-ish of the parser; spine
-- normal form in, canonical text out)
renderTerm :: Term -> String
renderTerm t =
  case filter (not . null) (spineOf t) of
    [] -> "pass"
    ss -> intercalate " >> " (map rStage ss)
  where
    rStage ats = unwords (map rAtom ats)
    rAtom (Prim ('"' : str)) = '"' : concatMap esc str ++ "\""
    rAtom (Prim n)      = n
    rAtom (Quote q)     = "[" ++ renderTerm q ++ "]"
    rAtom (Alts cs res) =
      "(" ++ intercalate " | " (map renderTerm cs)
          ++ (if res then " | ..." else "") ++ ")"
    rAtom (OpenAbs slots hasRest b) =
      "(" ++ unwords (map (maybe "_" id) slots ++ ["..." | hasRest])
          ++ " -> " ++ renderTerm b ++ ")"
    rAtom g = "(" ++ renderTerm g ++ ")"
    esc '"'  = "\\\""
    esc '\\' = "\\\\"
    esc '\n' = "\\n"
    esc c    = [c]

reflectPure :: Env -> Term -> Either String Value
reflectPure env = reflectFn env M.empty

-- reflect a closure: ground captured values, eliminate abstractions,
-- then encode the spine
reflectFn :: Env -> VarEnv -> Term -> Either String Value
reflectFn env cv t0 = do
  t1 <- groundTerm env cv t0
  t2 <- elimAbsTerm env t1
  termToCodeV env t2

termToCodeV :: Env -> Term -> Either String Value
termToCodeV env t = do
  stages <- mapM (mapM atomVal) (spineOf t)
  pure (encodeListV (map encodeListV stages))
  where
    atomVal (Prim n)
      | isIntLiteral n = Right (VSum 1 [VInt (read n)])
      | isStrLiteral n = Right (VSum 2 [VStr (drop 1 n)])
      | isSymLiteral n = Right (VSum 3 [VSym n])
      | otherwise      = Right (VSum 0 [VSym ('.' : n)])
    atomVal (Quote q) = do
      c <- termToCodeV env q
      pure (VSum 4 [c])
    atomVal (Alts comps residual) = do
      cs <- mapM (termToCodeV env) comps
      pure (VSum 5 [encodeListV cs, encodeBoolV residual])
    atomVal (OpenAbs {}) =
      Left "internal: abstraction survived elimination"
    atomVal g = do
      c <- termToCodeV env g
      pure (VSum 6 [c])

-- inverse: rebuild a Term from a Code value (a list of stages)
codeToTermV :: Value -> Either String Term
codeToTermV stagesV = do
  stageVs <- decodeListV stagesV
  stages  <- mapM (\sv -> decodeListV sv >>= mapM atomTerm) stageVs
  pure (chainTerm stages)
  where
    atomTerm (VSum 0 [VSym ('.' : n)]) = Right (Prim n)
    atomTerm (VSum 1 [VInt n])  = Right (Prim (show n))
    atomTerm (VSum 2 [VStr t])  = Right (Prim ('"' : t))
    atomTerm (VSum 3 [VSym t])  = Right (Prim t)
    atomTerm (VSum 4 [c])       = Quote <$> codeToTermV c
    atomTerm (VSum 5 [csV, bV]) = do
      cs <- decodeListV csV >>= mapM codeToTermV
      res <- case bV of
        VSum 0 [] -> Right True
        VSum 1 [] -> Right False
        _         -> Left "malformed residual flag"
      pure (Alts cs res)
    atomTerm (VSum 6 [c])       = codeToTermV c
    atomTerm v = Left $ "malformed atom value: " ++ show v

-- embed a runtime value as code that pushes it
valueToCode :: Env -> Value -> Either String Term
valueToCode _   (VInt n)  = Right (Prim (show n))
valueToCode _   (VStr t)  = Right (Prim ('"' : t))
valueToCode _   (VSym t)  = Right (Prim t)
valueToCode env (VFn _ cv t) = do
  t1 <- groundTerm env cv t
  t2 <- elimAbsTerm env t1
  pure (Quote t2)
valueToCode env (VSum tag vs) = do
  fields <- mapM (valueToCode env) vs
  let inj = Prim ("in" ++ show (tag + 1))
  pure $ if null fields then inj else Seq (Tensor fields) inj

-- substitute captured closure values (shadow-aware)
groundTerm :: Env -> VarEnv -> Term -> Either String Term
groundTerm env cv = go cv
  where
    go vars t@(Prim n)
      | Just v <- M.lookup n vars = valueToCode env v
      | otherwise                 = Right t
    go vars (Seq a b)    = Seq <$> go vars a <*> go vars b
    go vars (Tensor ts)  = Tensor <$> mapM (go vars) ts
    go vars (Quote t)    = Quote <$> go vars t
    go vars (Alts cs r)  = Alts <$> mapM (go vars) cs <*> pure r
    go vars (OpenAbs slots hasRest b) =
      OpenAbs slots hasRest
        <$> go (foldr M.delete vars [ n | Just n <- slots ]) b

--------------------------------------------------------------------------------
-- 11.6 Abstraction elimination (grinding the non-concatenative edges)
--------------------------------------------------------------------------------

elimAbsTerm :: Env -> Term -> Either String Term
elimAbsTerm env = go
  where
    go (Seq a b)      = Seq <$> go a <*> go b
    go (Tensor ts)    = Tensor <$> mapM go ts
    go (Quote t)      = Quote <$> go t
    go (Alts cs r)    = Alts <$> mapM go cs <*> pure r
    go (OpenAbs slots hasRest b) = do
      b' <- go b
      if hasRest
        -- the passthrough width is erased, so there is no static wire
        -- count to compile the parameter block against
        then Left "cannot reflect a binder whose parameters end in '...'"
        else do
          -- compileAbsOpen wants the layout [body inputs (deepest)]
          -- [param block] — the params sit ABOVE the wires the body
          -- consumes (its finalStage passes k0 wires and then drops the
          -- params).  Braid binders bind the DEEPEST wires, so every
          -- slot list with a `_` needs a permutation prefix that sinks
          -- the unnamed wires below the named ones.
          let names = [ n | Just n <- slots ]
              anons = length [ () | Nothing <- slots ]
          inner <- compileAbsOpen env names anons b'
          pure (foldr Seq inner (paramsAboveStages slots))
    go t = Right t

-- Adjacent-transposition stages that stably sink the UNNAMED slots
-- below the named ones, rearranging a positional parameter list into
-- the [body inputs][params] layout compileAbsOpen compiles against.
-- Stable (a bubble pass on the unnamed/named key), so each group keeps
-- its written order — in particular the first-written name stays the
-- deepest param.  Empty when there is nothing to move.
paramsAboveStages :: [Maybe String] -> [Term]
paramsAboveStages slots0 = go (map key slots0) []
  where
    key = maybe (0 :: Int) (const 1)
    go keys acc =
      case [ d | (d, (a, b)) <- zip [0 :: Int ..] (zip keys (drop 1 keys))
               , a > b ] of
        []      -> reverse acc
        (d : _) -> go (swapIdx d keys) (Tensor (swapAt d) : acc)
    swapAt d = replicate d (Prim "_") ++ [Prim "swap", Prim "pass"]
    swapIdx d xs =
      take d xs ++ [xs !! (d + 1), xs !! d] ++ drop (d + 2) xs

freeNamesIn :: Term -> [String]
freeNamesIn = go
  where
    go (Prim n)       = [n]
    go (Seq a b)      = go a ++ go b
    go (Tensor ts)    = concatMap go ts
    go (Quote t)      = go t
    go (Alts cs _)    = concatMap go cs
    go (OpenAbs slots _ b) =
      filter (`notElem` [ n | Just n <- slots ]) (go b)

-- (input arity, output arity, param copies to insert at relative input
-- offsets, replacement atom)
data AtomInfo = AtomInfo Int Int [(Int, Int)] Term

compileAbs :: Env -> [String] -> Term -> Either String Term
compileAbs env ps body = compileAbsOpen env ps 0 body

-- Rewrite `body` (consuming k0 underlying wires) so the parameters
-- arrive as a block of wires BELOW those inputs; the block is dropped
-- at the end.
compileAbsOpen :: Env -> [String] -> Int -> Term -> Either String Term
compileAbsOpen env ps k0 body = do
  stages <- rewriteChain k0 (spineOf body)
  pure (chainTerm stages)
  where
    n = length ps

    swapAt d = replicate d (Prim "_") ++ [Prim "swap", Prim "pass"]
    dupAt d  = replicate d (Prim "_") ++ [Prim "dup", Prim "pass"]
    -- copy the wire at depth `from` up to depth `to` (to <= from)
    fetchTo from to =
      dupAt from : [ swapAt j | j <- [from - 1, from - 2 .. to] ]

    rewriteChain k [] = Right [finalStage k]
    rewriteChain k (stage : rest) = do
      (pres, stage', k') <- rewriteStage k stage
      ((pres ++ [stage']) ++) <$> rewriteChain k' rest

    finalStage k = replicate k (Prim "_") ++ replicate n (Prim "drop")

    rewriteStage k atoms0 = do
      let (atoms, _) = case reverse atoms0 of
            (Prim "pass" : rs) -> (reverse rs, True)
            _                  -> (atoms0, False)
      infos <- mapM classify atoms
      let inAs    = [ i | AtomInfo i _ _ _ <- infos ]
          offsets = init (scanl (+) 0 inAs)
          inserts = [ (off + rel, idx)
                    | (AtomInfo _ _ specs _, off) <- zip infos offsets
                    , (rel, idx) <- specs ]
          -- insert left-to-right: shallower targets first; offsets are
          -- final-layout positions, so each target is correct at its
          -- moment of insertion
          fetches = concat
            [ fetchTo (k + j + idx) tgt
            | (j, (tgt, idx)) <- zip [0 ..] inserts ]
          p       = length inserts
          bigA    = sum inAs - p
          bigO    = sum [ o | AtomInfo _ o _ _ <- infos ] - p
          atoms'  = [ a | AtomInfo _ _ _ a <- infos ]
          k'      = (bigO + p) + (k - bigA)
      if bigA > k
        then Left "abstraction body consumes more than it has (internal)"
        else Right (fetches, atoms' ++ [Prim "pass"], k')

    classify :: Term -> Either String AtomInfo
    classify t@(Prim nm)
      | Just i <- elemIndex nm ps = Right (AtomInfo 1 1 [(0, i)] (Prim "_"))
      | nm == "pass" = Left "reflect: '...' before the end of a stage in an abstraction body"
      | isIntLiteral nm || isStrLiteral nm || isSymLiteral nm =
          Right (AtomInfo 0 1 [] t)
      | Just _ <- injIndex nm = segErr nm
      | otherwise =
          case M.lookup nm env of
            Nothing -> Left $ "reflect: unknown name in abstraction body: " ++ nm
            Just (Forall _ _ _ _ (Arrow i o))
              | openTailedS i || openTailedS o -> segErr nm
              | otherwise ->
                  Right (AtomInfo (closedArity i) (closedArity o) [] t)
    classify t@(Quote b)
      | any (`elem` ps) (freeNamesIn b) =
          Left "reflect: parameter captured in a quotation (a closure) — not reflectable yet"
      | otherwise = Right (AtomInfo 0 1 [] t)
    classify t@(Alts cs _)
      | any (any (`elem` ps) . freeNamesIn) cs =
          Left "reflect: parameter used inside a row component — not reflectable yet"
      | otherwise = Right (AtomInfo 1 1 [] t)
    classify (OpenAbs {}) =
      Left "internal: nested abstraction not yet eliminated"
    classify g = groupInfo g

    -- a grouped compound: recursively thread the parameters it uses
    groupInfo g = do
      let used = nub [ nm | nm <- freeNamesIn g, nm `elem` ps ]
          usedIdx = [ i | Just i <- map (`elemIndex` ps) used ]
      Arrow gi go <- inferGroupArrow g
      if openTailedS gi || openTailedS go
        then segErr "grouped program"
        else do
          let gIn  = closedArity gi
              gOut = closedArity go
          if null used
            then Right (AtomInfo gIn gOut [] g)
            else do
              g' <- compileAbsOpen env used gIn g
              pure (AtomInfo (gIn + length used) gOut
                             [ (gIn + j, idx)
                             | (j, idx) <- zip [0 ..] usedIdx ]
                             g')

    inferGroupArrow g = do
      let dummy = TV "_p"
          dummyScheme =
            Forall [dummy] [] [] [] (Arrow SEnd (SCons (TVarTy dummy) SEnd))
          arityEnv = foldr (\nm -> M.insert nm dummyScheme) env ps
      inferTermIn arityEnv g

    segErr nm = Left $
      "reflect: segment-consuming or open-arity atom '" ++ nm
        ++ "' in an abstraction body — not reflectable yet"

openTailedS :: SType -> Bool
openTailedS (SCons _ r)   = openTailedS r
openTailedS (STail _)     = True
openTailedS (SSplice _ _) = True
openTailedS (SExp _ _ _)  = True   -- unknown width: not a closed stack
openTailedS SEnd          = False

-- Typecheck and run a whole module; main runs on the empty stack.
runModule :: String -> IO (Either String ([Value], [String]))
runModule src = runExceptT $ do
  m <- liftEither (checkModule src)
  case modMain m of
    Nothing -> pure ([], [])
    Just (term, arr@(Arrow i _))
      | closedArity i > 0 ->
          throwError $ "main requires a nonempty input stack: " ++ show arr
      | otherwise -> evalTerm (modEnv m) (moduleRunDefs m) M.empty term []
