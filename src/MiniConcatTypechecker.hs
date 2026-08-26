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

-- Effect variables (ε): the tail of an arrow's effect row.  Same
-- tail-only discipline as every other sort (design-effects.md).
newtype EVar = EV String
  deriving (Eq, Ord)

instance Show EVar where
  show (EV s) = s

-- An arrow's GRADE: the set of resource wires it touches.  Stage 1 has
-- one label, `io` — the irreducible one (everything else in the effect
-- zoo is already an ordinary wire) — plus an optional tail for effect
-- polymorphism.  Composition UNIFIES two grades rather than joining
-- them: label-absorbing row unification, Koka-style, which keeps the
-- solver a single pass and inference principal.  Stage 2 widens the
-- Bool to a label set; the shape survives.
data EffRow = Eff { eIO :: Bool, eTail :: Maybe EVar }
  deriving (Eq, Ord, Show)

effPure :: EffRow
effPure = Eff False Nothing

effIO :: EffRow
effIO = Eff True Nothing

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
  | TFin Exp           -- Fin(n): an index into a bundle of width n.
                       -- The bound is a TYPE, erased like every other
                       -- width; at runtime a Fin is a bare Int.  Every
                       -- introduction's n is forced by a relevant
                       -- input (a literal offset, or a live bundle) —
                       -- see design-indices.md.
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
  show (TFin e)    = "Fin(" ++ show e ++ ")"

-- Stack types: front (leftmost) wire first, optional tail variable at the end
data SType
  = SEnd             -- closed end: empty stack •
  | STail SVar       -- open end: remainder variable ρ
  | SCons Ty SType   -- τ Σ (τ is the leftmost wire)
  | SExp SType Exp SType -- base^e: a CLOSED segment repeated e times, then rest
  deriving (Eq, Ord)

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
appendS (STail v) SEnd   = STail v
appendS (STail v) _      =
  error ("appendS: nothing may follow the open tail " ++ show v
         ++ " (the tail-only invariant)")
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
      go (SExp b e rest)  = showExpAt b e : go rest

-- Arrows: stack transformers Σ_in ⇒ Σ_out, carrying a GRADE.  A pure
-- arrow prints exactly as it always has; the bang is the only surface
-- the grade has, and effect tails are invisible (the same information
-- hiding ρ already gets inside Fn⟨…⟩).
data Arrow = Arrow SType SType EffRow
  deriving (Eq, Ord)

-- the overwhelmingly common case: build a pure arrow
arrPure :: SType -> SType -> Arrow
arrPure i o = Arrow i o effPure

-- ...and the five words that touch the world
arrIO :: SType -> SType -> Arrow
arrIO i o = Arrow i o effIO

arrowGlyph :: EffRow -> String
arrowGlyph e = if eIO e then " ⇒! " else " ⇒ "

instance Show Arrow where
  show (Arrow s1 s2 e) = show s1 ++ arrowGlyph e ++ show s2

--------------------------------------------------------------------------------
-- 2. Schemes and environments (only polymorphism over stack vars & type vars)
--------------------------------------------------------------------------------

data Scheme = Forall [TVar] [SVar] [RVar] [NVar] [EVar] Arrow
  deriving (Eq, Ord)

instance Show Scheme where
  -- effect variables are deliberately NOT listed: at stage 1 every
  -- arrow has a grade, so nearly every scheme would grow an `ε0` the
  -- reader can do nothing with.  The bang carries all the information
  -- the grade has.
  show (Forall tvars svars rvars nvars _ arr) =
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
  , effSub :: Map EVar EffRow
  } deriving (Eq, Show)

emptySubst :: Subst
emptySubst = Subst M.empty M.empty M.empty M.empty M.empty

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
  apply s (TFin e)    = TFin (apply s e)

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
  -- sexp normalizes: a concrete exponent expands into copies
  apply s (SExp b e rest) = sexp (apply s b) (apply s e) (apply s rest)

instance Substitutable SumRow where
  apply _ RNil = RNil
  apply s r@(RTail v) =
    case M.lookup v (rowSub s) of
      Nothing -> r
      Just r' -> apply s r'
  apply s (RCons st rest) = RCons (apply s st) (apply s rest)

instance Substitutable EffRow where
  apply s e@(Eff i mv) = case mv of
    Nothing -> e
    Just v  -> case M.lookup v (effSub s) of
      Nothing -> e
      -- the tail's own labels UNION in; that is what makes absorption
      -- (⟨io|ε⟩ ~ ⟨|ω⟩ ⟹ ω := ⟨io|υ⟩) come out right on both sides
      Just r  -> let Eff i' mv' = apply s r in Eff (i || i') mv'

instance Substitutable Arrow where
  apply s (Arrow i o e) = Arrow (apply s i) (apply s o) (apply s e)

instance Substitutable Scheme where
  -- Bound variables are removed from the substitution before it touches
  -- the arrow, so quantified names are never captured.
  apply s (Forall tv sv rv nv ev arr) =
    let s' = Subst (foldr M.delete (tySub s) tv)
                   (foldr M.delete (stSub s) sv)
                   (foldr M.delete (rowSub s) rv)
                   (foldr M.delete (expSub s) nv)
                   (foldr M.delete (effSub s) ev)
    in Forall tv sv rv nv ev (apply s' arr)

instance Substitutable Env where
  apply s = M.map (apply s)

--------------------------------------------------------------------------------
-- 4. Constraints and unification
--------------------------------------------------------------------------------

data Constraint
  = CEqTy Ty Ty
  | CEqStack SType SType
  | CEqEff EffRow EffRow
  | CFail String   -- carry a deferred inference error to the solver
  deriving (Eq, Show)

-- All variables (type, stack, row, exponent) in order of first
-- appearance, recursing through Fn⟨Γ ⇒ Δ⟩ and (… | …) element types.
-- The single traversal backing occurs checks, generalization, and
-- normalization.
type Vars = ([TVar], [SVar], [RVar], [NVar], [EVar])

noVars :: Vars
noVars = ([], [], [], [], [])

varsOfEff :: EffRow -> Vars
varsOfEff (Eff _ (Just v)) = ([], [], [], [], [v])
varsOfEff _                = noVars

varsOfTy :: Ty -> Vars
varsOfTy (TVarTy v)  = ([v], [], [], [], [])
varsOfTy TInt        = noVars
varsOfTy TStr        = noVars
varsOfTy TSym        = noVars
varsOfTy (TFn arr)   = varsOfArrow arr
varsOfTy (TSum row)  = varsOfRow row
varsOfTy (TData _ as) = foldr (catVars . varsOfStack) noVars as
varsOfTy (TFin e)    = varsOfExp e

varsOfStack :: SType -> Vars
varsOfStack SEnd             = noVars
varsOfStack (STail v)        = ([], [v], [], [], [])
varsOfStack (SCons t rest)   = varsOfTy t `catVars` varsOfStack rest
varsOfStack (SExp b e rest)  =
  varsOfStack b `catVars` varsOfExp e `catVars` varsOfStack rest

varsOfExp :: Exp -> Vars
varsOfExp (Exp _ (Just n)) = ([], [], [], [n], [])
varsOfExp _                = noVars

varsOfRow :: SumRow -> Vars
varsOfRow RNil            = noVars
varsOfRow (RTail v)       = ([], [], [v], [], [])
varsOfRow (RCons st rest) = varsOfStack st `catVars` varsOfRow rest

catVars :: Vars -> Vars -> Vars
catVars (t1, s1, r1, n1, e1) (t2, s2, r2, n2, e2) =
  (t1 ++ t2, s1 ++ s2, r1 ++ r2, n1 ++ n2, e1 ++ e2)

varsOfArrow :: Arrow -> Vars
varsOfArrow (Arrow i o e) =
  let (ts, ss, rs, ns, es) =
        varsOfStack i `catVars` varsOfStack o `catVars` varsOfEff e
  in (nub ts, nub ss, nub rs, nub ns, nub es)

-- Occurs checks.  Callers (bind*Var) only ever check against
-- fully-applied targets, so a pure structural traversal is sufficient.
occursTy :: TVar -> Ty -> Bool
occursTy a t = let (ts, _, _, _, _) = varsOfTy t in a `elem` ts

occursStack :: SVar -> SType -> Bool
occursStack v st = let (_, ss, _, _, _) = varsOfStack st in v `elem` ss

occursRow :: RVar -> SumRow -> Bool
occursRow v row = let (_, _, rs, _, _) = varsOfRow row in v `elem` rs

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
    (TFn (Arrow i1 o1 g1), TFn (Arrow i2 o2 g2)) -> do
      s' <- unifyStack s i1 i2
      s'' <- unifyStack s' o1 o2
      unifyEff s'' g1 g2
    (TSum r1, TSum r2)   -> unifyRow s r1 r2
    (TData n1 as1, TData n2 as2)
      | n1 == n2 && length as1 == length as2 ->
          foldM (\acc (x, y) -> unifyStack acc x y) s (zip as1 as2)
    -- two indices agree exactly when their bounds do: the same
    -- `k + n = e` solving that correlates bundle widths
    (TFin e1, TFin e2) -> unifyExp s e1 e2
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

-- Grades unify; they do not join.  Composition therefore FORCES two
-- arrows' effect rows equal, and the "join" people expect falls out of
-- label absorption into an open tail: ⟨io|ε⟩ ~ ⟨|ω⟩ binds ω := ⟨io|υ⟩.
-- Tail-only, one label, so this is the whole algebra (design-effects.md;
-- the same discipline that keeps stacks, sums and widths principal).
unifyEff :: Subst -> EffRow -> EffRow -> Either String Subst
unifyEff s e1 e2 =
  case (apply s e1, apply s e2) of
    (a, b) | a == b -> Right s
    -- both closed: the label sets must already agree
    (a@(Eff i1 Nothing), b@(Eff i2 Nothing))
      | i1 == i2  -> Right s
      | otherwise -> clash a b
    -- one open, one closed: the tail supplies the missing labels.  It
    -- can only ADD them, so an io on the open side with none on the
    -- closed side is unsatisfiable.
    (a@(Eff i1 (Just v)), b@(Eff i2 Nothing))
      | i1 && not i2 -> clash a b
      | otherwise    -> bindEffVar s v (Eff (i2 && not i1) Nothing)
    (a@(Eff i1 Nothing), b@(Eff i2 (Just w)))
      | i2 && not i1 -> clash a b
      | otherwise    -> bindEffVar s w (Eff (i1 && not i2) Nothing)
    -- both open: bridge the tails.  Equal labels ⇒ share one tail;
    -- otherwise the label-poorer side's tail takes on the difference
    -- AND the other tail, which is what makes `1 >> print` io without
    -- needing a fresh variable here (solve is a pure fold).
    (Eff i1 (Just v), Eff i2 (Just w))
      | i1 == i2  -> bindEffVar s v (Eff False (Just w))
      | i1        -> bindEffVar s w (Eff True (Just v))
      | otherwise -> bindEffVar s v (Eff True (Just w))
  where
    clash x y = Left $ "Cannot unify effects: " ++ showEff x
                    ++ " vs " ++ showEff y

showEff :: EffRow -> String
showEff e = if eIO e then "io" else "pure"

bindEffVar :: Subst -> EVar -> EffRow -> Either String Subst
bindEffVar s v row
  | eTail row == Just v, not (eIO row) = Right s
  | eTail row == Just v =
      Left $ "Occurs check failed on effect: " ++ show v
  | otherwise =
      Right s { effSub = M.insert v row (effSub s) }

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
    step s (CEqEff e1 e2)     = unifyEff s e1 e2
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

freshEVarName :: Infer EVar
freshEVarName = Infer $ do
  n <- get
  put (n + 1)
  pure (EV ("ε" ++ show n))

-- One-shot simultaneous substitution, NO chasing.  Instantiation is a
-- rename: a scheme generalized in one inference run may bind names (a0,
-- ρ1, …) that textually coincide with this run's fresh names, so using
-- the solver's chasing `apply` here can chain (a0 → a1 → a2, collapsing
-- distinct binders) or even cycle (a0 → a0, diverging).
substOnce :: Subst -> Arrow -> Arrow
substOnce s (Arrow i o e) = Arrow (goS i) (goS o) (goE' e)
  where
    goS SEnd = SEnd
    goS st@(STail v)  = fromMaybe st (M.lookup v (stSub s))
    goS (SCons t rest) = SCons (goT t) (goS rest)
    -- sexp, not SExp: substitution may ground an exponent (n := 0 from
    -- instantiateClosed), and the canonical form expands concrete
    -- copies away.  Rebuilding with the raw constructor left a literal
    -- zero-copy node that openTailedS then mistook for an open width —
    -- which made the recursive-call placement check reject every
    -- non-final exponent word, unreachable-branch runtime and all.
    goS (SExp b e rest) = sexp (goS b) (goE e) (goS rest)

    goE e@(Exp k mv) = case mv of
      Just n | Just (Exp k' mv') <- M.lookup n (expSub s) -> Exp (k + k') mv'
      _ -> e

    goE' e@(Eff i mv) = case mv of
      Just v | Just (Eff i' mv') <- M.lookup v (effSub s) -> Eff (i || i') mv'
      _ -> e

    goT t@(TVarTy v) = fromMaybe t (M.lookup v (tySub s))
    goT (TFn arr)  = TFn (substOnce s arr)
    goT (TSum row)   = TSum (goR row)
    goT (TData n as) = TData n (map goS as)
    -- NOT the catch-all: instantiation must freshen the bound, or
    -- every use site of a Fin-typed word would share one global n
    goT (TFin e)     = TFin (goE e)
    goT t            = t

    goR RNil = RNil
    goR row@(RTail v) = fromMaybe row (M.lookup v (rowSub s))
    goR (RCons st rest) = RCons (goS st) (goR rest)

-- Instantiate a polymorphic scheme with fresh type, stack, and row
-- variables (used for the final atom of a tensor chain, which may stay
-- open).
instantiate :: Scheme -> Infer Arrow
instantiate (Forall tvars svars rvars nvars evars arr) = do
  newTVs <- mapM (const freshTyVarName) tvars
  newSVs <- mapM (const freshSVarName) svars
  newRVs <- mapM (const freshRVarName) rvars
  newNVs <- mapM (const freshNVarName) nvars
  newEVs <- mapM (const freshEVarName) evars
  let tSub = M.fromList (zip tvars (map TVarTy newTVs))
      sSub = M.fromList (zip svars (map STail newSVs))
      rSub = M.fromList (zip rvars (map RTail newRVs))
      nSub = M.fromList (zip nvars (map (Exp 0 . Just) newNVs))
      eSub = M.fromList (zip evars [ Eff False (Just v) | v <- newEVs ])
  openEff (substOnce (Subst tSub sSub rSub nSub eSub) arr)

-- Every use of a scheme whose grade is CLOSED gets a fresh tail, so
-- composition can absorb labels into it: `1 >> print` works because the
-- literal's ⟨⟩ opens to ⟨|ε⟩ and unifies with print's ⟨io|ε'⟩.  Without
-- this, every pure word would refuse to sit next to an effectful one.
-- Schemes that already carry an explicit ε (apply, loop, the folds) are
-- left alone — their tail is their polymorphism.
openEff :: Arrow -> Infer Arrow
openEff (Arrow i o e@(Eff _ Nothing)) = do
  v <- freshEVarName
  pure (Arrow i o e { eTail = Just v })
openEff arr = pure arr

-- Instantiate a scheme *closed* for a non-final tensor atom: only the
-- OUTER TAILS of the arrow are closed (ρ := •) — that is all appendStack
-- needs.  Variables living purely inside element types (Fn⟨…⟩, sums)
-- are freshened like any instantiation: they are the atom's
-- polymorphism, not a remainder.  (Matches the grouped-compound closing
-- policy.)
instantiateClosed :: Scheme -> Infer Arrow
instantiateClosed (Forall tvars svars rvars nvars evars arr@(Arrow i o _)) = do
  newTVs <- mapM (const freshTyVarName) tvars
  let tailVs = openVarsS i ++ openVarsS o
  newSVs <- mapM (\v -> if v `elem` tailVs
                          then pure Nothing
                          else Just <$> freshSVarName) svars
  newRVs <- mapM (const freshRVarName) rvars
  newEVs <- mapM (const freshEVarName) evars
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
      eSub = M.fromList (zip evars [ Eff False (Just v) | v <- newEVs ])
  -- effect variables are FRESHENED, never closed: closing ε for a
  -- non-final atom would let `1 print` typecheck as pure.
  openEff (substOnce (Subst tSub sSub rSub nSub eSub) arr)

-- exponent variables on a stack's spine (not inside element types)
spineExpVars :: SType -> [NVar]
spineExpVars (SExp _ (Exp _ (Just n)) r) = n : spineExpVars r
spineExpVars (SExp _ _ r)                = spineExpVars r
spineExpVars (SCons _ r)                 = spineExpVars r
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
  | Use [String] Term     -- `use R1 R2` — an ambient scope.  The named
                          -- resources ride DEEPEST, and the rest of
                          -- the enclosing scope is the body; every
                          -- stage in it gets its routing written by
                          -- the elaborator (`elabUse`), which runs
                          -- between parse and infer.  This node never
                          -- reaches inference.
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
  | TokLAngle     -- ⟨ (open a Fn type: Fn⟨Σ ⇒ Θ⟩)
  | TokRAngle     -- ⟩ (close a Fn type)
  | TokFatArrow   -- ⇒ (the arrow inside a Fn type)
  | TokBangArrow  -- ⇒! / ->! (an IO arrow in a Fn type)
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
    go ('-':'>':'!':cs) = (TokBangArrow :) <$> go cs
    go ('-':'>':cs)     = (TokArrow :) <$> go cs
    go ('-':cs)
      | (ds@(_:_), rest) <- span isDigit cs =
          (TokIdent ('-' : ds) :) <$> go rest          -- negative literal
      | otherwise = (TokIdent "-" :) <$> go cs         -- subtraction
    go ('|':cs)         = (TokBar :) <$> go cs
    go ('^':cs)         = (TokCaret :) <$> go cs
    go (';':cs)         = (TokSeq :) <$> go cs   -- ; is a synonym for >>
    go ('⟨':cs)         = (TokLAngle :) <$> go cs     -- Fn⟨…⟩ type brackets
    go ('⟩':cs)         = (TokRAngle :) <$> go cs
    go ('⇒':'!':cs)     = (TokBangArrow :) <$> go cs
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
-- newlines adjacent to an operator or a bracket delimiter.
normalizeToks :: [Token] -> [Token]
normalizeToks = trim . collapse
  where
    -- A newline is a strict `>>`.  Two things absorb one:
    --
    --   * the railway operators (`>=>`, `>?>`, `>!>`) — composition a
    --     newline cannot itself express, so the operator wins;
    --   * a bracket delimiter, on its inner side: newlines just after
    --     `(`/`[` and just before `)`/`]`.  A bracket is an explicit
    --     scope, so a break against its edge is layout, not a stage
    --     boundary — that is what lets a wide atom wrap.
    --
    -- A newline BETWEEN stages inside a bracket is still `>>`: `(1 ⏎ 2)`
    -- is `(1 >> 2)`, exactly as at top level.  `>>` and `|` never absorb
    -- — a newline already *is* `>>`, and the row separator `|` must stay
    -- put so aligned track-columns work (`f |` ⏎ `| g` is two rows, not
    -- one collided `| |`).
    collapse [] = []
    collapse (TokNewline : ts) =
      case dropWhile (== TokNewline) ts of
        rest@(t : _) | absorbsBefore t -> collapse rest
        rest                           -> TokNewline : collapse rest
    collapse (t : ts)
      | absorbsAfter t = t : collapse (dropWhile (== TokNewline) ts)
      | otherwise      = t : collapse ts

    trim = dropWhile (== TokNewline) . dropTrailing
    dropTrailing = reverse . dropWhile (== TokNewline) . reverse

    -- newlines FOLLOWING this token are absorbed
    absorbsAfter t = railway t || t == TokLParen || t == TokLBrack
    -- newlines PRECEDING this token are absorbed
    absorbsBefore t = railway t || t == TokRParen || t == TokRBrack

    railway t =
      t == TokKleisli || t == TokOrElse || t == TokOrClose

-- Net bracket depth a source line contributes: `(`/`[` open, `)`/`]`
-- close, with `#` comments and string literals skipped (same escapes as
-- the tokenizer).  The line-based layers above the parser — def-body
-- blocks in `splitDefs`, the REPL's one-line read — consult this so a
-- bracket may span line breaks.
lineDepth :: String -> Int
lineDepth = go 0
  where
    go d []       = d
    go d ('#':_)  = d                    -- comment runs to end of line
    go d ('"':cs) = go d (skipStr cs)
    go d (c:cs)
      | c `elem` ("([" :: String) = go (d + 1) cs
      | c `elem` (")]" :: String) = go (d - 1) cs
      | otherwise                 = go d cs

    skipStr ('\\':_:cs) = skipStr cs
    skipStr ('"':cs)    = cs
    skipStr (_:cs)      = skipStr cs
    skipStr []          = []

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
-- `-> x y z` is the NAMING binder — the same construct written the
-- other way round, handing the wires straight back (see `mkName`).  The
-- arrow's side says which: names BEFORE it are cut from the stack,
-- names AFTER it label wires that keep flowing.  Both take the rest of
-- the scope as their body, which is why both are recognized here.
parseProgramToks :: [Token] -> Either String (Term, [Token])
parseProgramToks toks =
  case toks of
    -- `use R1 R2` opens an AMBIENT SCOPE, taking the rest of the scope
    -- as its body exactly as the binders do
    (TokIdent "use" : ts) | Just (rs, r) <- usePrefix ts -> mkUse rs r
    -- a leading arrow names the wires this scope was handed
    (TokArrow : ts) -> mkName ts
    _ ->
      case binderPrefix toks of
        Just (ps, rest) -> mkAbs ps rest
        Nothing -> do
          (t0, rest) <- parseRow toks
          loop t0 rest
  where
    -- `stage -> names`: the stage ends at the arrow (parseStage leaves
    -- it), and the names label the wires the stage just produced
    loop acc (TokArrow : rest) = do
      (nm, r') <- mkName rest
      Right (Seq acc nm, r')
    loop acc (TokNewline : rest)
      | (TokIdent "use" : ts) <- rest, Just (rs, r) <- usePrefix ts = do
          (u, r') <- mkUse rs r
          Right (Seq acc u, r')
      | (TokArrow : ts) <- rest = do
          (nm, r') <- mkName ts
          Right (Seq acc nm, r')
      | Just (ps, r) <- binderPrefix rest = do
          (abs', r') <- mkAbs ps r
          Right (Seq acc abs', r')
      | otherwise = do
          (t, rest') <- parseRow rest
          loop (Seq acc t) rest'
    loop acc rest = Right (acc, rest)

    -- `-> x _ y` is the NAMING binder: identity on the wires it names.
    -- They stay on the stack and pick up names for the rest of the
    -- enclosing scope — a wire label, not a cut.  It is sugar for the
    -- open binder that immediately puts back what it took:
    --
    --   -> x _ y   ≡   x _ y ... -> x _ y ...
    --
    -- so it needs no machinery of its own: consume the deepest wires
    -- (leftmost = deepest, as everywhere), re-push them under the
    -- remainder, bind the names.  Slots use the stage vocabulary, same
    -- as any binder: a name takes one wire, `_` skips one.  `...` is
    -- rejected — passing the rest along is what the form already IS.
    --
    -- The body is the rest of the scope, introduced by an explicit `->`
    -- or by an ordinary stage break (`;`, `>>`, or a newline).
    mkName ts = do
      let (params, rest0) = span isParamTok ts
      slots <- mapM slotOf params
      case slots of
        [] -> Left "'-> …' needs at least one name"
        _  -> Right ()
      let ns = [ n | Just n <- slots ]
      case [ p | (p, n) <- zip ns [0 :: Int ..], p `elem` take n ns ] of
        (p : _) -> Left $ "Duplicate parameter: " ++ p
        []      -> Right ()
      bodyToks <- case rest0 of
        (TokArrow : more)   -> Right more     -- `-> names -> body`
        (TokSeq : more)     -> Right more
        (TokNewline : more) -> Right more
        r | endsScope r ->
              Left "'-> …' ends its scope: nothing is left to use the names"
        (t : _) -> Left $
          "'-> …' must be followed by its body (a newline, ';' or '->')"
            ++ ", got: " ++ show t
      case bodyToks of
        [] -> Left "'-> …' ends its scope: nothing is left to use the names"
        _  -> Right ()
      -- the wires go straight back out, so the body starts by re-pushing
      -- them; reuse the parser so the desugaring is exactly the stage a
      -- user would have written
      let repush = [ TokIdent (fromMaybe "_" s) | s <- slots ] ++ [TokEllipsis]
      (body, rest') <- parseProgramToks (repush ++ TokNewline : bodyToks)
      Right (OpenAbs slots True body, rest')

    -- a run of resource names, then the body (a stage break or `->`)
    usePrefix ts = case span isUseTok ts of
      (ns@(_ : _), r) -> Just ([ n | TokIdent n <- ns ], r)
      _               -> Nothing
    isUseTok (TokIdent n) = n /= "_"
    isUseTok _            = False

    mkUse names rest = do
      case [ n | (n, i) <- zip names [0 :: Int ..], n `elem` take i names ] of
        (n : _) -> Left $ "Duplicate resource in `use`: " ++ n
        []      -> Right ()
      bodyToks <- case rest of
        (TokArrow : more)   -> Right more
        (TokSeq : more)     -> Right more
        (TokNewline : more) -> Right more
        r | endsScope r -> Left "'use …' ends its scope: there is no body \
                                \for the resources to be ambient in"
        (t : _) -> Left $ "'use …' must be followed by its body (a newline, \
                          \';' or '->'), got: " ++ show t
      (body, rest') <- parseProgramToks bodyToks
      Right (Use names body, rest')

    slotOf (TokIdent "_") = Right Nothing
    slotOf (TokIdent n)   = Right (Just n)
    slotOf TokEllipsis    =
      Left "'...' is implicit in '-> …' — it always passes the rest along"
    slotOf _              = Left "Malformed parameter list"

    endsScope []              = True
    endsScope (TokRParen : _) = True
    endsScope (TokRBrack : _) = True
    endsScope _               = False

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
    -- EVERY empty arm defaults to identity, not just the first and
    -- last: `(a | |)` ≡ `(a | pass | pass)`, `(| | c)` ≡
    -- `(pass | pass | c)`.  This is what makes track-column layout
    -- work: each line of a vertical pipeline touches one track and
    -- draws the others straight through as aligned `|` wires.
    loop acc (TokBar : rest@(TokBar : _)) =
      loop (Prim "pass" : acc) rest
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

parseStage :: [Token] -> Either String (Stage, [Token])
parseStage = go []
  where
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
    -- `-> names` closes the stage it follows and is left for
    -- parseProgramToks (the body is the rest of the SCOPE, which only
    -- that level can build).  With no stage to its left — an arrow
    -- straight after `;`/`>>` — the stage is just `pass`.
    go acc rest@(TokArrow : _)
      | null acc  = Right (Stage [Prim "pass"] False, rest)
      | otherwise = Right (Stage (reverse acc) False, rest)
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

-- A declaration parameter is kinded: a bare name stands for ONE WIRE,
-- `...` stands for a whole stack.  At most one stack parameter, and it
-- must come last — which is what makes a splice unspellable, since a
-- stack variable then always sits in tail position (`ssplice v SEnd`
-- is just `STail v`).
-- A third kind joins them: `PWidth`, a WIDTH (an exponent variable).
-- It is declared by USE — a parameter mentioned under `^` in the body
-- is a width — because the two roles are syntactically disjoint, so
-- position can decide without an annotation.  Width parameters are
-- supported on `type` aliases only for now (a `data` type would need
-- TData to carry width arguments).
data TyParam = PWire TVar | PStack SVar | PWidth NVar
  deriving (Eq, Show)

pName :: TyParam -> String
pName (PWire (TV n))  = n
pName (PStack (SV n)) = n
pName (PWidth (NV n)) = n

isStackParam :: TyParam -> Bool
isStackParam (PStack _) = True
isStackParam _          = False

isWidthParam :: TyParam -> Bool
isWidthParam (PWidth _) = True
isWidthParam _          = False

-- the stack a parameter stands for when the declaration is instantiated
paramStack :: TyParam -> SType
paramStack (PWire tv)  = SCons (TVarTy tv) SEnd
paramStack (PStack sv) = STail sv
paramStack (PWidth nv) =
  -- unreachable: `data` declarations reject width parameters at
  -- declaration time, and only they build a TData spine from params
  error ("paramStack: width parameter " ++ show nv
         ++ " (data declarations reject these)")

-- An argument at a use site: a stack for wire/`...` parameters, a
-- width for `^`-parameters.  TData still carries only stacks (data
-- types cannot take width parameters yet), so this widening is
-- confined to aliases and to display.
data TyArg = AStack SType | AWidth Exp
  deriving (Eq, Show)

data Alias = Alias
  { aName   :: String
  , aParams :: [TyParam]
  , aBody   :: Ty
  } deriving (Eq, Show)

-- A recursive `type` declaration: a NOMINAL data type.  Name(args)
-- unifies only with itself (argwise), never with its unfolding; the
-- generated coercions `Name` (roll) and `Name?` (unroll) are the only
-- doors, and both are runtime no-ops.
data DataDecl = DataDecl
  { dName   :: String
  , dParams :: [TyParam]
  , dBody   :: Ty
  , dResource :: Bool   -- declared with `resource`: a threaded wire.
                        -- Nominal like any data type, but it also (a)
                        -- generates no fold — you unroll it, you do not
                        -- eliminate it by points — and (b) folds onto
                        -- the ARROW as `=Name>` when it rides a suffix.
  } deriving (Eq, Show)

-- A THEORY is named slots plus laws.  Not a typeclass: nothing is
-- inferred or dispatched, an instance is selected BY NAME with `use`,
-- and the laws are ordinary Braid programs that must evaluate to `true`
-- — so an instance is an AUDITED model rather than a promise
-- (design-effects.md: "laws as runnable checks ... the
-- laws-are-programs doctrine given a front door").
data Theory = Theory
  { thName   :: String
  , thParams :: [TyParam]
  , thSlots  :: [(String, Arrow)]    -- declared signatures
  , thLaws   :: [(String, String)]   -- name, program source
  } deriving (Eq, Show)

-- An INSTANCE fills a theory's slots.  Each binding becomes an ordinary
-- def named `Inst#slot`, so resolution is a renaming at elaboration —
-- once per scope, never a dictionary per call.
data Instance = Instance
  { inName     :: String
  , inTheory   :: String
  , inArgs     :: [SType]
  , inBindings :: [(String, String)]  -- slot, program source
  } deriving (Eq, Show)

-- NOT `#`: that starts a comment, so a generated name using it would be
-- eaten by the lexer the moment it appeared in emitted source.
slotDefName :: String -> String -> String
slotDefName inst slot = inst ++ "@" ++ slot

lawDefName :: String -> String -> String
lawDefName inst lawNm = inst ++ "@law@" ++ lawNm

-- a generated law def, and the (instance, law) it came from
lawParts :: String -> Maybe (String, String)
lawParts n = case breakOn "@law@" n of
  Just (i, l) -> Just (i, l)
  Nothing     -> Nothing
  where
    breakOn pat str = go "" str
      where
        go _   []          = Nothing
        go acc r@(c : cs)
          | take (length pat) r == pat = Just (reverse acc, drop (length pat) r)
          | otherwise = go (c : acc) cs

dataSig :: DataDecl -> (String, [TyParam])
dataSig d = (dName d, dParams d)

-- The schemes and runtime entries a data declaration contributes:
--   Name   : ∀params. body ⇒ Name(params)      (roll)
--   unName : ∀params. Name(params) ⇒ body      (unroll)
dataDeclArtifacts :: DataDecl
                  -> ([(String, Scheme)], [(String, (Int, Bool, Term))])
dataDeclArtifacts d =
  ( [ (dName d,          Forall tvs svs [] nvs [] (Arrow bodyStack namedStack effPure))
    , ("un" ++ dName d,  Forall tvs svs [] nvs [] (Arrow namedStack bodyStack effPure)) ]
      ++ mergeSchemes
  , [ (dName d,         (rollArity, rollOpen, rollTerm))
    , ("un" ++ dName d, (1, False, unrollTerm)) ]
      ++ mergeRuns )
  where
    ps         = dParams d
    tvs        = [ tv | PWire tv  <- ps ]
    svs        = [ sv | PStack sv <- ps ]
    nvs        = [ nv | PWidth nv <- ps ]   -- always [] today (see below)
    namedStack = SCons (TData (dName d) (map paramStack ps)) SEnd
    rollOpen   = openTailedS bodyStack
    -- an n-ary uniform collapse for this declaration's arity: the
    -- runtime merge strips any tag; only the SCHEME is arity-specific,
    -- so we generate it per declaration (the counting-theorem dodge)
    (mergeSchemes, mergeRuns) =
      case dBody d of
        TSum row | k >= 2 ->
          ( [ ("merge" ++ dName d
            , Forall [] [SV "ρ"] [] [] []
                (arrPure (SCons (TSum uniformRow) SEnd) (STail (SV "ρ")))) ]
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
dataFoldSrc d | dResource d = Nothing   -- a resource is unrolled, not
                                        -- eliminated by points
dataFoldSrc d =
  case dBody d of
    TSum row -> do
      alts <- rowAlts row
      let k      = length alts
          fs     = [ "f" ++ show i | i <- [1 .. k] ]
          selfTy = TData (dName d) (map paramStack (dParams d))
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
                    -- recursive slots are pushed FIRST, so a case sees
                    -- FOLDED-then-payload however the alternative was
                    -- written.  (The splice generator did this with
                    -- rotLast; doing it here makes the convention one
                    -- rule instead of two, and keeps `foldList`'s
                    -- accumulator-first step.)
                    tagged = zip xs payload
                    slots  = map slot ([ q | q <- tagged, snd q == selfTy ]
                                       ++ [ q | q <- tagged, snd q /= selfTy ])
                    stages =
                      head slots
                        : [ unwords (replicate n "_") ++ " " ++ sl
                          | (n, sl) <- zip [1 :: Int ..] (tail slots) ]
                    body = intercalate " >> " stages
                             ++ " >> " ++ fi ++ " ... >> apply"
                in Just ("(" ++ unwords xs ++ " -> " ++ body ++ ")")

          comp (fi, st) = compClosed fi (stackElems st)

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
    hasSplice (SCons _ r)   = hasSplice r
    hasSplice _             = False
    stackElems SEnd          = []
    stackElems (STail _)     = []
    stackElems (SCons t st)  = t : stackElems st

occursData :: String -> Ty -> Bool
occursData n = goT
  where
    goT (TData m as)        = m == n || any goS as
    goT (TSum r)            = goR r
    goT (TFn (Arrow i o _))   = goS i || goS o  -- recursion THROUGH a Fn is codata
    goT _                   = False
    goR (RCons st r) = goS st || goR r
    goR _            = False
    goS (SCons t st)   = goT t || goS st
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
-- `theory Name(params)` + indented `slot : Σ ⇒ Θ` and `law nm = prog`
parseTheory :: [Alias] -> [(String, [TyParam])] -> String -> [String]
            -> Either String Theory
parseTheory aliases dataSigs header body = do
  (name, params) <- parseHead
  entries <- mapM (parseEntry params) (filter (not . blank) body)
  let slots = [ e | Left  e <- entries ]
      laws  = [ e | Right e <- entries ]
  case slots of
    [] -> Left $ "theory " ++ name ++ " declares no operations"
    _  -> Right ()
  pure (Theory name params slots laws)
  where
    blank l = all isSpace (takeWhile (/= '#') l)
    parseHead = do
      -- the header carries the block's `=`; it is punctuation, not a name
      toks <- normalizeToks <$> tokenize (takeWhile (/= '=') header)
      case toks of
        [TokIdent "theory", TokIdent n] -> Right (n, [])
        (TokIdent "theory" : TokIdent n : TokLParen : rest) ->
          (,) n <$> theoryParams rest
        _ -> Left $ "Malformed theory declaration: " ++ header
    theoryParams (TokIdent p : TokComma : r) = (PWire (TV p) :) <$> theoryParams r
    theoryParams [TokIdent p, TokRParen]     = Right [PWire (TV p)]
    theoryParams [TokEllipsis, TokRParen]    = Right [PStack (SV "s")]
    theoryParams _ = Left "Malformed theory parameter list"

    -- `law nm = program` | `slot : Σ ⇒ Θ`
    parseEntry params l =
      case words l of
        ("law" : nm : "=" : _) ->
          Right (Right (nm, drop 1 (dropWhile (/= '=') l)))
        _ -> case break (== ':') l of
          (lhs, ':' : sig)
            | [nm] <- words lhs -> do
                -- a slot signature is an arrow; reuse the Fn parser
                ty <- parseTyBody aliases dataSigs params ("Fn⟨" ++ sig ++ "⟩")
                case ty of
                  TFn arr -> Right (Left (nm, arr))
                  _ -> Left $ "theory: slot '" ++ nm
                           ++ "' needs a signature like `Σ ⇒ Θ`"
          _ -> Left $ "Malformed theory entry: " ++ dropWhile isSpace l

-- `instance Name : Theory(args)` + indented `slot = program`
parseInstance :: [Alias] -> [(String, [TyParam])] -> String -> [String]
              -> Either String Instance
parseInstance aliases dataSigs header body = do
  (nm, th, args) <- parseHead
  binds <- mapM parseBind (filter (not . blank) body)
  pure (Instance nm th args binds)
  where
    blank l = all isSpace (takeWhile (/= '#') l)
    parseHead =
      case break (== ':') (takeWhile (/= '=') header) of
        (lhs, ':' : rhs) | ["instance", nm] <- words lhs -> do
          toks <- normalizeToks <$> tokenize rhs
          case toks of
            [TokIdent th] -> Right (nm, th, [])
            (TokIdent th : TokLParen : rest) -> (,,) nm th <$> instArgs rest
            _ -> Left $ "Malformed instance head: " ++ header
        _ -> Left $ "Malformed instance declaration: " ++ header
    instArgs rest = do
      let names = [ n | TokIdent n <- takeWhile (/= TokRParen) rest ]
      mapM one names
    one n = do
      t <- parseTyBody aliases dataSigs [] n
      Right (SCons t SEnd)
    parseBind l =
      case break (== '=') l of
        (lhs, '=' : rhs) | [nm] <- words lhs -> Right (nm, rhs)
        _ -> Left $ "Malformed instance binding: " ++ dropWhile isSpace l

parseTypeLine :: [Alias] -> [(String, [TyParam])] -> String
              -> Either String (Either Alias DataDecl)
parseTypeLine aliases dataSigs line =
  case break (== '=') line of
    (lhs, '=' : rhs) -> do
      (kw, name, params) <- parseHead lhs
      let sigs = (name, params) : dataSigs
      body <- parseTyBody aliases sigs params rhs
      -- KINDS BY USE: every named parameter parses as a wire, and an
      -- occurrence under `^` makes it an exponent variable in the body.
      -- So the body's own free-variable sets settle the kinds.
      let (bodyTVs, bodySVs, _, bodyNVs, _) = varsOfTy body
          reclass q@(PWire (TV nm))
            | NV nm `elem` bodyNVs, TV nm `elem` bodyTVs =
                Left $ "Type " ++ name ++ ": parameter '" ++ nm
                    ++ "' is used both as a wire and as a width (^"
                    ++ nm ++ ")"
            | NV nm `elem` bodyNVs = Right (PWidth (NV nm))
            | otherwise            = Right q
          reclass q = Right q
      params <- mapM reclass params
      let occurs (PWire tv)  = tv `elem` bodyTVs
          occurs (PStack sv) = sv `elem` bodySVs
          occurs (PWidth nv) = nv `elem` bodyNVs
      if all occurs params
        then Right ()
        else Left $ "Type alias " ++ name
                 ++ ": every parameter must occur in the body"
      -- a width parameter would have to ride in TData's argument list,
      -- which carries stacks only; aliases are transparent, so they are
      -- fine.  Reject the nominal case with direction.
      case [ q | q <- params, isWidthParam q ] of
        (q : _) | kw == "data" || occursData name body ->
          Left $ "Type " ++ name ++ ": width parameter '" ++ pName q
              ++ "' is supported on `type` aliases only, not on "
              ++ "recursive/`data` declarations"
        _ -> Right ()
      -- The ambiguous-product-split check is gone: a wire parameter is
      -- exactly one wire, so juxtaposing them is never ambiguous, and a
      -- stack parameter is forced into tail position by the parser.
      -- `data` is always nominal; `type` is a transparent alias unless
      -- self-recursive (which forces nominality)
      -- a resource is nominal by keyword, never an alias: its whole
      -- point is that `Int Int` must NOT silently become a GameState
      pure $ if kw == "data" || kw == "resource" || occursData name body
               then Right (DataDecl name params body (kw == "resource"))
               else Left  (Alias name params body)
    _ -> Left $ "Malformed type declaration (missing '='): " ++ line
  where
    parseHead lhs = do
      toks <- normalizeToks <$> tokenize lhs
      case toks of
        [TokIdent kw, TokIdent name]
          | kw `elem` declKws, validName name ->
              Right (kw, name, [])
        (TokIdent kw : TokIdent name : TokLParen : rest)
          | kw `elem` declKws, validName name ->
              (,,) kw name <$> paramList rest
        _ -> Left $ "Malformed type declaration: " ++ line
    -- a bare name is ONE WIRE; `...` is a whole stack and may only be
    -- the last parameter (one stack parameter at most).  That placement
    -- rule is what keeps a stack variable in tail position, so no
    -- declaration can spell a splice.
    paramList (TokIdent p : TokComma : rest) = (PWire (TV p) :) <$> paramList rest
    paramList [TokIdent p, TokRParen]        = Right [PWire (TV p)]
    paramList [TokEllipsis, TokRParen]       = Right [PStack (SV "s")]
    paramList (TokEllipsis : _) =
      Left "'...' must be the last type parameter"
    paramList _ = Left "Malformed type parameter list"
    declKws = ["type", "data", "resource"]
    validName n = n `notElem` [ "Int", "Str", "Sym", "Fn", "Fin"
                              , "type", "data", "resource", "•" ]
    tyParams t = let (_, ss, _, _, _) = varsOfTy t in ss
    -- every stack appearing anywhere in a type body
    stacksOf :: Ty -> [SType]
    stacksOf (TSum r)     = rowStacks r
    stacksOf (TData _ as) = as ++ concatMap stackInner as
    stacksOf _            = []
    rowStacks RNil         = []
    rowStacks (RTail _)    = []
    rowStacks (RCons st r) = st : stackInner st ++ rowStacks r
    stackInner (SCons t st)   = stacksOf t ++ stackInner st
    stackInner _              = []

-- Parse a full RHS.  The body is a STACK, not just an element: that is
-- what makes `type T = Int^3` work (the `^` handling lives in the stack
-- parser).  A one-wire stack is that wire; anything wider becomes the
-- 1-ary-sum-as-segment form the exponent parser already round-trips.
parseTyBody :: [Alias] -> [(String, [TyParam])] -> [TyParam] -> String
            -> Either String Ty
parseTyBody aliases dataSigs params src = do
  toks <- normalizeToks <$> tokenize src
  (st, rest) <- parseTyStack aliases dataSigs params toks
  case rest of
    [] -> case st of
            SCons t SEnd -> Right t
            _            -> Right (TSum (RCons st RNil))
    _  -> Left $ "Unexpected tokens after type expression: " ++ show rest

-- A declaration's RHS is a STACK.  `goStack` lives inside parseTyElem's
-- where-block; rather than hoist that whole family, parse the body as a
-- 1-ary parenthesized row and unwrap — the same "a 1-ary sum IS a
-- segment" convention the exponent parser already uses for `(A B)^n`.
parseTyStack :: [Alias] -> [(String, [TyParam])] -> [TyParam] -> [Token]
             -> Either String (SType, [Token])
parseTyStack aliases dataSigs params toks = do
  (t, rest) <- parseTyElem aliases dataSigs params
                 (TokLParen : toks ++ [TokRParen])
  case t of
    TSum (RCons st RNil) -> Right (st, rest)
    _                    -> Left "Expected a type expression"

parseTyElem :: [Alias] -> [(String, [TyParam])] -> [TyParam] -> [Token]
            -> Either String (Ty, [Token])
parseTyElem aliases dataSigs params toks = case toks of
  -- Fn⟨Σ ⇒ Θ⟩ (Unicode, mirrors :t output) or Fn(Σ -> Θ) (ASCII): a
  -- reified program as an element type.  The inner stacks parse like
  -- any type stack (params splice, • is empty, Fn nests).
  (TokIdent "Fn" : TokLAngle : rest) -> parseFn TokRAngle rest
  (TokIdent "Fn" : TokLParen : rest) -> parseFn TokRParen rest
  (TokIdent "Fn" : _) ->
    Left "Fn must be written Fn⟨Σ ⇒ Θ⟩ (or Fn(Σ -> Θ))"
  -- Fin(n): an index into a width-n bundle.  Its argument is a WIDTH,
  -- so it reuses the exponent parser rather than the stack parser.
  (TokIdent "Fin" : TokLParen : rest) -> do
    (e, rest1) <- expLit rest
    case rest1 of
      (TokRParen : rest2) -> pure (TFin e, rest2)
      _ -> Left "Expected ')' to close Fin(…)"
  (TokIdent "Fin" : _) -> Left "Fin must be written Fin(n)"
  (TokLParen : rest) -> do
    (alts, rest') <- goAlts rest
    pure (TSum (foldr RCons RNil alts), rest')
  (TokIdent "Int" : rest) -> pure (TInt, rest)
  (TokIdent "Str" : rest) -> pure (TStr, rest)
  (TokIdent "Sym" : rest) -> pure (TSym, rest)
  (TokIdent name : TokLParen : rest)
    | Just ps <- lookup name dataSigs -> do
        (args, rest') <- goArgs ps rest
        if length args /= length ps
          then Left $ "Type " ++ name ++ " expects "
                   ++ show (length ps) ++ " argument(s)"
          else do
            -- data types carry stacks only (no width parameters yet),
            -- and a wire parameter takes exactly one wire
            sts <- mapM (stackArg name) args
            case [ (q, a) | (q, a) <- zip ps sts
                 , not (isStackParam q), closedArity a /= 1 || openTailedS a ] of
              ((q, a) : _) -> Left $ "Type " ++ name ++ ": parameter '"
                                 ++ pName q ++ "' takes one wire, but was "
                                 ++ "given '" ++ show a
                                 ++ "' (declare it '...' to take a stack)"
              [] -> pure (TData name sts, rest')
    | Just al <- lookupAlias name aliases -> do
        (args, rest') <- goArgs (aParams al) rest
        body <- applyAlias al args
        pure (body, rest')
  (TokIdent name : rest)
    | Just (PWire tv) <- lookupParam name params -> pure (TVarTy tv, rest)
    | Just (PStack _) <- lookupParam name params ->
        Left $ "Type parameter " ++ name
             ++ " is a stack (`...`): it cannot sit inside another element"
    | Just (PWidth _) <- lookupParam name params ->
        Left $ "Type parameter " ++ name
             ++ " is a width: write it as an exponent (T^" ++ name ++ ")"
    | Just [] <- lookup name dataSigs -> pure (TData name [], rest)
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
    goStack (TokEllipsis : rest)
      | Just (PStack sv) <- stackParam params = do
          (suffix, rest') <- goStackEnd rest
          case suffix of
            SEnd -> pure (STail sv, rest')
            _ -> Left "'...' must be the last thing in its stack"
      | otherwise = Left "'...' needs a `...` parameter on the declaration"
    goStack ts@(TokIdent name : rest)
      | Just (PStack sv) <- lookupParam name params = do
          (suffix, rest') <- goStackEnd rest
          case suffix of
            SEnd -> pure (STail sv, rest')
            _ -> Left $ "The stack parameter '" ++ name
                     ++ "' must be the last thing in its stack"
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
    -- a width: a literal, or a declared parameter.  A parameter used
    -- here IS a width — `parseTypeLine` reclassifies afterwards from
    -- the body's free variables, so no annotation is needed.
    expLit (TokInt k : rest) | k >= 0 = Right (Exp k Nothing, rest)
    expLit (TokIdent nm : rest)
      | Just q <- lookupParam nm params =
          Right (Exp 0 (Just (NV (pName q))), rest)
      | otherwise =
          Left $ "Exponent variable ^" ++ nm ++ " is not a parameter of "
              ++ "this declaration — add it to the parameter list"
    expLit _ =
      Left "Expected an exponent (a number or a width parameter) after '^'"
    goStackEnd rest = case rest of
      (TokBar : _)      -> pure (SEnd, rest)
      (TokRParen : _)   -> pure (SEnd, rest)
      (TokComma : _)    -> pure (SEnd, rest)
      (TokFatArrow : _) -> pure (SEnd, rest)   -- Fn⟨Σ ⇒ …⟩ boundary
      (TokBangArrow : _) -> pure (SEnd, rest)  -- Fn⟨Σ ⇒! …⟩ boundary
      (TokArrow : _)    -> pure (SEnd, rest)   -- Fn(Σ -> …) boundary
      (TokRAngle : _)   -> pure (SEnd, rest)   -- Fn⟨… ⇒ Θ⟩ close
      []                -> pure (SEnd, [])
      _                 -> goStack rest
    -- Fn⟨Σ ⇒ Θ⟩ / Fn(Σ -> Θ): two stacks around an arrow, then `close`
    parseFn close ts = do
      (inSt, rest1) <- goStack ts
      -- the arrow's own shape carries the grade: ⇒ is pure, ⇒! is io.
      -- A declared pure Fn type therefore MEANS pure — it refuses to
      -- unify with an io quotation rather than quietly accepting one.
      (rest2, grade) <- case rest1 of
                 (TokFatArrow : r)  -> Right (r, effPure)
                 (TokArrow : r)     -> Right (r, effPure)
                 (TokBangArrow : r) -> Right (r, effIO)
                 _ -> Left "Expected '⇒' (or '->', '⇒!') inside a Fn type"
      (outSt, rest3) <- goStack rest2
      case rest3 of
        (t : r) | t == close -> Right (TFn (Arrow inSt outSt grade), r)
        _ -> Left $ "Expected '"
                 ++ (if close == TokRAngle then "⟩" else ")")
                 ++ "' to close the Fn type"
    stackArg _ (AStack st) = Right st
    stackArg n (AWidth e)  =
      Left $ "Type " ++ n ++ ": a width argument (" ++ show e
          ++ ") is not allowed here — width parameters are supported on "
          ++ "`type` aliases only"
    stackParam ps = case [ q | q@(PStack _) <- ps ] of
                      (q : _) -> Just q
                      []      -> Nothing
    -- constructor/alias arguments, parsed against the DECLARED kinds:
    -- a width position takes a number (or a width parameter in scope),
    -- everything else takes a stack.
    goArgs ks ts = do
      let (k, ks') = case ks of
                       (q : more) -> (Just q, more)
                       []         -> (Nothing, [])
      (a, rest) <- goArg k ts
      case rest of
        (TokComma : rest')  -> do
          (args, rest'') <- goArgs ks' rest'
          pure (a : args, rest'')
        (TokRParen : rest') -> pure ([a], rest')
        _ -> Left "Expected ',' or ')' in type arguments"

    goArg (Just (PWidth _)) ts = do
      (e, rest) <- expLit ts
      pure (AWidth e, rest)
    goArg _ ts = do
      (st, rest) <- goStack ts
      pure (AStack st, rest)

lookupParam :: String -> [TyParam] -> Maybe TyParam
lookupParam n ps = case [ q | q <- ps, pName q == n ] of
                     (q : _) -> Just q
                     []      -> Nothing

applyAlias :: Alias -> [TyArg] -> Either String Ty
applyAlias al args
  | length args /= length (aParams al) =
      Left $ "Type alias " ++ aName al ++ " expects "
           ++ show (length (aParams al)) ++ " argument(s)"
  | otherwise = do
      (tm, sm, nm) <- foldM bind (M.empty, M.empty, M.empty)
                            (zip (aParams al) args)
      pure (substParams tm sm nm (aBody al))
  where
    -- a wire parameter takes exactly one wire; a `...` parameter takes
    -- the whole argument stack; a `^` parameter takes a width
    bind (tm, sm, nm) (PWire tv, AStack (SCons t SEnd)) =
      Right (M.insert tv t tm, sm, nm)
    bind _ (PWire tv, AStack st) =
      Left $ "Type " ++ aName al ++ ": parameter '" ++ show tv
           ++ "' takes one wire, but was given '" ++ show st
           ++ "' (declare it '...' to take a stack)"
    bind (tm, sm, nm) (PStack sv, AStack st) = Right (tm, M.insert sv st sm, nm)
    bind (tm, sm, nm) (PWidth nv, AWidth e)  = Right (tm, sm, M.insert nv e nm)
    bind _ (q, a) =
      Left $ "Type " ++ aName al ++ ": parameter '" ++ pName q
           ++ "' was given the wrong kind of argument ("
           ++ (case a of AWidth e -> "width " ++ show e
                         AStack st -> "stack " ++ show st) ++ ")"

substStackVars :: Map SVar SType -> Ty -> Ty
substStackVars m = substParams M.empty m M.empty

substParams :: Map TVar Ty -> Map SVar SType -> Map NVar Exp -> Ty -> Ty
substParams tmap m nmap = goT
  where
    goT t@(TVarTy v) = M.findWithDefault t v tmap
    goT TInt         = TInt
    goT TStr         = TStr
    goT TSym         = TSym
    goT (TFn (Arrow i o _)) = TFn (arrPure (goS i) (goS o))  -- substitute inside Fn
    goT (TSum r)     = TSum (goR r)
    goT (TData n as) = TData n (map goS as)
    goT (TFin e)     = TFin (goE e)
    goR RNil         = RNil
    goR t@(RTail _)  = t
    goR (RCons s r)  = RCons (goS s) (goR r)
    goS SEnd            = SEnd
    goS t@(STail v)     = M.findWithDefault t v m
    goS (SCons t s)     = SCons (goT t) (goS s)
    -- `sexp`, not `SExp`: grounding a width to a literal must expand
    -- into copies, or the canonical form is broken (the substOnce
    -- lesson).  This clause was MISSING — a latent pattern-match
    -- failure that width parameters make immediately reachable.
    goS (SExp b e r)    = sexp (goS b) (goE e) (goS r)
    goE e@(Exp k mv) = case mv of
      Just n | Just (Exp k' mv') <- M.lookup n nmap -> Exp (k + k') mv'
      _ -> e

-- One-way match of an alias body against a concrete element type.
-- Parameters bind single element types (nonlinear occurrences must
-- agree); closed rows/stacks only match same-shape closed structure.
matchAlias :: Alias -> Ty -> Maybe [TyArg]
matchAlias al t = do
  (sb, nb) <- goT (aBody al) t (M.empty, M.empty)
  mapM (lookupArg sb nb) (aParams al)
  where
    lookupArg _  nb (PWidth nv) = AWidth <$> M.lookup nv nb
    lookupArg sb _  q           = AStack <$> M.lookup (SV (pName q)) sb
    -- both kinds bind through the same map, keyed by the parameter's
    -- name; a wire parameter's binding is its one-wire stack
    pVar q = SV (pName q)
    goT (TVarTy v) x m
      | TV (show v) `elem` [ tv | PWire tv <- aParams al ] =
          bindS (SV (show v)) (SCons x SEnd) m
    goT TInt TInt m = Just m
    goT TStr TStr m = Just m
    goT TSym TSym m = Just m
    goT (TSum rb) (TSum rx) m = goR rb rx m
    goT (TData nb bs) (TData nx xs) m
      | nb == nx && length bs == length xs =
          foldM (\acc (b, x) -> goS b x acc) m (zip bs xs)
    goT (TFn (Arrow ib ob _)) (TFn (Arrow ix ox _)) m =
      goS ib ix m >>= goS ob ox
    goT (TFin eb) (TFin ex) m = bindE eb ex m
    goT _ _ _ = Nothing
    goR RNil RNil m = Just m
    goR (RCons sb rb) (RCons sx rx) m = goS sb sx m >>= goR rb rx
    goR _ _ _ = Nothing
    bindS p x (sb, nb)
      | openTailedS x = Nothing
      | otherwise =
          case M.lookup p sb of
            Nothing -> Just (M.insert p x sb, nb)
            Just y  -> if x == y then Just (sb, nb) else Nothing
    -- a width parameter binds against the concrete exponent
    bindE (Exp 0 (Just nv)) ex (sb, nb)
      | nv `elem` [ v | PWidth v <- aParams al ] =
          case M.lookup nv nb of
            Nothing -> Just (sb, M.insert nv ex nb)
            Just y  -> if y == ex then Just (sb, nb) else Nothing
    bindE eb ex m = if eb == ex then Just m else Nothing
    goS (STail p) x m
      | p `elem` map pVar (aParams al) = bindS p x m
    goS SEnd SEnd m = Just m
    goS (SCons tb sb) (SCons tx sx) m = goT tb tx m >>= goS sb sx
    -- exponents: same-shape bases, then the width, then the rest.
    -- (Missing before, so any alias with an exponent silently never
    -- folded for display.)
    goS (SExp bb eb rb) (SExp bx ex rx) m
      | closedArity bb == closedArity bx =
          goS bb bx m >>= bindE eb ex >>= goS rb rx
    goS _ _ _ = Nothing

-- Folded display: try to rewrite structure back into declared names.
-- Fewest parameters wins; ties go to the earliest alias in the list
-- (callers order user-latest-first, then prelude).
bestAlias :: [Alias] -> Ty -> Maybe (Alias, [TyArg])
bestAlias aliases t =
  case [ (al, args) | al <- aliases, Just args <- [matchAlias al t] ] of
    [] -> Nothing
    cs -> Just (minimumOn (length . aParams . fst) cs)
  where
    minimumOn f (x : xs) = go x xs
      where go best []       = best
            go best (y : ys) = go (if f y < f best then y else best) ys
    minimumOn _ [] = error "bestAlias: impossible"

-- What the type printer folds names back on: structural aliases, and
-- the nominal resource names — which fold onto the arrow rather than
-- onto a wire, so they cannot ride in the alias list.
data Disp = Disp { dispAliases :: [Alias], dispResources :: [String] }

noDisp :: Disp
noDisp = Disp [] []

aliasDisp :: [Alias] -> Disp
aliasDisp as = Disp as []

showTyA :: Disp -> Ty -> String
showTyA as t =
  case bestAlias (dispAliases as) t of
    Just (al, args)
      | null args -> aName al
      | otherwise ->
          aName al ++ "(" ++ intercalate ", " (map (showArgA as) args) ++ ")"
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
      TFin e    -> "Fin(" ++ show e ++ ")"

showArgA :: Disp -> TyArg -> String
showArgA as (AStack st) = showStackA as st
showArgA _  (AWidth e)  = show e

showRowA :: Disp -> SumRow -> String
showRowA as row = intercalate " | " (go row)
  where
    go RNil            = []
    go (RTail v)       = [show v]
    go (RCons st rest) = showStackA as st : go rest

showStackA :: Disp -> SType -> String
showStackA _  SEnd        = "•"
showStackA _  (STail v)   = show v
showStackA as st          = unwords (go st)
  where
    go SEnd             = []
    go (STail v)        = [show v]
    go (SCons t rest)   = showTyA as t : go rest
    go (SExp b e rest)  = showExpAt b e : go rest

-- A closed stack as its wires, deepest first; Nothing if open.
closedWires :: SType -> Maybe [Ty]
closedWires SEnd        = Just []
closedWires (SCons t r) = (t :) <$> closedWires r
closedWires _           = Nothing

-- The LEADING run of resource wires, and the working wires above them.
-- Resources ride deepest (the 2026-08-26 flip), which is what puts every
-- offset a known distance from the bottom — the property that lets the
-- elaborator route them without consulting inference.
resPrefix :: [String] -> [Ty] -> ([String], [Ty])
resPrefix rs ts =
  let isRes (TData n []) = n `elem` rs
      isRes _            = False
      (res, rest)        = span isRes ts
  in ([ n | TData n [] <- res ], rest)

-- `A =IO Log GameState> B` — the note's spelling.  The grade and the
-- threaded resources are the same thing said two ways (the set of
-- resource wires the def touches), so one arrow carries both; with no
-- resources it degrades to the plain glyph.
arrowBetween :: EffRow -> [String] -> String
arrowBetween e [] = arrowGlyph e
arrowBetween e ns = " =" ++ unwords ([ "IO" | eIO e ] ++ ns) ++ "> "

showArrowA :: Disp -> Arrow -> String
showArrowA as (Arrow s1 s2 e)
  -- a resource PREFIX shared by both sides is what "threaded through"
  -- means, so that is exactly when the name is earned.  Works on open
  -- stacks: the resources are at the bottom, the tail is far away.
  | r1 <- leadingRes (dispResources as) s1
  , r2 <- leadingRes (dispResources as) s2
  , not (null r1), r1 == r2
  = showStackA as (dropWires (length r1) s1)
      ++ arrowBetween e r1
      ++ showStackA as (dropWires (length r1) s2)
showArrowA as (Arrow s1 s2 e) =
  showStackA as s1 ++ arrowGlyph e ++ showStackA as s2

dropWires :: Int -> SType -> SType
dropWires 0 st            = st
dropWires n (SCons _ rest) = dropWires (n - 1) rest
dropWires _ st            = st

showSchemeA :: Disp -> Scheme -> String
showSchemeA as (Forall tvars svars rvars nvars evars arr) =
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

-- Inference: given an Env and a Term, produce an arrPure and constraints
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
        [ () | (Arrow i o _, ix) <- zip arrows0 [0 :: Int ..]
             , ix /= n - 1
             , openTailedS i || openTailedS o ]
      (arrows, cs) =
        if null openNonFinal
          then (arrows0, cs0)
          else ( [ if ix == n - 1 || not (openTailedS i || openTailedS o)
                     then a else arrPure SEnd SEnd
                 | (a@(Arrow i o _), ix) <- zip arrows0 [0 :: Int ..] ]
               , CFail ("A recursive call (or other open-arity atom) must \
                        \be the final atom of its tensor stage") : cs0 )
      inS    = foldr1 appendStack [ i | Arrow i _ _ <- arrows ]
      outS   = foldr1 appendStack [ o | Arrow _ o _ <- arrows ]
      -- One stage, one grade: every atom's row unifies with the
      -- stage's.  A pure atom's row is open (see openEff), so it simply
      -- absorbs whatever the effectful one carries.
      grades = [ g | Arrow _ _ g <- arrows ]
      stageG = head grades
      gcs    = [ CEqEff stageG g | g <- drop 1 grades ]
  -- PLACEMENT: several effectful atoms in one stage are LEGAL, and
  -- they run left to right — deepest wire first, the order the atoms
  -- are already written in.  design-effects.md offers this as the
  -- alternative to forbidding (its "left-to-right decree", which the
  -- evaluator has always implemented), and the argument for taking it
  -- here is that Braid's tensor is not the abstract bifunctorial ⊗ in
  -- the first place: atoms are positionally aligned to wires, so the
  -- text already fixes the order that the premonoidal obstruction says
  -- is missing.  `print print print` keeps working.
  --
  -- Reversibility runs the other way now (a decree can be relaxed
  -- further but not tightened without breaking programs), so the
  -- ladder's step 2/3 licences — reordering, parallelising, fusing —
  -- are what future grades must earn, not legality itself.
  pure (Arrow inS outS stageG, cs ++ gcs)

infer env (Seq t u) = do
  (Arrow i1 o1 e1, c1) <- infer env t
  (Arrow i2 o2 e2, c2) <- infer env u
  let c = CEqStack o1 i2
  -- Grades unify rather than join: the absorption case of unifyEff is
  -- what makes `1 >> print` come out io while `1 >> 2` stays pure.
  pure (Arrow i1 o2 e1, c1 ++ c2 ++ [c, CEqEff e1 e2])

-- Infer one operand of a tensor chain.  Only the final operand may keep
-- its remainder variable open; all earlier operands are closed (ρ := •).
inferOperand :: Env -> Bool -> Term -> Infer (Arrow, [Constraint])
inferOperand env final (Prim name)
  | isIntLiteral name = pick intLitScheme
  | isStrLiteral name =
      pick (Forall [] [] [] [] [] (arrPure SEnd (SCons TStr SEnd)))
  | isSymLiteral name =
      pick (Forall [] [] [] [] [] (arrPure SEnd (SCons TSym SEnd)))
  | Just n <- injIndex name, not (M.member name env) = pick (injScheme n)
  | Just k <- finIndex name, not (M.member name env) = pick (finScheme k)

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
  -- The effect lives INSIDE the Fn: pushing an io action is pure, and
  -- `apply` is where the grade transfers back out.  The outer row is
  -- open (openEff) so a quote may share a stage with an effectful atom.
  q <- openEff (arrPure SEnd (SCons (TFn arrP) SEnd))
  pure (q, cs)
inferOperand env _ (Alts comps residual) = do
  -- Code row (p₁ | … | pₙ [| ...]): the sum functor action.  A one-wire
  -- atom (Δ-in-sum ⇒ Δ-out-sum); component i maps alternative i,
  -- re-tagging into the same position.  The residual `| ...` shares one
  -- row variable between input and output: identity on the rest.
  results <- mapM (infer env) comps
  end <- if residual then RTail <$> freshRVarName else pure RNil
  let arrows = map fst results
      cs     = concatMap snd results
      inRow  = foldr RCons end [ i | Arrow i _ _ <- arrows ]
      outRow = foldr RCons end [ o | Arrow _ o _ <- arrows ]
      grades = [ g | Arrow _ _ g <- arrows ]
  -- exactly one arm runs, but either might, so the row carries the
  -- arms' common grade: an io branch grades the whole row
  rowG <- case grades of
            (g : _) -> pure g
            []      -> pure effPure
  let gcs = [ CEqEff rowG g | g <- drop 1 grades ]
  r <- openEff (Arrow (SCons (TSum inRow) SEnd)
                      (SCons (TSum outRow) SEnd) rowG)
  pure (r, cs ++ gcs)
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
  let paramScheme av = Forall [] [] [] [] [] (arrPure SEnd (SCons (TVarTy av) SEnd))
      env' = foldr (\(p, av) -> M.insert p (paramScheme av)) env
                   [ (n, av) | (Just n, av) <- zip slots stys ]
  (Arrow bi bo bg, cs) <- infer env' body
  restS <- if hasRest then STail <$> freshSVarName else pure SEnd
  let bodyIn = foldr (SCons . TVarTy) restS
                     [ av | (Nothing, av) <- zip slots stys ]
      inS    = foldr (SCons . TVarTy) restS stys
  pure (Arrow inS bo bg, CEqStack bi bodyIn : cs)
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
          pure (arrPure SEnd SEnd, cs)
        Right s ->
          let arr'@(Arrow i o _) = apply s arr
              tails = nub ([ v | Just v <- [tailVar i] ]
                        ++ [ v | Just v <- [tailVar o] ])
              sm = M.fromList [ (v, SEnd) | v <- tails ]
          in pure (substOnce (Subst M.empty sm M.empty M.empty M.empty) arr', cs)

-- The open stack variables of a stack: the tail, plus any splices.
openVarsS :: SType -> [SVar]
openVarsS (STail v)      = [v]
openVarsS (SCons _ r)    = openVarsS r
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

-- finK: the index literal family.  `finK : • ⇒ Fin(k+1+n)` — the
-- offset IS the proof that k is in range, so `at` needs no runtime
-- check, and `weaken` keeps it true as the bound grows.  A STATIC
-- witness, in the design-indices.md sense.
finIndex :: String -> Maybe Int
finIndex ('f':'i':'n':ds)
  | not (null ds), all isDigit ds = Just (read ds)
finIndex _ = Nothing

finScheme :: Int -> Scheme
finScheme k =
  Forall [] [] [] [NV "n"] []
    (arrPure SEnd (SCons (TFin (Exp (k + 1) (Just (NV "n")))) SEnd))

-- inN : ∀ Δ₁…Δₙ σ. Δₙ ⇒ (Δ₁ | … | Δₙ | σ) — bundle the whole input
-- segment, tagged at position N; other alternatives are placeholders.
injScheme :: Int -> Scheme
injScheme n =
  let d   = SV "Δ"
      ps  = [ SV ("Δ" ++ show i) | i <- [1 .. n - 1] ]
      rv  = RV "σ"
      row = foldr (RCons . STail) (RCons (STail d) (RTail rv)) ps
  in Forall [] (ps ++ [d]) [rv] [] []
       (arrPure (STail d) (SCons (TSum row) SEnd))

-- Integer literals are terminal-source: • ⇒ Int.  Constants have NO
-- implicit remainder — pushing onto a nonempty stack requires explicit
-- `...` (e.g. `1 ...` : ρ ⇒ Int ρ).  See spec-update-exponentials.md.
intLitScheme :: Scheme
intLitScheme = Forall [] [] [] [] [] (arrPure SEnd (SCons TInt SEnd))

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
      c   = TV "C"
      ta  = TVarTy a
      tb  = TVarTy b
      tc  = TVarTy c
      gam = SV "Γ"
      del = SV "Δ"
      one t = SCons t SEnd
      -- ε: the grade a higher-order word passes THROUGH.  The inner
      -- Fn's row and the outer arrow's row are the same variable, so
      -- running a pure quote is pure and running an io one is io — one
      -- prim, both readings (design-effects.md's shared variable sort).
      epsV = EV "ε"
      epsR = Eff False (Just epsV)
      arrEps i o = Arrow i o epsR
      fnGD = TFn (arrEps (STail gam) (STail del))
      applyTy = Forall [] [gam, del] [] [] [epsV]
        (arrEps (SCons fnGD (STail gam)) (STail del))
      -- merge : (Θ | Θ) ⇒ Θ — the binary codiagonal ∇
      mergeTy = Forall [] [SV "Θ"] [] [] []
        (arrPure (SCons (TSum (RCons (STail (SV "Θ"))
                       (RCons (STail (SV "Θ")) RNil))) SEnd)
               (STail (SV "Θ")))
      -- there : (σ) ⇒ (Δ | σ) — widen a sum with a new front track
      -- (tags shift by one; here ≡ in1, inN ≡ here >> there^(n-1))
      thereTy = Forall [] [SV "Δ"] [RV "σ"] [] []
        (arrPure (SCons (TSum (RTail (RV "σ"))) SEnd)
               (SCons (TSum (RCons (STail (SV "Δ")) (RTail (RV "σ")))) SEnd))
      -- loop : Fn⟨Σ ⇒ (Σ | Θ)⟩ Σ ⇒ Θ — Elgot iteration: the body routes
      -- to continue (re-enter) or done (exit)
      loopTy =
        let sg = SV "Σ"; th = SV "Θ"
            body = TFn (arrEps (STail sg)
                     (one (TSum (RCons (STail sg)
                           (RCons (STail th) RNil)))))
        in Forall [] [sg, th] [] [] [epsV]
             (arrEps (SCons body (STail sg)) (STail th))
      int2 = SCons TInt (one TInt)
      codeStructTy =
        TData "List"
          [SCons (TData "List" [SCons (TData "Atom" []) SEnd]) SEnd]
      int2Router = Forall [] [] [] [] []
        (arrPure int2
               (one (TSum (RCons int2 (RCons int2 RNil)))))
      eqTy = Forall [a] [] [] [] []
        (let aa = SCons ta (one ta)
         in arrPure aa (one (TSum (RCons aa (RCons aa RNil)))))
      binIntTy = Forall [] [] [] [] []
        (arrPure (SCons TInt (one TInt)) (one TInt))
      -- Bool ≡ (• | •): two payload-free tracks; true = in1, false = in2
      tBool    = TSum (RCons SEnd (RCons SEnd RNil))
      boolLit  = Forall [] [] [] [] [] (arrPure SEnd (one tBool))
      -- foldExp: the eliminator of an exponent bundle aⁿ (the stack-level
      -- foldList).  n is erased; at runtime the bundle is the final
      -- segment and its width is the witness.
      nExp = Exp 0 (Just (NV "n"))
      foldExpTy =
        let stepArr = arrPure (SCons tb (one ta)) (one tb)
        in Forall [a, b] [] [] [NV "n"] []
             (arrPure (SCons (TFn stepArr)
                      (SCons tb (SExp (one ta) nExp SEnd)))
                    (one tb))
      -- foldExp2: the two-wide twin — eliminate a bundle of PAIRS
      -- (a c)ⁿ; the step sees [acc, a, c]
      foldExp2Ty =
        let c  = TV "c"
            tc = TVarTy c
            stepArr = arrPure (SCons tb (SCons ta (one tc))) (one tb)
        in Forall [a, b, c] [] [] [NV "n"] []
             (arrPure (SCons (TFn stepArr)
                      (SCons tb (SExp (SCons ta (one tc)) nExp SEnd)))
                    (one tb))
      -- GLA generators, width-polymorphic in n (design-exponents.md)
      dupNTy = Forall [a] [] [] [NV "n"] []
        (arrPure (SExp (one ta) nExp SEnd)
               (SExp (one ta) nExp (SExp (one ta) nExp SEnd)))
      zipNTy = Forall [a, b] [] [] [NV "n"] []
        (arrPure (SExp (one ta) nExp (SExp (one tb) nExp SEnd))
               (SExp (SCons ta (one tb)) nExp SEnd))
      -- map a one-wire function across a bundle: the tier's missing
      -- container-preserving word (folds collapse, this one rebuilds)
      mapNTy = Forall [a, b] [] [] [NV "n"] [epsV]
        (arrEps (SCons (TFn (arrEps (one ta) (one tb)))
                      (SExp (one ta) nExp SEnd))
               (SExp (one tb) nExp SEnd))
      -- the pair twin, mirroring foldExp/foldExp2.  With zipN this
      -- lifts ANY two-wire word pointwise, so addN and the rest stop
      -- needing to be primitive.
      mapN2Ty = Forall [a, b, c] [] [] [NV "n"] [epsV]
        (arrEps (SCons (TFn (arrEps (SCons ta (one tb)) (one tc)))
                      (SExp (SCons ta (one tb)) nExp SEnd))
               (SExp (one tc) nExp SEnd))
      -- zipN's inverse: de-interleave a pair bundle into two bundles
      -- INDICES (design-indices.md).  Every introduction's n is forced
      -- by a relevant input: `indicesN` and `checkedAt` read a live
      -- bundle, and the finK literals carry their bound as an offset.
      -- There is deliberately no `tabulate`/`asFin`: an output-only n
      -- has no witness, exactly as for `zeroN`.
      atTy = Forall [a] [] [] [NV "n"] []
        (arrPure (SCons (TFin nExp) (SExp (one ta) nExp SEnd))
               (one ta))
      indicesNTy = Forall [a] [] [] [NV "n"] []
        (arrPure (SExp (one ta) nExp SEnd)
               (SExp (SCons (TFin nExp) (one ta)) nExp SEnd))
      -- the dynamic discharge: check an Int against the LIVE width;
      -- the hit track carries the index and the untouched bundle
      checkedAtTy = Forall [a] [] [] [NV "n"] []
        (arrPure (SCons TInt (SExp (one ta) nExp SEnd))
               (one (TSum (RCons (SCons (TFin nExp) (SExp (one ta) nExp SEnd))
                          (RCons (SCons TInt (SExp (one ta) nExp SEnd))
                                 RNil)))))
      weakenTy = Forall [] [] [] [NV "n"] []
        (arrPure (one (TFin nExp)) (one (TFin (Exp 1 (Just (NV "n"))))))
      finIntTy = Forall [] [] [] [NV "n"] []
        (arrPure (one (TFin nExp)) (one TInt))
      unzipNTy = Forall [a, b] [] [] [NV "n"] []
        (arrPure (SExp (SCons ta (one tb)) nExp SEnd)
               (SExp (one ta) nExp (SExp (one tb) nExp SEnd)))
  in M.fromList
       [ ("id",    Forall [a]    [] [] [] [] (arrPure (one ta) (one ta)))
       , ("_",     Forall [a]    [] [] [] [] (arrPure (one ta) (one ta)))  -- hole: id
       , ("swap",  Forall [a, b] [] [] [] []
           (arrPure (SCons ta (one tb)) (SCons tb (one ta))))
       , ("dup",   Forall [a]    [] [] [] [] (arrPure (one ta) (SCons ta (one ta))))
       , ("drop",  Forall [a]    [] [] [] [] (arrPure (one ta) SEnd))
       , ("pass",  Forall []     [rho] [] [] [] (arrPure (STail rho) (STail rho)))
         -- the terminal morphism: forget the whole segment
       , ("forget", Forall []    [rho] [] [] [] (arrPure (STail rho) SEnd))
       , ("+",     binIntTy)
       , ("*",     binIntTy)
       , ("print", Forall [a]    [] [] [] [] (arrIO (one ta) SEnd))
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
       , ("cat",       Forall [] [] [] [] []
           (arrPure (SCons TStr (one TStr)) (one TStr)))
       , ("toStr",     Forall [a] [] [] [] [] (arrPure (one ta) (one TStr)))
       , ("asInt?",    Forall [] [] [] [] []
           (arrPure (one TStr)
                  (one (TSum (RCons (one TInt)
                        (RCons (one TStr) RNil))))))
       , ("symStr",    Forall [] [] [] [] [] (arrPure (one TSym) (one TStr)))
       , ("unparse",   Forall [] [] [] [] []
           (arrPure (SCons codeStructTy SEnd) (one TStr)))
       , ("parse",     Forall [] [] [] [] []
           (arrPure (one TStr)
                  (one (TSum (RCons (one codeStructTy)
                        (RCons (one TStr) RNil))))))
       , ("readLine",  Forall [] [] [] [] []
           (arrIO SEnd
                  (one (TSum (RCons (one TStr)
                        (RCons (one TStr) RNil))))))
       , ("readFile",  Forall [] [] [] [] []
           (arrIO (one TStr)
                  (one (TSum (RCons (one TStr) (RCons (one TStr) RNil))))))
       , ("writeFile", Forall [] [] [] [] []
           (arrIO (SCons TStr (one TStr))
                  (one (TSum (RCons SEnd (RCons (one TStr) RNil))))))
       , ("evalCode",  Forall [] [gam, del] [] [] []
           (arrIO (SCons codeStructTy (STail gam))
                  (one (TSum (RCons (STail del)
                        (RCons (SCons TStr (STail gam)) RNil))))))
       , ("reflect",   Forall [] [gam, del] [] [] [epsV]
           (arrPure (one (TFn (arrEps (STail gam) (STail del))))
                  (one (TSum (RCons (one codeStructTy)
                        (RCons (one TStr) RNil))))))
       , ("apply",     applyTy)
       , ("there",     thereTy)
       , ("merge",     mergeTy)
       , ("loop",      loopTy)
       , ("foldExp",   foldExpTy)
       , ("foldExp2",  foldExp2Ty)
       , ("at",        atTy)
       , ("indicesN",  indicesNTy)
       , ("checkedAt", checkedAtTy)
       , ("weaken",    weakenTy)
       , ("finInt",    finIntTy)
       , ("mapN",      mapNTy)
       , ("mapN2",     mapN2Ty)
       , ("unzipN",    unzipNTy)
       , ("dupN",      dupNTy)
       , ("zipN",      zipNTy)
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
primsIn (Use _ b)      = primsIn b

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
    go (Use rs b)       = Use rs (go b)
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
               , Nothing <- [injIndex n]
               , Nothing <- [finIndex n] ] of
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
                   , Nothing <- [injIndex n]
                   , Nothing <- [finIndex n] ] of
        (n : _) -> Left $ "Unknown primitive: " ++ n
        [] -> do
          let (arr, cs) = runInfer0 $ do
                fi <- freshSVarName
                fo <- freshSVarName
                let mono = Forall [] [] [] [] []
                             (arrPure (STail fi) (STail fo))
                (a@(Arrow bi bo _), cs') <-
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
  let (tvs, svs, rvs, nvs, evs) = varsOfArrow arr
      tm = M.fromList
             (zip tvs [ TVarTy (TV ("a" ++ show n)) | n <- [0 :: Int ..] ])
      sm = M.fromList
             (zip svs [ STail (SV ("ρ" ++ show n)) | n <- [0 :: Int ..] ])
      rm = M.fromList
             (zip rvs [ RTail (RV ("σ" ++ show n)) | n <- [0 :: Int ..] ])
      nm = M.fromList
             (zip nvs [ Exp 0 (Just (NV ("n" ++ show n))) | n <- [0 :: Int ..] ])
      -- effect tails are invisible in display, but normalizing them
      -- keeps `:t!` deterministic
      em = M.fromList
             (zip evs [ Eff False (Just (EV ("ε" ++ show n)))
                      | n <- [0 :: Int ..] ])
  in substOnce (Subst tm sm rm nm em) arr

--------------------------------------------------------------------------------
-- 9.5 The ambient elaborator (`use`)
--
-- Resources ride DEEPEST, in `use` order, so every offset here is a
-- constant known from the header alone.  That is the whole reason this
-- can be syntactic: it never consults inference, so inference stays the
-- CHECKER of what we emit rather than an input to it, and a type error
-- is reported against the user's program rather than from inside a
-- rewrite they never wrote (design-effects.md).
--------------------------------------------------------------------------------

-- the leading run of resource wires on a stack (works on open stacks
-- too, unlike closedWires — a resource op's tail is often open)
leadingRes :: [String] -> SType -> [String]
leadingRes rs (SCons (TData n []) r) | n `elem` rs = n : leadingRes rs r
leadingRes _  _                                    = []

elabUse :: Env -> Term -> Either String Term
elabUse env = elabUseWith env []

-- `use` names RESOURCES (wires to thread) and INSTANCES (slots to
-- resolve).  Both are scoped selection with no inference and no
-- dispatch: an instance's operations are renamed to that instance's
-- defs, once, for the rest of the scope.
elabUseWith :: Env -> [(String, [String])] -> Term -> Either String Term
elabUseWith env instSlots = go
  where
    go (Use ns b) = do
      b' <- go b
      let (is, rs) = partitionEithers
                       [ maybe (Right n) (Left . (,) n) (lookup n instSlots)
                       | n <- ns ]
          b'' = foldr (\(i, sl) t -> renameSlotsT i sl t) b' is
      case rs of
        [] -> pure b''
        _  -> elabScope env rs b''
    go (Seq a b)       = Seq <$> go a <*> go b
    go (Tensor ts)     = Tensor <$> mapM go ts
    go (Quote t)       = Quote <$> go t
    go (Alts cs r)     = Alts <$> mapM go cs <*> pure r
    go (OpenAbs sl h b) = OpenAbs sl h <$> go b
    go t               = Right t

-- the Term-level twin of renameSlots: within a `use Inst` scope every
-- occurrence of one of the theory's operations means THIS instance's
partitionEithers :: [Either a b] -> ([a], [b])
partitionEithers xs = ([ a | Left a <- xs ], [ b | Right b <- xs ])

renameSlotsT :: String -> [String] -> Term -> Term
renameSlotsT inst slots = go
  where
    go (Prim n) | n `elem` slots = Prim (slotDefName inst n)
    go (Seq a b)        = Seq (go a) (go b)
    go (Tensor ts)      = Tensor (map go ts)
    go (Quote t)        = Quote (go t)
    go (Alts cs r)      = Alts (map go cs) r
    go (Use ns b)       = Use ns (go b)
    go (OpenAbs sl h b) = OpenAbs sl h (go b)
    go t                = t

elabScope :: Env -> [String] -> Term -> Either String Term
elabScope env rs body = do
  stages <- mapM routeStage (spineOf body)
  -- `use Log Counter` is a CLAIM about the incoming wires, so make it
  -- one: `unLog >> Log` is the identity on a Log and typechecks on
  -- nothing else.  Without this a body that never touches a resource
  -- would leave its wires unconstrained, and the scope would be padding
  -- rather than a statement.
  let assert = [ [ Seq (Prim ("un" ++ r)) (Prim r) | r <- rs ]
                 ++ [Prim "pass"] | not (null rs) ]
  pure (chainTerm (assert ++ concat stages))
  where
    k = length rs
    pad n = replicate n (Prim "_")
    swapStage d = pad d ++ [Prim "swap", Prim "pass"]

    schemeOf (Prim n) = M.lookup n env
    schemeOf _        = Nothing

    resUse a = case schemeOf a of
      Just (Forall _ _ _ _ _ (Arrow i _ _)) -> leadingRes rs i
      _                                     -> []

    -- an open-arity word must stay final, so it takes the remainder
    -- itself instead of us appending one (§13 rule 1)
    isOpen a = case schemeOf a of
      Just (Forall _ _ _ _ _ (Arrow i o _)) -> openTailedS i || openTailedS o
      _                                     -> False

    routeStage atoms0 =
      let atoms = [ a | a <- atoms0, a /= Prim "pass" ]
          tailPass = [ Prim "pass" | not (null atoms), not (isOpen (last atoms)) ]
          touching = [ (a, u) | a <- atoms, let u = resUse a, not (null u) ]
      in case touching of
        -- a pure stage: step over the resources, act, thread the rest
        [] -> Right [ pad k ++ atoms ++ tailPass ]
        -- one resource operation, alone in its stage: bring its wire up
        -- beside the working wires, apply, put it back
        [(a, [r])] | [a] == atoms, Just j <- elemIndex r rs ->
          Right ( [ swapStage i | i <- [j .. k - 2] ]
               ++ [ pad (k - 1) ++ [a] ++ tailPass ]
               ++ [ swapStage i | i <- reverse [j .. k - 2] ] )
        [(a, u)] | [a] == atoms ->
          Left $ "`use`: " ++ renderTerm a ++ " touches "
              ++ show (length u) ++ " resources at once; the elaborator \
                 \routes one per stage"
        _ -> Left $ "`use`: a stage may contain at most one resource \
                    \operation, and it must be alone — put "
                 ++ renderTerm (fst (head touching)) ++ " on its own line"

-- A law is a program that must be runnable on nothing and answer yes:
-- `• ⇒ Bool`.  Checked here so a malformed law is a declaration error
-- rather than a mystery at module start.
checkLawType :: Env -> String -> Either String ()
checkLawType env n = do
  sc <- maybe (Left $ "internal: missing law def " ++ n) Right (M.lookup n env)
  let Arrow i o _ = runInfer0 (instantiate sc)
      boolTy = TSum (RCons SEnd (RCons SEnd RNil))
  case solve [CEqStack i SEnd, CEqStack o (SCons boolTy SEnd)] of
    Right _ -> Right ()
    Left _  ->
      let (inst, lw) = maybe ("?", n) id (lawParts n)
      in Left $ "law '" ++ lw ++ "' of " ++ inst ++ " must be a program "
             ++ "with type `• ⇒ Bool`, but is "
             ++ show (normalizeArrow (runInfer0 (instantiate sc)))

-- An instance becomes ordinary defs: one per slot, one per law.  The
-- slot bodies are the user's programs with the instance's own slots in
-- scope (so a law may call `op` and mean this instance's `op`), which
-- is the same renaming `use` performs — resolution once, not per call.
instanceDefs :: [Theory] -> Instance
             -> Either String [(String, String, Maybe String)]
instanceDefs theories inst = do
  th <- theoryOf theories (inTheory inst)
  let slotNames = map fst (thSlots th)
      given     = map fst (inBindings inst)
  case [ n | n <- slotNames, n `notElem` given ] of
    (n : _) -> Left $ "instance " ++ inName inst ++ ": no binding for '"
                   ++ n ++ "' (declared by theory " ++ thName th ++ ")"
    [] -> Right ()
  case [ n | n <- given, n `notElem` slotNames ] of
    (n : _) -> Left $ "instance " ++ inName inst ++ ": '" ++ n
                   ++ "' is not an operation of theory " ++ thName th
    [] -> Right ()
  -- Each generated def is wrapped in its OWN instance's scope, so the
  -- Term-level renaming does the work.  Renaming the source text
  -- instead would have to re-implement tokenization — `op)` is not the
  -- word `op` — and would get it subtly wrong.
  let rename body = "use " ++ inName inst ++ " ; " ++ body
      slots  = [ ( slotDefName (inName inst) n, rename body
                 , Just ("slot '" ++ n ++ "' of " ++ inName inst) )
               | (n, body) <- inBindings inst ]
      laws   = [ ( lawDefName (inName inst) nm, rename body
                 , Just ("law '" ++ nm ++ "' of " ++ inName inst
                         ++ " — runs at module start") )
               | (nm, body) <- thLaws th ]
  pure (slots ++ laws)

theoryOf :: [Theory] -> String -> Either String Theory
theoryOf ths n = case [ t | t <- ths, thName t == n ] of
  (t : _) -> Right t
  []      -> Left $ "Unknown theory: " ++ n

-- Every slot's inferred type must match what the theory declared, read
-- at this instance's arguments.  This is the half of "audited model"
-- that does not need to run.
checkInstance :: Env -> [Theory] -> Instance -> Either String ()
checkInstance env theories inst = do
  th <- theoryOf theories (inTheory inst)
  if length (inArgs inst) /= length (thParams th)
    then Left $ "instance " ++ inName inst ++ ": theory " ++ thName th
             ++ " expects " ++ show (length (thParams th)) ++ " argument(s)"
    else Right ()
  mapM_ (one th) (thSlots th)
  where
    one th (nm, declared) = do
      let dn = slotDefName (inName inst) nm
      sc <- maybe (Left $ "instance " ++ inName inst ++ ": missing " ++ dn)
                  Right (M.lookup dn env)
      wanted <- substArrow th (inArgs inst) declared
      let got = runInfer0 (instantiate sc)
      case solve [ CEqStack (arrIn got) (arrIn wanted)
                 , CEqStack (arrOut got) (arrOut wanted) ] of
        Right _ -> Right ()
        Left _  -> Left $ "instance " ++ inName inst ++ ": slot '" ++ nm
                       ++ "' is " ++ show (normalizeArrow got)
                       ++ " but theory " ++ thName th ++ " declares "
                       ++ show (normalizeArrow wanted)
    arrIn  (Arrow i _ _) = i
    arrOut (Arrow _ o _) = o
    substArrow th args (Arrow i o e) = do
      let bind (PWire tv, SCons t SEnd) = Right (Left (tv, t))
          bind (PStack sv, st)          = Right (Right (sv, st))
          bind (q, st) = Left $ "instance " ++ inName inst ++ ": parameter '"
                             ++ pName q ++ "' takes one wire, given " ++ show st
      bs <- mapM bind (zip (thParams th) args)
      let tm = M.fromList [ b | Left  b <- bs ]
          sm = M.fromList [ b | Right b <- bs ]
      pure (Arrow (substParamsS tm sm i) (substParamsS tm sm o) e)

-- substitute theory parameters through a stack
substParamsS :: Map TVar Ty -> Map SVar SType -> SType -> SType
substParamsS tm sm = go
  where
    go SEnd          = SEnd
    go t@(STail v)   = M.findWithDefault t v sm
    go (SCons t r)   = SCons (substParams tm sm M.empty t) (go r)
    go (SExp b e r)  = sexp (go b) e (go r)

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
freeVarsScheme (Forall tv sv rv nv ev arr) =
  let (ft, fs, fr, fn, fe) = freeVarsArrow arr
  in (ft \\ tv, fs \\ sv, fr \\ rv, fn \\ nv, fe \\ ev)

freeVarsEnv :: Env -> Vars
freeVarsEnv env =
  foldr (catVars . freeVarsScheme) noVars (M.elems env)

-- Generalize all free type, stack, row, and exponent variables not
-- fixed by the environment.
generalize :: Env -> Arrow -> Scheme
generalize env arr =
  let (ftv, fsv, frv, fnv, fev) = freeVarsArrow arr
      (etv, esv, erv, env', eev) = freeVarsEnv env
  in Forall (ftv \\ etv) (fsv \\ esv) (frv \\ erv) (fnv \\ env')
            (fev \\ eev) arr

-- A checked module: definitions in order, plus an optional main program.
data Module = Module
  { modEnv     :: Env
  , modDefs    :: [(String, Scheme, Term)]
  , modAliases :: [Alias]          -- match order: latest first
  , modDatas   :: [DataDecl]       -- recursive (nominal) declarations
  , modDocs    :: Map String String -- ## doc comments, by def/type name
  , modMain    :: Maybe (Term, Arrow)
  , modTheories  :: [Theory]
  , modInstances :: [Instance]
  }

-- Split source into `def name = body` lines, `type …` declaration
-- lines, and the main program (all remaining lines, in order, joined
-- by newline-sequencing).  A `## text` line is a doc comment: it binds
-- to the next def or type line (consecutive doc lines join); doc text
-- preceding a plain program line is dropped.
-- Returns (defs, type/data/resource lines, BLOCK declarations, main).
-- A block declaration is `theory`/`instance`: a header line plus the
-- indented lines under it, kept raw for the declaration parser.
splitDefs :: String
          -> Either String ( [(String, String, Maybe String)]
                           , [(String, Maybe String)]
                           , [(String, [String], Maybe String)]
                           , String )
splitDefs src = do
  (defs, tys, decls, progLines) <- go Nothing (lines src)
  pure (defs, tys, decls, intercalate "\n" progLines)
  where
    go _ [] = Right ([], [], [], [])
    go doc (l : rest)
      | Just d <- docLine l =
          go (Just (maybe d (\p -> p ++ " " ++ d) doc)) rest
      | (kw : _) <- words l, kw `elem` ["type", "data", "resource"] = do
          (ds, ts, bs, ps) <- go Nothing rest
          pure (ds, (l, doc) : ts, bs, ps)
      -- `theory` / `instance`: a header plus its indented block, raw
      | (kw : _) <- words l, kw `elem` ["theory", "instance"] = do
          let (block, rest') = spanBlock 0 rest
          if null block
            then Left $ "Empty " ++ kw ++ " body: " ++ l
            else do
              (ds, ts, bs, ps) <- go Nothing rest'
              pure (ds, ts, (l, block, doc) : bs, ps)
      | ("def" : _) <- words l = do
          (name, body) <- parseDefLine l
          -- a `#` comment on the `=` line is not code: treat a
          -- comment-only body as blank so the block-body form triggers
          if all isSpace (takeWhile (/= '#') body)
            then do
              -- block body: the following indented lines.  A blank line
              -- ends it — unless a bracket is still open, in which case
              -- the body is mid-atom and keeps going.
              let (block, rest') = spanBlock 0 rest
              if null block
                then Left $ "Empty definition body: " ++ name
                else do
                  (ds, ts, bs, ps) <- go Nothing rest'
                  pure ((name, intercalate "\n" block, doc) : ds, ts, bs, ps)
            else do
              -- inline body: it may leave a bracket open, in which case
              -- the following lines belong to it, not to the module
              let (cont, rest') = spanOpen l rest
              (ds, ts, bs, ps) <- go Nothing rest'
              pure ((name, intercalate "\n" (body : cont), doc) : ds, ts, bs, ps)
      | otherwise = do
          -- a program line may leave a bracket open; the lines that
          -- close it are part of it, so `def`/`type`/`##` inside an open
          -- bracket is code, not a declaration
          let (cont, rest') = spanOpen l rest
          (ds, ts, bs, ps) <- go Nothing rest'
          pure (ds, ts, bs, l : cont ++ ps)

    indented ln = not (all isSpace ln) && isSpace (head ln)

    -- an indented block body, continuing across blank/dedented lines
    -- while a bracket opened inside it is still unclosed
    spanBlock d (ln : ls)
      | d > 0 || indented ln =
          let (b, r) = spanBlock (d + lineDepth ln) ls in (ln : b, r)
    spanBlock _ ls = ([], ls)

    -- the lines AFTER `l` needed to close a bracket `l` left open
    spanOpen l = walk (lineDepth l) []
      where
        walk d acc ls
          | d <= 0    = (reverse acc, ls)
        walk _ acc [] = (reverse acc, [])
        walk d acc (x : xs) = walk (d + lineDepth x) (x : acc) xs

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
  (defSrcs, tyLines, declLines, mainSrc) <- splitDefs src
  (env1, _, _, ownAliases, ownDatas, docs0) <-
    foldM addType (env0, aliases0, datas0, [], [], M.empty) tyLines
  let sigs = map dataSig ownDatas
  -- theories first: an instance is checked against its theory, so the
  -- theory must already be known.  Both run before any def, which is
  -- what gives them file-wide scope.
  theories <- sequence [ parseTheory ownAliases sigs h b
                       | (h, b, _) <- declLines, take 6 h == "theory" ]
  insts    <- sequence [ parseInstance ownAliases sigs h b
                       | (h, b, _) <- declLines, take 8 h == "instance" ]
  instDefs <- concat <$> mapM (instanceDefs theories) insts
  slotTable <- sequence [ (,) (inName i) . map fst . thSlots
                            <$> theoryOf theories (inTheory i)
                        | i <- insts ]
  let genDefs =
        [ (fn, body, Just ("definition by points: one quoted case per "
                           ++ "constructor of " ++ dName dd
                           ++ ", recursive slots pre-folded"))
        | dd <- reverse ownDatas, Just (fn, body) <- [dataFoldSrc dd] ]
  (env', _, defsRev, docs) <-
    foldM (addDef slotTable) (env1, shadow0, [], docs0)
          (genDefs ++ instDefs ++ defSrcs)
  -- every slot's inferred type must match the theory's declaration,
  -- instantiated at this instance's arguments
  mapM_ (checkInstance env' theories) insts
  mapM_ (checkLawType env') [ n | (n, _, _) <- instDefs, isJust (lawParts n) ]
  mainPart <-
    if all isSpace mainSrc
      then pure Nothing
      else do
        term0 <- parseProgram mainSrc
        term  <- elabUseWith env' slotTable term0
        arr   <- inferTermIn env' term
        pure (Just (term, arr))
  -- own lists are built latest-first, which is exactly the match order
  pure (Module env' (reverse defsRev) ownAliases ownDatas docs mainPart
                theories insts)
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
    addDef slotTable (env, shadow, acc, docs) (name, bodySrc, doc) = do
      if M.member name env && name `notElem` shadow
        then Left $ "Duplicate definition: " ++ name
        else Right ()
      term0 <- either (Left . inDef) Right (parseProgram bodySrc)
      let env1 = M.delete name env   -- a shadowed def must not leak in
      -- `use` scopes are written out here, between parse and infer, the
      -- same slot substRecurse occupies: a syntactic Term rewrite with
      -- the Env available for arities and resource signatures.
      term1 <- either (Left . inDef) Right (elabUseWith env1 slotTable term0)
      let term = substRecurse name term1
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
  , "## an optional value, PAYLOAD FIRST: one element, or empty.  The order matters here in a way it does not in Haskell — in1 is the track `>=>` threads and `ok` builds, so a payload-second Maybe could not ride the railway at all."
  , "type Maybe(...) = (... | •)"
  , "## the list: initial algebra of (• | a X); foldList is generated"
  , "type List(a) = (• | a List(a))"
    -- a whole stack as ONE wire: what multi-wire aggregates become now
    -- that list cells hold a single wire
  , "data Box(...) = (...)"
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
  , "def pack2 = [(f x y -> [(l -> f ((x y >> Box) l >> cons) >> apply)])] [pass] ... >> foldExp2 >> _ nil >> apply"
  , "## top-first packs: head = TOP of the segment.  With a `...` ladder"
  , "## (each line pushes UNDER), list order = TEXT order — the vertical"
  , "## list idiom:   line1 / line2 ... / line3 ... / packR"
  , "def packR = [(l x -> x l >> cons)] nil ... >> foldExp"
  , "def pack2R = [(l x y -> (x y >> Box) l >> cons)] nil ... >> foldExp2"
  , "## first-match over a clause list: each clause is [router] [action];"
  , "## the first router that hits runs its action on x, else the default."
  , "## the always-hit router: the last lane of a guard clause list"
  , "def else? = in1"
  , "## probe a clause list (pack2 / pack2R lanes): run the first hit;"
  , "## in1(result) on a hit, in2(input) if none hit"
  , "def choose = (x clauses -> clauses >> [x >> in2] [(rest c -> c >> unBox >> (p f -> x >> p ... >> apply >> (f ... >> apply >> in1 | drop >> rest) >> merge))] ... >> foldList)"
  , "def matchWith = (x default clauses -> x clauses >> choose >> (pass | default ... >> apply) >> merge)"
  , "## commute List over the sum monad: all hits, or the first miss"
  , "def sequence = [nil >> ok] [(r x -> x >> ((y -> r >> (y ... >> cons | ...)) | miss) >> merge)] ... >> foldList"
  , "## keep the elements a quoted router hits"
  , "def filter = (p -> [p ... >> apply >> (single | drop >> nil) >> merge]) ... >> flatMap"
  , "## splice one level of right-nesting into the parent row — ANY"
  , "## inner arity (the row variable does the counting):"
  , "##   splice : (ρ0 | (σ0)) ⇒ (ρ0 | σ0)"
  , "def splice = (in1 | there) >> merge"
  , "## the ladder steps, a dual pair.  settle: the GUARD ladder — state"
  , "## (answered | working); each level routes the working track,"
  , "## answers the hit, and settle folds the agreeing answer in, so the"
  , "## state stays a 2-sum forever (one bar per level):"
  , "##   settle : (ρ0 | (ρ0 | ρ1)) ⇒ (ρ0 | ρ1)"
  , "def settle = assocL >> (merge |)"
  , "## settleR: the VALIDATION ladder — (working | errors); each check"
  , "## must pass to keep working, failures settle behind you:"
  , "##   settleR : ((ρ0 | ρ1) | ρ1) ⇒ (ρ0 | ρ1)"
  , "def settleR = assocR >> (| merge)"
  , "## a Bool selects one of two quotations"
  , "## flat coproduct eliminators: one quoted handler per track of a"
  , "## right-nested sum, all landing on a common result — to sums what"
  , "## foldList is to lists.  Sum on top, handlers below:"
  , "##   tag >> [h1] [h2] [h3] ... >> case3"
  , "def case2 = (f g s -> s >> (f ... >> apply | g ... >> apply) >> merge)"
  , "def case3 = (f g h s -> s >> (f ... >> apply | (g ... >> apply | h ... >> apply) >> merge) >> merge)"
  , "def case4 = (f g h i s -> s >> (f ... >> apply | (g ... >> apply | (h ... >> apply | i ... >> apply) >> merge) >> merge) >> merge)"
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
  , "def zip = (l r -> l >> unList >> (nil | (x xs -> r >> unList >> (nil | (y ys -> xs ys >> zip >> (x y >> Box) ... >> cons)) >> merge)) >> merge)"
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
  , "## run a program one wire deeper: `[f] >> lift` is f with one wire riding beneath it, untouched.  Compose it once per context wire.  This is tensorial STRENGTH — the action of (A ⊗ −) on a morphism — and it is what threads a resource past a pure stage, so it is an ordinary word rather than machinery."
  , "def lift = (f -> [_ (f ... >> apply)])"
  , "def sumN = [+] 0 ... >> foldExp"
    -- the GLA generators are now DERIVED: mapN/mapN2 lift any one- or
    -- two-wire word pointwise, so `+` and `*` are the only arithmetic
    -- the bundle tier needs to know about
  , "## pointwise add: the bundle monoid ∇, lifted from `+`"
  , "def addN = zipN >> [+] ... >> mapN2"
  , "## scale a bundle by a scalar, lifted from `*`"
  , "def scaleN = (k ... -> [k _ >> *] ... >> mapN)"
  , "## pointwise multiply (NOT linear — outside the GLA generators)"
  , "def mulN = zipN >> [*] ... >> mapN2"
  , "## pointwise subtract"
  , "def subN = zipN >> [-] ... >> mapN2"
  , "## guard lanes as a bare product: (Bool Fn)^n lanes, default Fn on"
  , "## top.  All conditions are pre-evaluated (probe every lane); the"
  , "## FIRST true lane's action runs, else the default — exactly one"
  , "## action ever runs (the fold selects quotes, applies once).  The"
  , "## accumulator is (decided | default): a true lane decides once;"
  , "## later lanes leave a decision alone."
  , "def firstTrue = (d -> d >> in2) ... >> [(acc b f -> acc >> (in1 | (g -> b [f >> in1] [g >> in2] >> cond)) >> merge)] ... >> foldExp2 >> merge >> apply"
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

-- Determinate wire count of a stack: Just n for a fully-closed stack,
-- Nothing when an open tail / splice / exponent leaves the width
-- unknown at compile time (in which case a runtime width check would
-- false-positive and is skipped).  Used as the top-level desync
-- backstop: a result whose actual value count disagrees with its
-- determinate type width means a spliced program's real output stack
-- did not match the type its context assumed — the evalCode arity gap
-- (see spec-code.md / design-metaprogramming.md).  Delivers the
-- "caught by defensive checks, clean runtime errors, never crashes"
-- guarantee spec-code.md claims, which was silently violated.
staticWidth :: SType -> Maybe Int
staticWidth = go 0
  where
    go n (SCons _ rest) = go (n + 1) rest
    go n SEnd           = Just n
    go _ _              = Nothing  -- STail / SExp: indeterminate

-- Backstop check shared by the file runner and the REPL.
desyncError :: SType -> [Value] -> Maybe String
desyncError o out =
  case staticWidth o of
    Just n | n /= length out ->
      Just $ "result desync: the type says " ++ show n ++ " wire(s) but "
          ++ show (length out) ++ " were produced.  A spliced program's "
          ++ "actual output stack disagreed with the type its context "
          ++ "assumed (the evalCode arity gap; see design-metaprogramming.md)."
    _ -> Nothing

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
    arityOf (Forall _ _ _ _ _ (Arrow i _ _)) = closedArity i
    openOf  (Forall _ _ _ _ _ (Arrow i _ _)) = openTailed i
    openTailed (SCons _ rest) = openTailed rest
    openTailed (STail _)      = True
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
    -- readLine: one line from stdin; EOF (or a closed stream) rides
    -- the miss track like any other IO failure
    applyAtom _ (Prim "readLine") stk
      | not (M.member "readLine" vars), not (M.member "readLine" defs) = do
          r <- liftIO (try getLine)
          case r of
            Left e  -> pure ([VSum 1 [VStr (show (e :: IOException))]], stk, [])
            Right t -> pure ([VSum 0 [VStr t]], stk, [])
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
    -- (the forget convention).  Non-final was typed at n := 0.
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
    applyAtom isFinal (Prim "zipN") stk
      | not (M.member "zipN" vars), not (M.member "zipN" defs) =
          if not isFinal then pure ([], stk, [])
          else if odd (length stk)
            then throwError "zipN: odd segment (unreachable on typechecked programs)"
            else let (xs, ys) = splitAt (length stk `div` 2) stk
                 in pure (concat (zipWith (\x y -> [x, y]) xs ys), [], [])
    applyAtom isFinal (Prim "unzipN") stk
      | not (M.member "unzipN" vars), not (M.member "unzipN" defs) =
          if not isFinal then pure ([], stk, [])
          else if odd (length stk)
            then throwError "unzipN: odd segment (unreachable on typechecked programs)"
            else let pairs = chunk2 stk
                 in pure (map fst pairs ++ map snd pairs, [], [])
    applyAtom isFinal (Prim "mapN2") stk
      | not (M.member "mapN2" vars), not (M.member "mapN2" defs) = do
          (args, stk') <- takeWires "mapN2" 1 stk
          case args of
            [VFn scope cvars body] -> do
              let bundle = if isFinal then stk' else []
              if odd (length bundle)
                then throwError "mapN2: odd segment (unreachable on typechecked programs)"
                else do
                  let step (x, y) = do
                        (out, lg) <- evalTerm env scope cvars body [x, y]
                        case out of
                          [w] -> pure (w, lg)
                          _   -> throwError
                                   "mapN2: the quotation must be two wires in, one out"
                  rs <- mapM step (chunk2 bundle)
                  pure ( map fst rs, if isFinal then [] else stk'
                       , concatMap snd rs )
            _ -> throwError "Runtime type error in mapN2: expected a quotation"
    -- at: index into the segment.  0 is the DEEPEST wire — the same
    -- leftmost-is-deepest alignment atoms use.  Non-final closes to
    -- Fin(0), which is uninhabited, so that branch cannot be reached
    -- by a typechecked program.
    applyAtom isFinal (Prim "at") stk
      | not (M.member "at" vars), not (M.member "at" defs) = do
          (args, stk') <- takeWires "at" 1 stk
          case (args, isFinal) of
            ([VInt i], True)
              | i >= 0, i < length stk' -> pure ([stk' !! i], [], [])
              | otherwise -> throwError
                  "at: index out of range (unreachable on typechecked programs)"
            ([VInt _], False) -> throwError
              "at: empty bundle (Fin(0) is uninhabited — is `at` non-final?)"
            _ -> throwError "Runtime type error in at: expected an index"
    -- indicesN: pair each wire with its position, deepest-first
    applyAtom isFinal (Prim "indicesN") stk
      | not (M.member "indicesN" vars), not (M.member "indicesN" defs) =
          if not isFinal then pure ([], stk, [])
            else pure (concat (zipWith (\i v -> [VInt i, v]) [0 ..] stk), [], [])
    -- checkedAt: the DYNAMIC witness.  The bound is erased, so the
    -- live segment's own width is what the index is checked against;
    -- the hit track carries index and bundle on untouched.
    applyAtom isFinal (Prim "checkedAt") stk
      | not (M.member "checkedAt" vars), not (M.member "checkedAt" defs) = do
          (args, stk') <- takeWires "checkedAt" 1 stk
          case args of
            [VInt i] -> do
              let bundle = if isFinal then stk' else []
                  tag    = if i >= 0 && i < length bundle then 0 else 1
              pure ( [VSum tag (VInt i : bundle)]
                   , if isFinal then [] else stk', [] )
            _ -> throwError "Runtime type error in checkedAt: expected an Int"
    applyAtom isFinal (Prim "mapN") stk
      | not (M.member "mapN" vars), not (M.member "mapN" defs) = do
          (args, stk') <- takeWires "mapN" 1 stk
          case args of
            [VFn scope cvars body] -> do
              let bundle = if isFinal then stk' else []
                  step v = do
                    (out, lg) <- evalTerm env scope cvars body [v]
                    case out of
                      [w] -> pure (w, lg)
                      _   -> throwError
                               "mapN: the quotation must be one wire in, one out"
              rs <- mapM step bundle
              pure ( map fst rs, if isFinal then [] else stk'
                   , concatMap snd rs )
            _ -> throwError "Runtime type error in mapN: expected a quotation"
    applyAtom _ (Prim name) stk
      | Just k <- finIndex name
      , not (M.member name vars)
      , not (M.member name defs) = pure ([VInt k], stk, [])
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
                Forall [dummy] [] [] [] [] (arrPure SEnd (SCons (TVarTy dummy) SEnd))
              arityEnv = foldr (\n -> M.insert n dummyScheme)
                               env (M.keys vars)
          Arrow i _ _ <- liftEither (inferTermIn arityEnv t')
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
    Just (Forall _ _ _ _ _ (Arrow i _ _)) -> Right (closedArity i)
    Nothing -> Left $ "Unknown primitive at runtime: " ++ name

runBuiltin :: Env -> RunDefs -> String -> [Value]
           -> Either String ([Value], [String])
runBuiltin _ _ "id"    [v]              = Right ([v], [])
runBuiltin _ _ "_"     [v]              = Right ([v], [])
runBuiltin _ _ "swap"  [x, y]           = Right ([y, x], [])
runBuiltin _ _ "dup"   [v]              = Right ([v, v], [])
runBuiltin _ _ "drop"  [_]              = Right ([], [])
-- weaken/finInt are runtime identities: the bound is a TYPE, and an
-- index is a bare Int.  Widening it and forgetting it are both no-ops
-- on the value — the whole content is in the type.
runBuiltin _ _ "weaken" [v]             = Right ([v], [])
runBuiltin _ _ "finInt" [v]             = Right ([v], [])
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
    go vars (Use rs b)   = Use rs <$> go vars b
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
    go (Use rs b)     = Use rs <$> go b
    go (OpenAbs slots hasRest b) = do
      b' <- go b
      -- compileAbsOpen wants the layout [body inputs (deepest)]
      -- [param block] — the params sit ABOVE the wires the body
      -- consumes (its finalStage passes k0 wires and then drops the
      -- params).  Braid binders bind the DEEPEST wires, so every
      -- slot list with a `_` needs a permutation prefix that sinks
      -- the unnamed wires below the named ones.
      --
      -- An open binder (`x ... ->`) works too, even though the
      -- passthrough width is erased: the remainder is the stack's TAIL,
      -- so it sits ABOVE the param block, and every emitted stage ends
      -- in `pass` — one atom, no width.  Params are reached by depth
      -- from the DEEPEST wire, so every fetch is static and none of
      -- them ever crosses the erased segment.
      --
      -- The one thing that DOES need a width is a body that consumes
      -- out of the remainder.  Inference has already solved that case
      -- (the passthrough is pinned to a concrete stack), so ask it:
      -- a determinate remainder is counted into the body's wires and
      -- the binder compiles closed; an indeterminate one is genuinely
      -- passed through and rides in the `pass`.
      let names = [ n | Just n <- slots ]
          anons = length [ () | Nothing <- slots ]
          extra
            | not hasRest = Nothing
            | otherwise   = restWidth slots hasRest b'
          e = fromMaybe 0 extra
      inner <- compileAbsOpen' env names (anons + e)
                               (hasRest && isNothing extra) b'
      pure (foldr Seq inner
              (paramsAboveStages slots
                 ++ restAboveStages anons (length names) e))
    go t = Right t

    -- wires the passthrough was pinned to, when inference determined it
    restWidth slots hasRest b =
      case inferTermIn env (OpenAbs slots hasRest b) of
        Right (Arrow i _ _)
          | let r = dropS (length slots) i
          , not (openTailedS r) -> Just (closedArity r)
        _ -> Nothing

    dropS :: Int -> SType -> SType
    dropS 0 s              = s
    dropS k (SCons _ rest) = dropS (k - 1) rest
    dropS _ s              = s

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

-- Lift the param block above `e` determinate remainder wires sitting on
-- top of it: [anons][params][rest] → [anons][rest][params], which is the
-- contiguous [body inputs][params] layout compileAbsOpen compiles
-- against once the remainder counts as body input.  Empty when the
-- remainder is indeterminate (e = 0): then it never moves at all — it
-- rides above the params inside each stage's `pass`.
restAboveStages :: Int -> Int -> Int -> [Term]
restAboveStages a n e =
  [ Tensor (swapAt d)
  | j <- [0 .. e - 1]
  , d <- [a + j + n - 1, a + j + n - 2 .. a + j] ]
  where
    swapAt d = replicate d (Prim "_") ++ [Prim "swap", Prim "pass"]

freeNamesIn :: Term -> [String]
freeNamesIn = go
  where
    go (Prim n)       = [n]
    go (Seq a b)      = go a ++ go b
    go (Tensor ts)    = concatMap go ts
    go (Quote t)      = go t
    go (Alts cs _)    = concatMap go cs
    go (Use _ b)      = go b
    go (OpenAbs slots _ b) =
      filter (`notElem` [ n | Just n <- slots ]) (go b)

-- (input arity, output arity, param copies to insert at relative input
-- offsets, replacement atom)
data AtomInfo = AtomInfo Int Int [(Int, Int)] Term

compileAbs :: Env -> [String] -> Term -> Either String Term
compileAbs env ps body = compileAbsOpen env ps 0 body

compileAbsOpen :: Env -> [String] -> Int -> Term -> Either String Term
compileAbsOpen env ps k0 = compileAbsOpen' env ps k0 False

-- Rewrite `body` (consuming k0 underlying wires) so the parameters
-- arrive as a block of wires BELOW those inputs; the block is dropped
-- at the end.  `open` says an erased remainder rides above the params,
-- so the final stage must let it through instead of ending exactly.
compileAbsOpen' :: Env -> [String] -> Int -> Bool -> Term -> Either String Term
compileAbsOpen' env ps k0 open body = do
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
                     ++ [ Prim "pass" | open ]

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
      -- an index literal is a closed point (• ⇒ Fin(…)), so it
      -- reflects like any other literal — not an open-arity word
      | Just _ <- finIndex nm = Right (AtomInfo 0 1 [] t)
      | Just _ <- injIndex nm = segErr nm
      | otherwise =
          case M.lookup nm env of
            Nothing -> Left $ "reflect: unknown name in abstraction body: " ++ nm
            Just (Forall _ _ _ _ _ (Arrow i o _))
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
      Arrow gi go _ <- inferGroupArrow g
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
            Forall [dummy] [] [] [] [] (arrPure SEnd (SCons (TVarTy dummy) SEnd))
          arityEnv = foldr (\nm -> M.insert nm dummyScheme) env ps
      inferTermIn arityEnv g

    segErr nm = Left $
      "reflect: segment-consuming or open-arity atom '" ++ nm
        ++ "' in an abstraction body — not reflectable yet"

openTailedS :: SType -> Bool
openTailedS (SCons _ r)   = openTailedS r
openTailedS (STail _)     = True
openTailedS (SExp _ _ _)  = True   -- unknown width: not a closed stack
openTailedS SEnd          = False

-- Typecheck and run a whole module; main runs on the empty stack.
runModule :: String -> IO (Either String ([Value], [String]))
runModule src = runExceptT $ do
  m <- liftEither (checkModule src)
  -- AUDITED MODELS: every law runs before main and must answer true.
  -- An instance that fails its theory's laws is not an instance, and
  -- saying so at module start is the whole difference between a law
  -- that documents and a law that holds.
  mapM_ (runLaw m) [ (n, t) | (n, _, t) <- modDefs m, isJust (lawParts n) ]
  case modMain m of
    Nothing -> pure ([], [])
    Just (term, arr@(Arrow i o _))
      | closedArity i > 0 ->
          throwError $ "main requires a nonempty input stack: " ++ show arr
      | otherwise -> do
          (out, logs) <- evalTerm (modEnv m) (moduleRunDefs m) M.empty term []
          case desyncError o out of
            Just e  -> throwError e
            Nothing -> pure (out, logs)

-- Run one generated law def; anything but `true` is a module error.
runLaw :: Module -> (String, Term)
       -> ExceptT String IO ()
runLaw m (n, t) = do
  (out, _) <- evalTerm (modEnv m) (moduleRunDefs m) M.empty t []
  case out of
    [VSum 0 []] -> pure ()
    _ ->
      let (inst, lw) = maybe ("?", n) id (lawParts n)
      in throwError $ "law '" ++ lw ++ "' fails for instance " ++ inst
                   ++ ": an instance must be an audited model of its theory"

-- adjacent pairs of a segment (bases of width 2 come interleaved)
chunk2 :: [a] -> [(a, a)]
chunk2 (x : y : rest) = (x, y) : chunk2 rest
chunk2 _              = []
