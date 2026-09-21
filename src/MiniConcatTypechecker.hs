{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module MiniConcatTypechecker where

import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.Set as S
import Data.Set (Set)
import Data.Maybe (fromMaybe, isNothing, isJust, fromJust, catMaybes, listToMaybe)
import Data.List (nub, intercalate, elemIndex, isPrefixOf, isSuffixOf,
                  isInfixOf,
                  stripPrefix, partition, dropWhileEnd, sortOn, (\\))
import Control.Monad.State
import Control.Monad.Except (ExceptT, runExceptT, throwError, liftEither,
                             MonadError, catchError)
import Control.Monad.IO.Class (liftIO)
import Control.Exception (try, IOException, evaluate)
import Control.Monad (foldM)
import Data.Char (isAlpha, isAlphaNum, isDigit, isLower, isSpace, isUpper,
                  toLower)
import Data.Bifunctor (first)
import Numeric (showFFloat)
import System.Directory (doesFileExist, canonicalizePath)
import System.FilePath (takeDirectory, takeFileName, isAbsolute, (</>))

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

-- An arrow's MANIFEST: the set of labels its elaborated code carries,
-- plus an optional tail for effect polymorphism.  Composition JOINS two
-- manifests: grades live in the join-semilattice (P(Labels), ∪, ∅) and
-- `Σ =L> Θ` then `Θ =M> Ξ` is `Σ =L∪M> Ξ`.  Inference states that as a
-- SUBEFFECTING constraint `part ⊆ composite` (Talpin–Jouvelot) and
-- takes the least solution; ∅ is the bottom, so a pure part flows into
-- any composite.
--
-- It used to UNIFY (rows forced equal, the join simulated by absorption
-- into an open tail).  That is sound only while nothing else shares the
-- row: `ev` shares its stage's row with the argument's Fn row, so the
-- composite's labels were pushed INTO the parameter and every derived
-- higher-order word narrowed its argument (2026-09-12; see
-- design-effects.md's amendment and `CSubEff`).
--
-- The set was a Bool until 2026-09-08 (`io` was the only label, being
-- the irreducible one — everything else in the effect zoo is already an
-- ordinary wire).  It widened when functors started minting PROVENANCE
-- labels: `with Traced` leaves `Traced` on everything elaborated under
-- it, so the manifest records not only what a program touches but what
-- rewrote it.  Markers are written, receipts are inferred; a label may
-- only be minted by a `with`, which is what makes it evidence.
data EffRow = Eff { eLabels :: Set String, eTail :: Maybe EVar }
  deriving (Eq, Ord, Show)

-- A subeffecting constraint, `part ⊆ composite`, as a scheme carries
-- it: the link a higher-order word keeps between a parameter's Fn row
-- and its own outer row.  `ev`'s prim scheme writes that link by hand
-- as a SHARED ε; a derived word cannot, because its outer row is a join
-- of several parts, and one tail cannot name a union of several.
type EffSub = (EffRow, EffRow)

-- io is a label like any other; it is spelled out here exactly once
ioLabel :: String
ioLabel = "IO"

-- `IO`'S CARRIER (stage 7b, 2026-09-17).  Every label names a functor,
-- and the functor's carrier is looked up from the label's own
-- declaration: `Log`'s is `Log \8855 -`, a carrier-less label's is the
-- identity on homs, and `IO`'s is `World \8855 -` for an abstract linear
-- `World`.  So `IO` stops being an EXCEPTION in the statement -- it is
-- a label like the others, with its difference in the carrier column
-- rather than in a branch of the checker.
--
-- It stays a shortcut in the IMPLEMENTATION, and this says so plainly
-- rather than claiming more.  There is exactly ONE `World` and it is
-- ambient, so every representative in the fibre `C(World \8855 \931,
-- World \8855 \920)` is determined and the whiskering map is the IDENTITY:
-- the elaborator never writes the wire, routing for it is a no-op, and
-- the four io prims stay marked.  That is Clean's `*World` and GHC's
-- `State# RealWorld` with the wire erased because it is a singleton
-- (design-7b.md \167 4b, reading b2).
--
-- DISCHARGE IS IMPOSSIBLE STRUCTURALLY, not by a check: a handler is
-- `seed ; \8230 ; unwrap`, and those come from the `data` machinery a
-- `resource` declaration drives.  `World` is not declared by
-- `resource` -- it is not declared at all -- so there is no `World`
-- and no `unWorld` to write one with.  The name lives in the
-- compiler's `@` namespace, which source may not write either.
ioCarrier :: String
ioCarrier = ioLabel ++ "@World"

-- THE DICTIONARY'S OWN WIRE (stage 8, 2026-09-17).  A declaration is
-- an ACT ON THE DICTIONARY, and the dictionary is a resource like any
-- other after 7b: a label naming a functor, with a carrier looked up
-- from the label's declaration.  `def f = body` is `[body] "f" defW`,
-- and `defW : Code Str =Dict> •` says in its own arrow what it does —
-- the phase distinction the keyword-initial surface marks, written
-- down as a grade (design-macros.md, "direction 3", 2026-08-29).
--
-- WHAT IT HOLDS is the module's DECLARATIONS SO FAR, not the finished
-- `Module`: the defs with their headers and source, the type lines,
-- the theory/model/functor/transformation blocks, the imports, the
-- tables, the keyword table, and the program lines the declarations did
-- not take.  Not the `Module`, because a `Module` holds an `Env`, a
-- `Scheme` and a `Term`, none of which has a Braid rep — handing one
-- to a program would be bootstrap rung 2 and not a declaration layer.
-- `Dict` is the WRITE handle; the read side already exists and is the
-- reflection words (`declOf`, `typeOfWord`, `envOf`), which read the
-- four tables the checker holds at the point the word runs.
--
-- DISCHARGE IS IMPOSSIBLE STRUCTURALLY, exactly as it is for `World`
-- and for the same reason: a handler is `seed ; • ; unwrap`, and both
-- ends come from the `data` machinery a `resource` declaration drives.
-- `Dict` is not declared by `resource` — it is not declared at all —
-- so there is no `Dict` to seed one with and no `unDict` to open one
-- with, and the name may not be declared either (the refusal below).
-- Its carrier lives in the compiler's `@` namespace, which source may
-- not write.  The one thing that discharges it is the LOADER, which is
-- the host: it holds the dictionary, hands it to each declaration word
-- in turn, and turns what comes back into a module.
dictLabel :: String
dictLabel = "Dict"

dictCarrier :: String
dictCarrier = dictLabel ++ "@Dict"

-- The second built-in label (2026-09-09; renamed and made a MARKER
-- 2026-09-14).  `Recursive` is the name of a scope — `with Recursive`
-- puts a def's own name in scope in its body — and, like every other
-- scope, the name of the label its receipt mints.  It reads "may
-- recurse without bound", NOT "diverges": a labelled word can still be
-- total, and an unlabelled one never ties a knot, hence terminates by
-- construction.  Structural recursors (`foldList`, `foldTree`, … —
-- emitted per `data` declaration) mint nothing: they are bounded by
-- the value they eat.
recLabel :: String
recLabel = "Recursive"

-- The knot, under a name source cannot write: `#` opens a comment, so
-- no program and no reflected atom can name or shadow it.  `with
-- Recursive` is the only thing that emits it — the machinery that was
-- the prim `fix` until 2026-09-14, when `fix` became a prelude def.
knotPrimName :: String
knotPrimName = "#fix"

eIO :: EffRow -> Bool
eIO = S.member ioLabel . eLabels

effPure :: EffRow
effPure = Eff S.empty Nothing

effIO :: EffRow
effIO = effLabel ioLabel

-- the closed row carrying one label: `print`'s io, `with F`'s receipt
effLabel :: String -> EffRow
effLabel l = Eff (S.singleton l) Nothing

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
  | TFloat             -- IEEE double (2026-09-14).  Its own base type
                       -- beside Int, sharing NO word with it: there is no
                       -- numeric tower and no overloading, so `+` is Int
                       -- arithmetic and `fadd` is Float arithmetic.
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
  show TFloat      = "Float"
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

-- IO is a LABEL like any other, so it rides in the manifest rather than
-- decorating the arrow: `a0 =IO> •`, not `a0 ⇒! •`.  The bang was a
-- leftover from when io was the only grade and could afford its own
-- glyph; with functors and categories minting labels beside it, one
-- spelling for all of them is the honest one (2026-09-06).
arrowGlyph :: EffRow -> String
arrowGlyph e
  | S.null (eLabels e) = " ⇒ "
  | otherwise          = " =" ++ unwords (S.toList (eLabels e)) ++ "> "

instance Show Arrow where
  show (Arrow s1 s2 e) = show s1 ++ arrowGlyph e ++ show s2

--------------------------------------------------------------------------------
-- 2. Schemes and environments (only polymorphism over stack vars & type vars)
--------------------------------------------------------------------------------

-- A CONSTRAINED type scheme (Talpin–Jouvelot): the quantifiers, the
-- surviving `⊆` constraints between effect rows, and the arrow.  The
-- constraints are what a derived higher-order word needs and a prim's
-- shared ε expressed by hand — `loop`'s body row flows into `loop`'s
-- own row, so an io body gives an io loop, without the body being
-- forced to carry `Recursive`.
data Scheme = Forall [TVar] [SVar] [RVar] [NVar] [EVar] [EffSub] Arrow
  deriving (Eq, Ord)

instance Show Scheme where
  -- effect variables are deliberately NOT listed: at stage 1 every
  -- arrow has a grade, so nearly every scheme would grow an `ε0` the
  -- reader can do nothing with.  The bang carries all the information
  -- the grade has.  This RAW instance DOES show the ⊆ constraints;
  -- every user-facing renderer (`showSchemeA`, `:t`, `:t!`) hides them
  -- exactly as it hides the tails they relate.
  show (Forall tvars svars rvars nvars _ subs arr) =
    "∀ " ++ unwords (map show tvars ++ map show svars ++ map show rvars
                       ++ map show nvars)
         ++ ". " ++ showSubs subs ++ show arr

-- `{ε0 ⊆ ε1, …} ` — empty when there are none
showSubs :: [EffSub] -> String
showSubs [] = ""
showSubs ss = "{" ++ intercalate ", " [ showEffRaw p ++ " ⊆ " ++ showEffRaw c
                                      | (p, c) <- ss ] ++ "} "

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

class Substitutable a where
  apply :: Subst -> a -> a

instance Substitutable Ty where
  apply s t@(TVarTy v) =
    case M.lookup v (tySub s) of
      Nothing -> t
      Just t' -> apply s t'   -- chase chains, like the SType instance
  apply _ TInt        = TInt
  apply _ TFloat      = TFloat
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
  apply s e@(Eff ls mv) = case mv of
    Nothing -> e
    Just v  -> case M.lookup v (effSub s) of
      Nothing -> e
      -- the tail's own labels UNION in; that is what makes absorption
      -- (⟨io|ε⟩ ~ ⟨|ω⟩ ⟹ ω := ⟨io|υ⟩) come out right on both sides
      Just r  -> let Eff ls' mv' = apply s r in Eff (ls `S.union` ls') mv'

instance Substitutable Arrow where
  apply s (Arrow i o e) = Arrow (apply s i) (apply s o) (apply s e)

instance Substitutable Scheme where
  -- Bound variables are removed from the substitution before it touches
  -- the arrow, so quantified names are never captured.
  apply s (Forall tv sv rv nv ev subs arr) =
    let s' = Subst (foldr M.delete (tySub s) tv)
                   (foldr M.delete (stSub s) sv)
                   (foldr M.delete (rowSub s) rv)
                   (foldr M.delete (expSub s) nv)
                   (foldr M.delete (effSub s) ev)
    in Forall tv sv rv nv ev [ (apply s' p, apply s' c) | (p, c) <- subs ]
              (apply s' arr)

instance Substitutable Env where
  apply s = M.map (apply s)

--------------------------------------------------------------------------------
-- 4. Constraints and unification
--------------------------------------------------------------------------------

data Constraint
  = CEqTy Ty Ty
  | CEqStack SType SType
  | CEqEff EffRow EffRow
  -- `part ⊆ composite`: composition JOINS grades.  Emitted wherever
  -- several arrows make up one (a `;`, a tensor stage, a code row) and
  -- by `subsumes` (code's grade ≤ the written grade IS the semilattice
  -- order).  Equality is kept only where two rows are the SAME row —
  -- inside a `Fn` type, where a prim's scheme shares ε on purpose.
  | CSubEff EffRow EffRow
  | CFail String   -- carry a deferred inference error to the solver
  -- WHERE this constraint came from: the line of the stage `infer` was
  -- looking at when it emitted it (2026-09-15).  The solver reports the
  -- line of the first constraint that fails, which is how a refusal
  -- names a stage instead of a whole file.  Nothing else reads it.
  | CAt Int Constraint
  deriving (Eq, Show)

-- Stamp every constraint a stage emitted with that stage's line.  An
-- INNER stamp wins: a group's own stage is more precise than the stage
-- that contains it.
stampAt :: Int -> [Constraint] -> [Constraint]
stampAt 0 cs = cs
stampAt n cs = map one cs
  where
    one c@(CAt _ _) = c
    one c           = CAt n c

-- …and the other way: the line, and the constraint underneath it.
unAt :: Constraint -> (Maybe Int, Constraint)
unAt (CAt n c) = case unAt c of
  (Nothing, c') -> (Just n, c')
  p             -> p
unAt c = (Nothing, c)

-- A LOCATION, carried inside the message.  Every refusal in this module
-- is an `Either String`, and threading a position through all of it
-- would have touched every line that can fail; instead a located
-- refusal writes its line into the message behind a marker, and the
-- printer (`resolveLoc`) turns the marker into `file:line`.  `\SOH`
-- cannot occur in source: the tokenizer would read it as an identifier
-- character, and no Braid file has one.
locMark :: Int -> String
locMark n = '\SOH' : show n ++ "\SOH"

atLine :: Maybe Int -> String -> String
atLine Nothing  msg = msg
atLine (Just n) msg
  | '\SOH' `elem` msg = msg          -- an inner stage already said where
  | otherwise         = locMark n ++ msg

-- Turn the marker into the thing a reader can act on.  With a map (a
-- file was loaded) that is `path:line`; without one (a REPL line, a
-- module checked from a string) it is `line N`, which is still the line
-- of the text that was handed over.  The separator is `, ` in front of
-- `in def …` and `: ` otherwise, so the whole reads as one sentence:
--
--   examples/frame.braid:212, in def notional: Cannot unify stacks: • vs Str
--   examples/frame.braid:376: Cannot unify stacks: • vs Str
--
-- A message with no marker is returned untouched, so nothing that could
-- not be located grows a fake location.
-- How a refusal about THIS source should name its place.  With a map
-- the file is known; without one the line number is still the line of
-- the text that was handed over — unless there is only one line of it,
-- in which case a location says nothing and is dropped.  That is the
-- REPL: a typed line is one line, and `line 1` is not news.
locFor :: LineMap -> String -> (String -> String)
locFor lm src msg =
  case takeLocMark msg of
    Nothing -> hinted Nothing msg
    Just (n, bare) ->
      let body = hinted (Just n) (stripLoc bare)
      in if placed
           then whereAt lm n
                  ++ (if "in def " `isPrefixOf` body then ", " else ": ")
                  ++ body
           else body
  where
    srcLines = lines src
    placed   = not (null lm) || length srcLines > 1
    hinted n b = b ++ maybe "" ("  " ++) (hintFor srcLines n b)

--------------------------------------------------------------------------------
-- 8.1½ Hints: the rule, where a cheap syntactic check makes it likely
--
-- A refusal states what did not fit; a hint says which RULE is usually
-- behind it, and what to write instead.  Each one fires only on a
-- syntactic shape the checker can see in the source — never on the type
-- error alone — and each says "usually"/"often" where it is a guess,
-- because a confident wrong diagnosis costs more than none.  The seven
-- shapes are the ones three agents in a row lost time to (§14).
--------------------------------------------------------------------------------

hintFor :: [String] -> Maybe Int -> String -> Maybe String
hintFor ls mn msg =
  listToMaybe (catMaybes [ rowArm, knotRow, residual, closedGroup, newStage
                         , forgotInstall, flatUnzip ])
  where
    at k | k >= 1, k <= length ls = Just (ls !! (k - 1))
         | otherwise              = Nothing
    here  = lineCode <$> (mn >>= at)
    -- the nearest line above the failure with code on it
    above = do
      n <- mn
      listToMaybe [ c | k <- [n - 1, n - 2 .. 1], Just l <- [at k]
                      , let c = lineCode l, not (null c) ]
    stacks = "Cannot unify stacks" `isInfixOf` msg

    -- 1. A ROW ARM ON ITS OWN LINE.  `|` never absorbs a break, so the
    -- arm below is a stage of its own and the arms end up composed.
    rowArm = do
      h <- here
      if take 1 h == "|"
        then Just "A row arm on its own line is a new STAGE, so the arms \
                   \compose at `>>` instead of standing side by side: end \
                   \each line of the row with `\\`, or put the row on one \
                   \line (MANUAL \167\&4)."
        else Nothing

    -- 2. A RECURSIVE CALL INSIDE A ROW.  The knot shares open
    -- metavariables with the row's alternatives, so the row must be
    -- closed before it comes back.
    knotRow = do
      _ <- mn
      nm <- defNameOf msg
      let rowLike = case breakOn " in " (drop 1 (dropWhile (/= ':') msg)) of
                      Just rhs -> " | " `isInfixOf` rhs
                      Nothing  -> False
      if "Occurs check failed on stack:" `isInfixOf` msg
           && rowLike && underRecursive nm
        then Just "A recursive call inside a row usually wants `merge` \
                   \after the row: the row leaves the alternatives open, \
                   \and the knot cannot close them (MANUAL \167\&14)."
        else Nothing

    -- 3. A RESIDUAL MEETING A WRITTEN TYPE.  An injection is open: it
    -- says "at least this alternative", and a written type says exactly.
    residual
      | " | \963" `isInfixOf` msg =
          Just "An open injection leaves a residual (`\963`), and a written \
                \type has none: close the row with `(pass | pass)` \
                \(MANUAL \167\&14)."
      | otherwise = Nothing

    -- 4. A GROUP THAT IS NOT LAST IN ITS STAGE.  Every non-final
    -- operand of a tensor stage is instantiated CLOSED, so a group
    -- whose width was meant to be polymorphic is pinned where it sits.
    closedGroup = do
      h <- here
      if stacks && groupNotLast h
        then Just "A grouped atom in non-final position is instantiated \
                   \CLOSED, so its width is fixed here: pin it with `id`, \
                   \or move the group last in its stage (MANUAL \167\&14)."
        else Nothing

    -- 5. A NEW LINE IS A NEW STAGE.  A `(`- or `[`-led line reads as a
    -- continuation and is not one — unless the line above said it was
    -- unfinished, or ended a binder head (whose body does start on the
    -- next line).
    newStage = do
      h <- here
      a <- above
      if stacks && take 1 h `elem` ["(", "["]
           && not (any (`isSuffixOf` a) (continuers ++ ["->", "|", ","]))
        then Just "A new line is a new stage, so this `(` does not \
                   \continue the line above: end that line with `\\` to \
                   \carry the stage on, or write `;` at either end to \
                   \compose (MANUAL \167\&4)."
        else Nothing

    -- 6. A RESOURCE THAT WAS NEVER INSTALLED (2026-09-17).  Since
    -- stage 7b `with R` -- and inferred routing -- MINTS `R`, and the
    -- carrier stays a WIRE riding deepest, so a missing install lands
    -- two ways: a row that carries `R` where a written one does not,
    -- and a wire that is an `R` where a plain one was expected.
    -- Either way the fix is not to write the label -- it is to INSTALL
    -- the resource, or to discharge it with a handler.  *You forgot to
    -- install.*  Fires only when the module DECLARES the resource the
    -- message names, which is the syntactic shape this hint is allowed.
    forgotInstall = do
      r <- listToMaybe [ n | n <- declaredRes, n `elem` msgWords ]
      if "Cannot unify" `isInfixOf` msg
        then Just ("`" ++ r ++ "` is a resource, so the code on one side "
                ++ "of this was ROUTED for it and says so.  The fix is "
                ++ "usually to INSTALL the wire rather than to write the "
                ++ "label: seed it at the call site (`(\"\" ; " ++ r
                ++ ")`), or wrap the program in a handler that seeds and "
                ++ "unwraps (MANUAL \167\&14).")
        else Nothing

    -- 7. `unzipN` ON A FLAT PAIR BUNDLE (2026-09-21).  `unzipN` took
    -- the flat `(a b)\8319` until the Naperian iso was made symmetric;
    -- it takes the BOXED form now, and the flat chunker kept working
    -- under the name `splitN`.  The shape is unmistakable: the line
    -- says `unzipN` and the refusal says `Box`.
    flatUnzip = do
      h <- here
      if "Cannot unify" `isInfixOf` msg && "Box" `isInfixOf` msg
           && "unzipN" `isInfixOf` h
        then Just "`unzipN` takes the BOXED bundle `Box(a b)\8319` \8212 it \
                   \is `zipN`'s inverse, not the flat splitter. To chunk a \
                   \flat `(a b)\8319` into two lanes, write `splitN` \
                   \(MANUAL \167\&13.2)."
        else Nothing

    declaredRes = [ takeWhile (/= '(') n
                  | l <- ls, Just n <- [doctrineCarrierName (lineCode l)] ]

    -- the message's IDENTIFIER-LIKE words, so a resource name matches
    -- as a name and not as a substring of a longer one
    msgWords = words (map (\c -> if isAlphaNum c || c == '_' then c else ' ')
                          msg)

    -- `in def X: …` — the def a refusal is inside, if it says so
    defNameOf m = do
      rest <- stripPrefix "in def " m
      case break (== ':') rest of
        (nm, ':' : _) | not (null nm) -> Just nm
        _                             -> Nothing

    -- does that def's header open `with Recursive`?  Its lines run from
    -- its `def` line down to the failure.
    underRecursive nm = case mn of
      Nothing -> False
      Just n  ->
        let starts = [ k | (k, l) <- zip [1 ..] ls, k <= n
                         , case words (lineCode l) of
                             ("def" : w : _) -> takeWhile (/= '=') w == nm
                                                  || w == nm
                             _               -> False ]
        in case starts of
             [] -> False
             ks -> any (("with Recursive" `isInfixOf`) . lineCode)
                       (take (n - last ks + 1) (drop (last ks - 1) ls))

    groupNotLast h = go (0 :: Int) False h
      where
        -- after a group closes, anything but a stage break means the
        -- group was not the final atom
        go _ _ []       = False
        go d _ ('(' : r) = go (d + 1) False r
        go d _ ('[' : r) = go (d + 1) False r
        go d _ (')' : r) = go (d - 1) (d == 1) r
        go d _ (']' : r) = go (d - 1) (d == 1) r
        go 0 True (c : r)
          | isSpace c              = go 0 True r
          | c `elem` (";|" :: String) = go 0 False r
          | c == '>'               = go 0 False r
          | otherwise              = True
        go d closed (_ : r) = go d closed r

    breakOn sep s
      | Just r <- stripPrefix sep s = Just r
      | (_ : cs) <- s               = breakOn sep cs
      | otherwise                   = Nothing

-- Drop every marker, rendering nothing.
stripLoc :: String -> String
stripLoc s = case break (== '\SOH') s of
  (pre, '\SOH' : more) -> case break (== '\SOH') more of
    (ds, '\SOH' : post) | not (null ds), all isDigit ds -> pre ++ stripLoc post
    _ -> pre ++ more
  _ -> s

resolveLoc :: LineMap -> String -> String
resolveLoc lm msg =
  case takeLocMark msg of
    Nothing        -> msg
    Just (n, rest) ->
      let r = stripLoc rest
      in whereAt lm n ++ (if "in def " `isPrefixOf` r then ", " else ": ") ++ r

-- The first marker in a message: its line, and the message without it.
takeLocMark :: String -> Maybe (Int, String)
takeLocMark s = case break (== '\SOH') s of
  (pre, '\SOH' : more) -> case break (== '\SOH') more of
    (ds, '\SOH' : post) | not (null ds), all isDigit ds ->
      Just (read ds :: Int, pre ++ post)
    _ -> Nothing
  _ -> Nothing

-- The n-th line of the assembled source, named where its author wrote it.
whereAt :: LineMap -> Int -> String
whereAt lm n = case drop (n - 1) lm of
  ((fp, k) : _) | n >= 1 -> fp ++ ":" ++ show k
  _                      -> "line " ++ show n

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
varsOfTy TFloat      = noVars
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

mixedNumbers :: String
mixedNumbers =
  "Cannot unify types: Int vs Float.  Braid has no numeric tower and no \
  \overloading: `+ - * div mod lt?` are Int words and `fadd fsub fmul \
  \fdiv flt?` are Float words, and no word is shared.  Cross with \
  \`toFloat : Int \8658 Float` or `floor : Float \8658 Int`, written where \
  \you mean it."

-- Unify simple element types
unifyTy :: Subst -> Ty -> Ty -> Either String Subst
unifyTy s t1 t2 =
  let t1' = apply s t1
      t2' = apply s t2
  in case (t1', t2') of
    (TVarTy a, t) -> bindTyVar s a t
    (t, TVarTy a) -> bindTyVar s a t
    (TInt, TInt)  -> Right s
    (TFloat, TFloat) -> Right s
    -- The one clash worth its own sentence: there is no numeric tower
    -- and no overloading, so the fix is never "add a coercion here" —
    -- it is a different word, or a written crossing.
    (TInt, TFloat) -> Left mixedNumbers
    (TFloat, TInt) -> Left mixedNumbers
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
  | isRigidT a =
      case t of
        TVarTy b | not (isRigidT b) -> bindTyVar s b (TVarTy a)
        _ -> Left (rigidMsg (show a) (show t))
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
  | isRigidN n =
      Left $ rigidMsg (show n) "a fixed width"
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
  -- a rigid var may still absorb a FLEXIBLE one (bind the flexible side)
  | isRigidS v =
      case st of
        STail w | not (isRigidS w) -> bindStackVar s w (STail v)
        _ -> Left (rigidMsg (show v) (show st))
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

-- Unify two rows that genuinely ARE one row.  COMPOSITION no longer
-- comes here (it joins: see `CSubEff` and `solve`'s second pass) —
-- what does is a `Fn` type meeting another `Fn` type, and the shared ε
-- a higher-order prim writes between its inner `Fn` and its own arrow.
-- `Fn` is invariant in its arrow, so equality is the right question
-- there, and the answer is label-absorbing row unification:
-- ⟨IO|ε⟩ ~ ⟨|ω⟩ binds ω := ⟨IO|υ⟩.  Labels are idempotent (a SET, not
-- a multiset), so a tail may absorb a label the other side already
-- carries, and unifying ⟨A|ε⟩ with ⟨B|ε⟩ is satisfiable at
-- ε := ⟨A B|υ⟩ (design-effects.md; the same discipline that keeps
-- stacks, sums and widths principal).
unifyEff :: Subst -> EffRow -> EffRow -> Either String Subst
unifyEff s e1 e2 =
  case (apply s e1, apply s e2) of
    (a, b) | a == b -> Right s
    -- both closed: the label sets must already agree
    (a@(Eff l1 Nothing), b@(Eff l2 Nothing))
      | l1 == l2  -> Right s
      | otherwise -> clash a b
    -- one open, one closed: the tail supplies the missing labels.  It
    -- can only ADD them, so a label on the open side that the closed
    -- side lacks is unsatisfiable.
    (a@(Eff l1 (Just v)), b@(Eff l2 Nothing))
      | not (S.null (l1 S.\\ l2)) -> clash a b
      | otherwise                 -> bindEffVar s v (Eff (l2 S.\\ l1) Nothing)
    (a@(Eff l1 Nothing), b@(Eff l2 (Just w)))
      | not (S.null (l2 S.\\ l1)) -> clash a b
      | otherwise                 -> bindEffVar s w (Eff (l1 S.\\ l2) Nothing)
    -- both open: each tail takes on what the other side has and it
    -- lacks, and the two share a residual.  When only one side is
    -- poorer the other's tail IS the residual and no variable is minted
    -- — which is what kept `1 >> print` free of one while io was the
    -- only label (solve is a pure fold with no fresh supply).
    (Eff l1 (Just v), Eff l2 (Just w)) ->
      let d1 = l2 S.\\ l1
          d2 = l1 S.\\ l2
          u  = bridge v w
      in case (S.null d1, S.null d2, v == w) of
           (True,  True,  _)     -> bindEffVar s v (Eff S.empty (Just w))
           (_,     _,     True)  -> bindEffVar s v
                                      (Eff (d1 `S.union` d2) (Just u))
           (_,     True,  False) -> bindEffVar s v (Eff d1 (Just w))
           (True,  _,     False) -> bindEffVar s w (Eff d2 (Just v))
           _                     -> do
             s' <- bindEffVar s v (Eff d1 (Just u))
             bindEffVar s' w (Eff d2 (Just u))
  where
    clash x y = Left $ "Cannot unify effects: " ++ showEff x
                    ++ " vs " ++ showEff y ++ hint x y
    -- One side unlabelled is the common shape and it has a fix worth
    -- naming: an unlabelled manifest is one that was WRITTEN (inference
    -- always leaves a tail to absorb into), so the repair is to write
    -- the label there — `Fn⟨Int ⇒ Int⟩` refusing a `fix`/`while` body
    -- wants `Fn⟨Int =Recursive> Int⟩`.
    hint (Eff l1 _) (Eff l2 _)
      | S.null l1, not (S.null l2) = repair l2
      | S.null l2, not (S.null l1) = repair l1
      | otherwise                  = ""
    repair ls = " (the unlabelled side's manifest is written and fixed: "
             ++ "write =" ++ unwords (S.toList ls) ++ "> on that arrow, "
             ++ "or keep this code label-free)"
    -- The residual tail of a pair, named from the pair itself: the
    -- equational pass is a pure fold with no fresh-name supply, and a
    -- pair can be bridged only once (both its variables are bound by
    -- that step, so `ev` never presents them again).  Never rigid —
    -- the tag is a prefix, and this name starts with ε.
    --
    -- Stage 5a⁹⁄₁₀ planned to DELETE this case, on the grounds that
    -- composition no longer unifies parts.  Verified and kept: two
    -- `Fn` types can still be forced equal while each carries a label
    -- the other lacks — `[yell] [spin] >> eq?` for an `=IO>` quote and
    -- a `=Recursive>` one — and under join semantics that program must
    -- type.  A test pins it.
    bridge (EV a) (EV b) = EV ("ε<" ++ a ++ "|" ++ b ++ ">")

showEff :: EffRow -> String
showEff e
  | S.null (eLabels e) = "pure"
  | otherwise          = unwords (S.toList (eLabels e))

-- The row as the SOLVER sees it — labels and tail.  Used only by the
-- raw `Show Scheme` instance, where a ⊆ constraint would otherwise be a
-- relation between two invisible things.
showEffRaw :: EffRow -> String
showEffRaw e@(Eff ls mv) = case mv of
  Nothing -> showEff e
  Just v | S.null ls -> show v
         | otherwise -> unwords (S.toList ls) ++ "|" ++ show v

bindEffVar :: Subst -> EVar -> EffRow -> Either String Subst
bindEffVar s v row
  | eTail row == Just v, S.null (eLabels row) = Right s
  | eTail row == Just v =
      Left $ "Occurs check failed on effect: " ++ show v
  -- a skolem tail may only be renamed to a flexible one, never raised:
  -- the expected manifest is fixed, and code carrying a label the
  -- expectation does not is exactly what the check exists to refuse
  | isRigidE v =
      case row of
        Eff ls (Just w) | S.null ls, not (isRigidE w) ->
          Right s { effSub = M.insert w (Eff S.empty (Just v)) (effSub s) }
        _ -> Left $ "Cannot unify effects: " ++ showEff row
                 ++ " vs pure (the expected type fixes the grade; "
                 ++ "this code must stay pure)"
  | otherwise =
      Right s { effSub = M.insert v row (effSub s) }

bindRowVar :: Subst -> RVar -> SumRow -> Either String Subst
bindRowVar s v row
  | row == RTail v = Right s
  | isRigidR v =
      case row of
        RTail w | not (isRigidR w) -> bindRowVar s w (RTail v)
        _ -> Left (rigidMsg (show v) "a fixed set of alternatives")
  | occursRow v row =
      Left $ "Occurs check failed on sum row: " ++ show v ++ " in " ++ show row
  | otherwise = Right s { rowSub = M.insert v row (rowSub s) }

-- Existential (rigid) variables.  A splice's stamp records what the
-- CONTEXT expected of code that will only exist at runtime.  When that
-- expectation is polymorphic it must not be generalized into the
-- definition's scheme, or every caller could pick its own type for a
-- result none of them can see.  So those variables are frozen: they
-- unify with nothing but themselves, and callers must stay parametric.
rigidTag :: String
rigidTag = "∃"

isRigidT :: TVar -> Bool
isRigidT (TV n) = rigidTag `isPrefixOf` n

isRigidS :: SVar -> Bool
isRigidS (SV n) = rigidTag `isPrefixOf` n

isRigidR :: RVar -> Bool
isRigidR (RV n) = rigidTag `isPrefixOf` n

isRigidN :: NVar -> Bool
isRigidN (NV n) = rigidTag `isPrefixOf` n

isRigidE :: EVar -> Bool
isRigidE (EV n) = rigidTag `isPrefixOf` n

-- A skolem was asked to become something concrete.  The expected type
-- quantifies over it, so the code must work for EVERY choice; demanding
-- one is exactly the failure subsumption exists to catch.
rigidMsg :: String -> String -> String
rigidMsg v what =
  "'" ++ dropRigid v ++ "' is universally quantified in the expected type "
    ++ "but this code requires it to be " ++ what
    ++ " — the expected type promises the code works for every choice of '"
    ++ dropRigid v ++ "', so it must stay parametric in it"

-- skolems are displayed under the name the user actually wrote
dropRigid :: String -> String
dropRigid v = fromMaybe v (stripPrefix rigidTag v)

-- Solve a list of constraints, in TWO passes.
--
--   1. the EQUATIONAL pass — wires, widths, sums, and the effect rows
--      that are genuinely the SAME row (a `Fn` type's, a prim scheme's
--      shared ε).  A fold, exactly as before.
--   2. the LEAST-FIXPOINT pass over the ⊆ constraints: labels flow
--      UPWARD out of the parts into the composites' flexible tails.  A
--      composite whose row is CLOSED (it was written) and that lacks a
--      label one of its parts carries is the error — that is the
--      sandbox.  A RIGID (skolem) tail absorbs nothing, which is what
--      makes a written pure expectation refuse labelled code.
--
-- WHY THE LEAST FIXPOINT IS UNIQUE, hence types principal.  Each ⊆
-- constraint reads `lp ∪ σ(tp) ⊆ lc ∪ σ(tc)` over the join-semilattice
-- (P(Labels), ∪, ∅) — a Horn clause.  If two assignments σ₁, σ₂ each
-- satisfy it then so does their pointwise INTERSECTION, because ∪
-- distributes over ∩ on sets; so the solution set is closed under
-- intersection, a least element exists, and it is unique.  This pass
-- computes it by adding only labels some constraint forces and never
-- one it does not, so it IS that least element.  (Tarski; Talpin &
-- Jouvelot 1992/94 for the effect reading.)  Termination: the label
-- universe is finite — every label comes from some constraint — and
-- each step adds at least one label to some variable's value.
solve :: [Constraint] -> Either String Subst
solve cs0 = do
    s <- foldM step emptySubst eqs
    fixSubs (0 :: Int) (0 :: Int) s
  where
    -- the line each constraint was stamped with, alongside it: every
    -- refusal below is reported AT that line (2026-09-15)
    cs = map unAt cs0
    (subs, eqs) = partition (isSub . snd) cs
    isSub (CSubEff _ _) = True
    isSub _             = False

    step s (ln, c) = first (atLine ln) (raw s c)

    raw s (CEqTy t1 t2)      = unifyTy s t1 t2
    raw s (CEqStack st1 st2) = unifyStack s st1 st2
    raw s (CEqEff e1 e2)     = unifyEff s e1 e2
    raw s (CSubEff _ _)      = Right s            -- pass 2
    raw _ (CFail msg)        = Left msg
    raw s (CAt _ c)          = raw s c

    -- a generous bound on the number of rounds, from the termination
    -- argument above: rounds cannot exceed one per (constraint, label).
    -- Reaching it would be a bug in this pass, not a program error.
    rounds = (length subs + 1) * (S.size allLabels + 1) + 1
    allLabels = S.unions [ eLabels p `S.union` eLabels c
                         | (_, CSubEff p c) <- subs ]

    fixSubs r n s
      | r > rounds = Left "internal: the effect fixpoint did not converge"
      | otherwise = do
          (s', n', changed) <- foldM flow (s, n, False) subs
          if changed then fixSubs (r + 1) n' s' else Right s'

    flow acc@(s, n, _) (ln, CSubEff p0 c0) =
      let p@(Eff lp _)  = apply s p0
          c@(Eff lc tc) = apply s c0
          missing       = lp S.\\ lc
      in if S.null missing then Right acc else
         case tc of
           Nothing -> Left (atLine ln (closedGradeErr p c))
           Just v
             | isRigidE v -> Left (atLine ln (fixedGradeErr p c))
             | otherwise  -> do
                 -- the composite grows by exactly what it was missing,
                 -- keeping a fresh tail so it can grow again
                 s' <- bindEffVar s v (Eff missing (Just (EV ("ε⊔" ++ show n))))
                 Right (s', n + 1, True)
    flow acc _ = Right acc

-- The composite's row is CLOSED: it was written, and a written row is
-- exact.  This is where the sandbox lives.
closedGradeErr :: EffRow -> EffRow -> String
closedGradeErr p c =
  "Cannot unify effects: " ++ showEff p ++ " vs " ++ showEff c
    ++ " (composition joins grades, and this arrow's manifest is written "
    ++ "and fixed: write =" ++ unwords (S.toList (eLabels p `S.union` eLabels c))
    ++ "> on that arrow, or keep this code label-free)"

-- The composite's tail is a SKOLEM: the expectation is someone else's
-- to choose, so it absorbs nothing.  `subsumes` is the only source.
fixedGradeErr :: EffRow -> EffRow -> String
fixedGradeErr p c
  | S.null (eLabels c) =
      base ++ " (the expected type fixes the grade; this code must stay pure)"
  | otherwise =
      base ++ " (the expected type fixes the grade at ="
           ++ unwords (S.toList (eLabels c)) ++ ">; this code also carries "
           ++ unwords (S.toList (eLabels p S.\\ eLabels c)) ++ ")"
  where base = "Cannot unify effects: " ++ showEff p ++ " vs " ++ showEff c

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
-- `substOnce` on a bare effect row (a scheme's ⊆ constraints are pairs
-- of these, and instantiation must rename them with the arrow).
substOnceEff :: Subst -> EffRow -> EffRow
substOnceEff s e@(Eff ls mv) = case mv of
  Just v | Just (Eff ls' mv') <- M.lookup v (effSub s) -> Eff (ls `S.union` ls') mv'
  _ -> e

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

    goE' = substOnceEff s

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
instantiate = fmap fst . instantiateC

-- …and the scheme's ⊆ constraints, freshened with it.  Every use site
-- re-emits them into its own constraint pool: that is how a derived
-- higher-order word passes its parameter's grade out to its caller.
instantiateC :: Scheme -> Infer (Arrow, [Constraint])
instantiateC (Forall tvars svars rvars nvars evars subs arr) = do
  newTVs <- mapM (const freshTyVarName) tvars
  newSVs <- mapM (const freshSVarName) svars
  newRVs <- mapM (const freshRVarName) rvars
  newNVs <- mapM (const freshNVarName) nvars
  newEVs <- mapM (const freshEVarName) evars
  let tSub = M.fromList (zip tvars (map TVarTy newTVs))
      sSub = M.fromList (zip svars (map STail newSVs))
      rSub = M.fromList (zip rvars (map RTail newRVs))
      nSub = M.fromList (zip nvars (map (Exp 0 . Just) newNVs))
      eSub = M.fromList (zip evars [ Eff S.empty (Just v) | v <- newEVs ])
      sub  = Subst tSub sSub rSub nSub eSub
  arr' <- openEff (substOnce sub arr)
  pure (arr', [ CSubEff (substOnceEff sub p) (substOnceEff sub c)
              | (p, c) <- subs ])

-- Every use of a scheme whose grade is CLOSED gets a fresh tail, so
-- composition can absorb labels into it: `1 >> print` works because the
-- literal's ⟨⟩ opens to ⟨|ε⟩ and unifies with print's ⟨io|ε'⟩.  Without
-- this, every pure word would refuse to sit next to an effectful one.
-- Schemes that already carry an explicit ε (ev, loop, the folds) are
-- left alone — their tail is their polymorphism.
openEff :: Arrow -> Infer Arrow
openEff (Arrow i o e@(Eff _ Nothing)) = do
  v <- freshEVarName
  pure (Arrow i o e { eTail = Just v })
openEff arr = pure arr

-- A fresh, wholly unknown grade: the row a COMPOSITE starts with,
-- before its parts' labels flow into it.  Composition joins, so the
-- composite is a new variable bounded below by each part — never one
-- of the parts, which is what used to narrow them.
freshEffRow :: Infer EffRow
freshEffRow = Eff S.empty . Just <$> freshEVarName

-- Instantiate a scheme *closed* for a non-final tensor atom: only the
-- OUTER TAILS of the arrow are closed (ρ := •) — that is all appendStack
-- needs.  Variables living purely inside element types (Fn⟨…⟩, sums)
-- are freshened like any instantiation: they are the atom's
-- polymorphism, not a remainder.  (Matches the grouped-compound closing
-- policy.)
instantiateClosed :: Scheme -> Infer Arrow
instantiateClosed = fmap fst . instantiateClosedC

instantiateClosedC :: Scheme -> Infer (Arrow, [Constraint])
instantiateClosedC (Forall tvars svars rvars nvars evars subs arr@(Arrow i o _)) = do
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
      eSub = M.fromList (zip evars [ Eff S.empty (Just v) | v <- newEVs ])
  -- effect variables are FRESHENED, never closed: closing ε for a
  -- non-final atom would let `1 print` typecheck as pure.
  let sub = Subst tSub sSub rSub nSub eSub
  arr' <- openEff (substOnce sub arr)
  pure (arr', [ CSubEff (substOnceEff sub p) (substOnceEff sub c)
              | (p, c) <- subs ])

-- Is a scheme AT LEAST AS GENERAL as an expected arrow?
--
-- Two places need this and they are the same question at two phases: a
-- theory slot's declared arrow is an expectation written in the theory,
-- and `evalAs`'s witness is an expectation written in the program.  In
-- both, the expected arrow's variables stand for "whatever the CONTEXT
-- chose", which the checked code does not get to pick.  So they are
-- skolemized for the duration of the check and the candidate is
-- instantiated fresh.
--
-- Plain unification would be unsound: `drop 1 1 : a b ⇒ Int Int` unifies
-- with an expected `a ⇒ a a` at a := Int, and then a context that chose
-- Str runs it anyway.  Subsumption rejects that, because the skolem for
-- `a` refuses to become Int.
--
-- The effect tail is skolemized too (see skolemizeArrow): a pure
-- expectation admits only pure code, an io expectation admits both
-- grades by absorption.
subsumes :: Scheme -> Arrow -> Either String ()
subsumes = subsumesWith skolemizeArrow

-- The same question about the WIRES only, with the manifest left free:
-- `interpose` asks whether a stage fits at every cut, which is a
-- question about shape.  A stage that prints, or that carries a
-- functor's receipt, still fits; enumerating the labels it may carry
-- would be a list to keep up to date, and an open tail is that list.
subsumesShape :: Scheme -> Arrow -> Either String ()
subsumesShape = subsumesWith skolemizeStacks

subsumesWith :: (Arrow -> Arrow) -> Scheme -> Arrow -> Either String ()
subsumesWith skolemize sc expected =
  let want       = skolemize expected
      (got, gcs) = runInfer0 (instantiateC sc)
  -- The GRADE is compared by ⊆, not by =: "this code's grade is at most
  -- what the written type allows" IS the semilattice order, and with
  -- `want`'s tail skolemized it absorbs nothing, so a pure expectation
  -- still refuses labelled code while an io one accepts pure code.
  in () <$ solve ( [ CEqStack (arrowIn got)  (arrowIn want)
                   , CEqStack (arrowOut got) (arrowOut want)
                   , CSubEff  (arrowEff got) (arrowEff want) ] ++ gcs )

arrowIn :: Arrow -> SType
arrowIn (Arrow i _ _) = i

arrowOut :: Arrow -> SType
arrowOut (Arrow _ o _) = o

arrowEff :: Arrow -> EffRow
arrowEff (Arrow _ _ e) = e

-- Freeze every variable of an arrow — type, stack, row, width, AND the
-- effect tail — into a rigid constant, so unification may not choose a
-- value for it.  The rigid naming convention (`rigidTag`) and the guards
-- in the bind*Var functions are what enforce it.  Freezing the effect
-- tail is what makes a pure expectation a SANDBOX: absorption would
-- otherwise let io code raise the tail and pass.  (Before this the
-- refusal happened only by accident, when the two inference runs
-- happened to reuse the same tail name and tripped the occurs check.)
skolemizeArrow :: Arrow -> Arrow
skolemizeArrow arr =
  let (tvs, svs, rvs, nvs, evs) = varsOfArrow arr
      sk s = rigidTag ++ s
      tSub = M.fromList [ (v, TVarTy (TV (sk n)))       | v@(TV n) <- tvs ]
      sSub = M.fromList [ (v, STail  (SV (sk n)))       | v@(SV n) <- svs ]
      rSub = M.fromList [ (v, RTail  (RV (sk n)))       | v@(RV n) <- rvs ]
      nSub = M.fromList [ (v, Exp 0 (Just (NV (sk n)))) | v@(NV n) <- nvs ]
      eSub = M.fromList [ (v, Eff S.empty (Just (EV (sk n)))) | v@(EV n) <- evs ]
  in substOnce (Subst tSub sSub rSub nSub eSub) arr

-- Freeze the wires but not the manifest: the labels stay free to absorb
-- whatever the checked code carries.  (`skolemizeArrow` minus eSub.)
skolemizeStacks :: Arrow -> Arrow
skolemizeStacks arr =
  let (tvs, svs, rvs, nvs, _) = varsOfArrow arr
      sk s = rigidTag ++ s
      tSub = M.fromList [ (v, TVarTy (TV (sk n)))       | v@(TV n) <- tvs ]
      sSub = M.fromList [ (v, STail  (SV (sk n)))       | v@(SV n) <- svs ]
      rSub = M.fromList [ (v, RTail  (RV (sk n)))       | v@(RV n) <- rvs ]
      nSub = M.fromList [ (v, Exp 0 (Just (NV (sk n)))) | v@(NV n) <- nvs ]
  in substOnce (Subst tSub sSub rSub nSub M.empty) arr

-- exponent variables on a stack's spine (not inside element types)
spineExpVars :: SType -> [NVar]
spineExpVars (SExp _ (Exp _ (Just n)) r) = n : spineExpVars r
spineExpVars (SExp _ _ r)                = spineExpVars r
spineExpVars (SCons _ r)                 = spineExpVars r
spineExpVars _                           = []

--------------------------------------------------------------------------------
-- 6. Terms
--------------------------------------------------------------------------------


-- What a `with` clause DOES to the body, for the model it names.
--
-- A Doctrine model — one whose theory declares a hom-object and a
-- composition — can be applied to a body in exactly two ways, and which
-- one is right is decided by the def's `in` clause and by nothing else
-- (2026-09-16):
--
--   * `Transporting`: the body is a BASE program and the model is the
--     functor that carries it into the category — `;` becomes
--     `compose`, every stage becomes `embed` of itself.  This is
--     `def f with Enum = …`, a def with no `in`.
--   * `Instantiating`: the body is ALREADY a morphism of the theory (a
--     template, `def f in Prob = …`), so the model only says what its
--     slot names mean.  Composition stays the base's, because a
--     morphism of B[T] composes like the base.
--
-- Never both: transporting a template would embed the expansion's own
-- `embed` and `compose`, which is exactly the failure `design-macros.md`
-- recorded on 2026-09-15.  A receipt is minted either way — `with`
-- always mints.
data Apply = Transporting | Instantiating deriving (Show, Eq, Ord)

data Term
  = Prim String
  | Tensor [Term]         -- n-ary tensor chain, atoms aligned with wires left to right
  | Seq Int Term Term     -- t >> u, stamped with the LINE the right-hand
                          -- stage was written on (0 = the compiler wrote
                          -- it, so it has no line of its own).  This is
                          -- the whole of the location mechanism: a
                          -- refusal names the stage that failed because
                          -- the `>>` that put it there remembers where
                          -- it came from (2026-09-15).
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
  | With Apply [String] Term
                          -- `with M1 M2` — a def's APPLICATION clause.
                          -- The named things ride DEEPEST, and the
                          -- def's body is the scope; every stage in it
                          -- gets its routing written by the elaborator
                          -- (`elabHeaders`), which runs between parse
                          -- and infer.  This node never reaches
                          -- inference.  `Apply` says whether a model
                          -- named here TRANSPORTS the body or only
                          -- INSTANTIATES it (see `Apply`).
  | In [String] Term      -- `in X` — a def's MEMBERSHIP clause, saying
                          -- what the def IS: a morphism of theory X (a
                          -- TEMPLATE, whose body waits for a model)
                          -- or of a model with a carrier (a hand-built
                          -- word of that category).  It
                          -- applies nothing — that is `with`'s job — so
                          -- the elaborator consumes the clause and
                          -- leaves the body exactly as written.  Like
                          -- `With`, it never reaches inference.
  | Alts [Term] Bool      -- (p₁ | … | pₙ [| ---]): code row — the sum
                          -- functor action; one component per
                          -- alternative, residual flag = identity on
                          -- the remaining alternatives
  deriving (Show)

-- Ord because a quotation is a symbolic VALUE in the normalizer (§12.9)
-- and a case split keys a map on symbolic values — and BOTH skip a
-- stage's line stamp, because provenance is not structure: two programs
-- written on different lines are the same program, and `eq?` on two
-- quotes must say so.  The constructor order is the declaration order,
-- exactly what `deriving` gave until 2026-09-15.
termTag :: Term -> Int
termTag Prim{}    = 0
termTag Tensor{}  = 1
termTag Seq{}     = 2
termTag Quote{}   = 3
termTag OpenAbs{} = 4
termTag With{}    = 5
termTag In{}      = 6
termTag Alts{}    = 7

instance Eq Term where
  a == b = compare a b == EQ

instance Ord Term where
  compare (Prim a)        (Prim b)        = compare a b
  compare (Tensor a)      (Tensor b)      = compare a b
  compare (Seq _ a b)     (Seq _ c d)     = compare a c <> compare b d
  compare (Quote a)       (Quote b)       = compare a b
  compare (OpenAbs a b c) (OpenAbs d e f) =
    compare a d <> compare b e <> compare c f
  compare (With a b c)    (With d e f)    =
    compare a d <> compare b e <> compare c f
  compare (In a b)        (In c d)        = compare a c <> compare b d
  compare (Alts a b)      (Alts c d)      = compare a c <> compare b d
  compare a b = compare (termTag a) (termTag b)

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
  | TokDashes     -- --- (the ROW tail: "and more alternatives")
  | TokNewline Int
      -- line break (strict >>), stamped with the number of the line it
      -- OPENS.  A stage begins after a break, so the break is where the
      -- lexer can say which line the next stage was written on — the
      -- one fact every refusal in §14 wanted and none of them had
      -- (2026-09-15).  Nothing else needs a stamp: within one line a
      -- stage cannot move.
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
  | TokEffArrow [String]
      -- =IO>, =Recursive>, =IO Recursive>, … (and the older ⇒! / ->!, which mean
      -- =IO>): a LABELLED arrow inside a Fn type.  The labels are the
      -- written manifest, in any order; display sorts them.
  deriving (Eq, Show)

tokenize :: String -> Either String [Token]
tokenize = go 1
  where
    go _ [] = Right []
    go n ('\r':'\n':cs) = (TokNewline (n + 1) :) <$> go (n + 1) cs
    go n ('\n':cs)      = (TokNewline (n + 1) :) <$> go (n + 1) cs
    go n ('#':cs)         = go n (dropWhile (/= '\n') cs)  -- comment to EOL
    -- A LINE THAT WRAPS (2026-09-14).  A newline is a strict `>>`, so a
    -- tensor stage that will not fit on one line needs a way to say
    -- "not yet": a `\` closing the line drops the newline, and the next
    -- line continues the SAME stage.  It is the one continuation form —
    -- a line that begins or ends with `;`/`>>` already continues by
    -- composition (`normalizeToks`), and indentation cannot be made to
    -- mean this without changing every multi-line def body, which is
    -- indented deeper than its `def` line and relies on newline = `>>`.
    -- `\` collides with nothing: it is unwritable in a program today,
    -- and it is stage-final where `|`, `...` and `---` are not.
    go n ('\\':cs)
      | Just rest <- afterLine cs =
          case dropWhile (`elem` (" \t\r" :: String)) rest of
            (c : _) | c /= '\n' && c /= '#' -> go (n + 1) rest
            _ -> Left (atLine (Just n)
                   "A `\\` continues a tensor stage onto the next line, \
                   \so the next line must have something on it")
      | otherwise = Left (atLine (Just n)
                     "A `\\` continues a tensor stage onto the next \
                     \line, so it must be the last thing on its line")
      where
        afterLine str = case dropWhile (`elem` (" \t\r" :: String)) str of
          ('\n' : r) -> Just r
          ('#' : r)  -> case dropWhile (/= '\n') r of
                          ('\n' : r') -> Just r'
                          _           -> Nothing
          _          -> Nothing
    go n ('"':cs)         = do
      (str, rest) <- lexStr cs
      (TokIdent ('"' : str) :) <$> go n rest
    go n ('>':'=':'>':cs) = (TokKleisli :) <$> go n cs
    go n ('>':'?':'>':cs) = (TokOrElse :) <$> go n cs
    go n ('>':'!':'>':cs) = (TokOrClose :) <$> go n cs
    go n ('>':'>':'>':cs) = (TokSeqPass :) <$> go n cs
    go n ('>':'>':cs)     = (TokSeq :) <$> go n cs
    go _ ('>':_)          = Left "Unexpected '>' without matching '>>'"
    go n ('.':'.':'.':cs) = (TokEllipsis :) <$> go n cs
    go n ('.':cs)
      | (nm, rest) <- span isIdentChar cs
      , not (null nm) = (TokIdent ('.' : nm) :) <$> go n rest
    go n ('…':cs)         = (TokEllipsis :) <$> go n cs   -- U+2026, autocorrect's ...
    go _ ('.':_)          = Left "Unexpected '.' (did you mean '...'?)"
    go n ('[':cs)         = (TokLBrack :) <$> go n cs
    go n (']':cs)         = (TokRBrack :) <$> go n cs
    go n ('(':cs)         = (TokLParen :) <$> go n cs
    go n (')':cs)         = (TokRParen :) <$> go n cs
    go n (',':cs)         = (TokComma :) <$> go n cs
    -- `=IO Recursive>`: what the manifest DISPLAYS, so also what you write.
    -- Any label set, in any order, on one line; `=` that is not the
    -- head of such an arrow (a `def`'s `=`) falls through to an
    -- identifier.  (The older `⇒!`/`->!` spellings still lex as `=IO>`,
    -- for source that predates the 2026-09-06 move of io into the
    -- manifest.)
    go n ('=':cs)
      | Just (labels, rest) <- lexEffArrow cs = (TokEffArrow labels :) <$> go n rest
    go n ('-':'>':'!':cs) = (TokEffArrow [ioLabel] :) <$> go n cs
    -- `---` is ONE token, and only one: `----` is `---` then minus.
    go n ('-':'-':'-':cs) = (TokDashes :) <$> go n cs
    go n ('-':'>':cs)     = (TokArrow :) <$> go n cs
    go n ('-':cs)
      | (ds@(_:_), rest) <- span isDigit cs =
          case floatTail rest of
            Just (frac, rest') ->                      -- negative Float
              expNote rest' ((TokIdent ('-' : ds ++ "." ++ frac) :) <$> go n rest')
            Nothing -> expNote rest ((TokIdent ('-' : ds) :) <$> go n rest)
      | otherwise = (TokIdent "-" :) <$> go n cs         -- subtraction
    go n ('|':cs)         = (TokBar :) <$> go n cs
    go n ('^':cs)         = (TokCaret :) <$> go n cs
    go n (';':cs)         = (TokSeq :) <$> go n cs   -- ; is a synonym for >>
    go n ('⟨':cs)         = (TokLAngle :) <$> go n cs     -- Fn⟨…⟩ type brackets
    go n ('⟩':cs)         = (TokRAngle :) <$> go n cs
    go n ('⇒':'!':cs)     = (TokEffArrow [ioLabel] :) <$> go n cs
    go n ('⇒':cs)         = (TokFatArrow :) <$> go n cs

    go n (c:cs)
      | isSpace c = go n cs
      -- Unicode superscripts lex as ^ + the translated exponent
      | Just _ <- unSup c =
          let (sups, rest) = span (isJust . unSup) (c:cs)
              plain = map (fromJust . unSup) sups
          in ((TokCaret :) . (supTok plain :)) <$> go n rest
      | isDigit c =
          let (digits, rest) = span isDigit (c:cs)
          in case floatTail rest of
               Just (frac, rest') ->
                 expNote rest' ((TokIdent (digits ++ "." ++ frac) :) <$> go n rest')
               Nothing -> expNote rest ((TokInt (read digits) :) <$> go n rest)
      | otherwise =
          let (ident, rest) = span isIdentChar (c:cs)
          in case appliedSlot rest of
               Just (tail', rest') -> (TokIdent (ident ++ tail') :) <$> go n rest'
               Nothing             -> (TokIdent ident :) <$> go n rest

    -- A SLOT OF AN APPLIED MODEL: `Fwd(Floats)@add` (2026-09-15).  A
    -- model parameterized by a model is named by its APPLICATION — one
    -- spelling for the header, the receipt and the transformation that
    -- names it — so the def names it heads carry parentheses.  `@` is
    -- the compiler's character and is refused wherever source is walked,
    -- so `)@` cannot appear in a program anyone wrote: absorbing the
    -- balanced group and the slot name into one identifier here is
    -- unambiguous, and it is what lets a generated slot, law or square
    -- be ordinary source like every other one.
    appliedSlot ('(' : cs0) = walk (1 :: Int) "(" cs0
      where
        walk _ _   []       = Nothing
        walk 0 acc ('@':r)  =
          let (nm, r') = span isIdentChar r
          in if null nm then Nothing
             else Just (reverse acc ++ "@" ++ nm, r')
        walk 0 _   _        = Nothing
        walk d acc (ch : r)
          | ch == '('                = walk (d + 1) (ch : acc) r
          | ch == ')'                = walk (d - 1) (ch : acc) r
          | isIdentChar ch           = walk d (ch : acc) r
          | ch == ',' || ch == ' '   = walk d (ch : acc) r
          | otherwise                = Nothing
    appliedSlot _ = Nothing

    -- A FLOAT LITERAL is digits `.` digits (2026-09-14), lexed as one
    -- identifier so that it travels the whole pipeline — scheme, spine,
    -- reflection, runtime — exactly as an Int literal does.  It is taken
    -- only after a digit, so `2...` is still `2` then `...` and `.foo`
    -- is still a symbol.
    floatTail ('.' : cs@(d : _))
      | isDigit d = let (frac, rest) = span isDigit cs in Just (frac, rest)
    floatTail _   = Nothing

    -- …and there is no exponent form.  `-` cannot be an identifier
    -- character (it heads `->`, `---` and every negative literal), so
    -- `1e-3` would need a lexer case of its own for a notation the
    -- display convention never prints back.  One spelling per thing.
    expNote (e : cs) _
      | e `elem` ("eE" :: String)
      , (d : _) <- dropWhile (`elem` ("+-" :: String)) cs
      , isDigit d =
          Left "Exponent notation is not a Float literal: write the decimal \
               \point form (1e-3 is 0.001)"
    expNote _ k = k

    supTok plain
      | all isDigit plain = TokInt (read plain)
      | otherwise         = TokIdent plain

    unSup ch = lookup ch (zip "⁰¹²³⁴⁵⁶⁷⁸⁹ⁿᵐᵏⁱʲ" "0123456789nmkij")

    isIdentChar ch =
      not (isSpace ch) && isNothing (unSup ch)
        && ch `notElem` (">.[](),-|#\"^;\8230\10216\10217\8658" :: String)

    -- After a `=`: is this the head of a written manifest arrow?  It is
    -- iff what follows is one or more capitalized label names separated
    -- by blanks and closed by a single `>` on the same line.  The tests
    -- are deliberately narrow so that `def f = A >> b` and `def f = g`
    -- keep lexing as they always did: a label must start uppercase, and
    -- the closing `>` must not be the first half of `>>`.
    lexEffArrow cs =
      let (body, rest) = span (\ch -> ch /= '>' && ch /= '\n') cs
          labels = words body
      in case rest of
           ('>' : '>' : _) -> Nothing
           ('>' : more)
             | not (null labels)
             , all isLabelName labels -> Just (labels, more)
           _ -> Nothing

    isLabelName (c : rest) = isUpper c && all isIdentChar rest
    isLabelName []         = False

    -- string literal body: minimal escapes \" \\ \n
    lexStr ('\\':'"':cs)  = first ('"' :)  <$> lexStr cs
    lexStr ('\\':'\\':cs) = first ('\\' :) <$> lexStr cs
    lexStr ('\\':'n':cs)  = first ('\n' :) <$> lexStr cs
    lexStr ('"':cs)       = Right ("", cs)
    lexStr (c:cs)         = first (c :) <$> lexStr cs
    lexStr []             = Left "Unterminated string literal"

-- Is this token a line break?  A break carries the number of the line
-- it opens (2026-09-15), so it is no longer comparable with `==`.
isNewlineTok :: Token -> Bool
isNewlineTok (TokNewline _) = True
isNewlineTok _              = False

-- Collapse newline runs, drop leading/trailing newlines, and absorb
-- newlines adjacent to an operator or a bracket delimiter.
normalizeToks :: [Token] -> [Token]
normalizeToks = snd . normalizeToksAt

-- ...and the line the FIRST stage sits on.  Blank and comment lines
-- before it are not stages, so `trim` drops their breaks — and with
-- them the only stamp that could have said where the program starts.
-- It is returned instead of thrown away (2026-09-15).
normalizeToksAt :: [Token] -> (Int, [Token])
normalizeToksAt ts =
  let c            = collapse ts
      (lead, rest) = span isNewlineTok c
      start        = last (1 : [ l | TokNewline l <- lead ])
  in (start, dropTrailing rest)
  where
    -- A newline is a strict `>>`.  Two things absorb one:
    --
    --   * the railway operators (`>=>`, `>?>`, `>!>`) — composition a
    --     newline cannot itself express, so the operator wins;
    --   * `>>` and `;`, on either side — a newline already IS `>>`, so
    --     writing it too is redundant rather than wrong (2026-09-14);
    --   * a bracket delimiter, on its inner side: newlines just after
    --     `(`/`[` and just before `)`/`]`.  A bracket is an explicit
    --     scope, so a break against its edge is layout, not a stage
    --     boundary — that is what lets a wide atom wrap.
    --
    -- A newline BETWEEN stages inside a bracket is still `>>`: `(1 ⏎ 2)`
    -- is `(1 >> 2)`, exactly as at top level.  `|` never absorbs: the
    -- row separator must stay put so aligned track-columns work (`f |`
    -- ⏎ `| g` is two rows, not one collided `| |`).
    --
    -- A RUN of breaks collapses to the LAST one's stamp: blank lines
    -- are not stages, so the line that opens the next stage is the one
    -- the final break names.  An ABSORBED break takes its stamp with
    -- it, so a stage carried onto the next line by `;`/`>>`/`\\` — or
    -- opened against a bracket edge — reports the line the stage
    -- STARTED on.  That is the honest answer for a stage that spans
    -- lines, and it is the only one a token stream with no stamp left
    -- in it can give.
    collapse [] = []
    collapse (TokNewline k : ts) =
      let (run, ts') = span isNewlineTok ts
          ln         = last (k : [ l | TokNewline l <- run ])
      in case ts' of
           (t : _) | absorbsBefore t -> collapse ts'
           _                         -> TokNewline ln : collapse ts'
    collapse (t : ts)
      | absorbsAfter t = t : collapse (dropWhile isNewlineTok ts)
      | otherwise      = t : collapse ts

    dropTrailing = reverse . dropWhile isNewlineTok . reverse

    -- newlines FOLLOWING this token are absorbed
    absorbsAfter t = railway t || seqTok t || t == TokLParen || t == TokLBrack
    -- newlines PRECEDING this token are absorbed
    absorbsBefore t = railway t || seqTok t || t == TokRParen || t == TokRBrack

    -- ...and `>>` / `;` on either side of the break (2026-09-14).  A
    -- newline already IS `>>`, so a line that begins or ends with one
    -- is saying the same thing twice — which is exactly why it should
    -- be legal: a long pipeline reads better with the operator carried
    -- onto the line it joins.  Both were ERRORS before this (`Expected
    -- a tensor stage, got: TokSeq`), so no file changes meaning.
    seqTok t = t == TokSeq || t == TokSeqPass

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

-- Does a source line SAY it is unfinished?  Three ways, all of them
-- the ones `tokenize`/`normalizeToks` already honour: a trailing `\`
-- (the stage itself wraps), a trailing `;`/`>>` (the composition is
-- carried onto the next line), a trailing railway operator.  Comments
-- and string literals are skipped, exactly as `lineDepth` skips them.
-- The line-based layers above the parser ask, so a stage may wrap
-- inside an inline `def` body the way a bracket already may.
lineContinues :: String -> Bool
lineContinues l = any (`isSuffixOf` lineCode l) continuers

-- What a line SAYS it has not finished with.  One list, because
-- `lineContinues` and the hint that explains a silent stage boundary
-- (§14) must agree about it.
continuers :: [String]
continuers = ["\\", ";", ">>", ">=>", ">?>", ">!>"]

-- A line's code: the comment cut off the end, string literals kept
-- whole, the blanks trimmed from both sides.
lineCode :: String -> String
lineCode = trimSpace . codeOf
  where
    codeOf []       = []
    codeOf ('#':_)  = []
    codeOf ('"':cs) = '"' : strTail cs
    codeOf (c:cs)   = c : codeOf cs
    strTail ('\\':d:cs) = '\\' : d : strTail cs
    strTail ('"':cs)    = '"' : codeOf cs
    strTail (c:cs)      = c : strTail cs
    strTail []          = []

--------------------------------------------------------------------------------
-- 6.0½ Destructuring binders (2026-09-14)
--
-- `(Dual(a, da) Dual(b, db) -> …)` is SYNTAX, and it dies here.  The
-- rewrite is purely token-level, before any parse tree exists, and what
-- it produces is exactly the source a user wrote by hand until today:
-- the data type's generated `un` word applied in place, then an
-- ORDINARY binder over the fields.
--
--   (Dual(a, da) Dual(b, db) -> p)  ≡  unDual _ >> _ _ unDual >> (a da b db -> p)
--   (Dual(a, da) x -> p)            ≡  unDual _ >> (a da x -> p)
--   (Dual(a, da) ... -> p)          ≡  unDual >> (a da ... -> p)
--
-- so there is no destructuring binder downstream of this function: no
-- new Term, no new case in inference, in the runtime, in `reflect`.  A
-- field may itself be a pattern (`Pair(Dual(a, da), b)`), because the
-- rewrite lands on a binder head the same scan reaches again.
--
-- The un-stage for the j-th slot pads with `_`: one for each wire
-- already un-constructed to its left, one for each slot still whole to
-- its right — which is what makes `_ _ unDual` the second stage of a
-- two-`Dual` head.
--------------------------------------------------------------------------------

-- What a pattern needs to know about a data type: how many ALTERNATIVES
-- it has (a pattern un-constructs one, so more than one is refused) and
-- how many FIELDS that alternative holds (the pattern's arity).
data PatCon = PatCon
  { pcAlts   :: Int
  , pcFields :: Int
  } deriving (Eq, Show)

patCons :: [DataDecl] -> [(String, PatCon)]
patCons ds = [ (dName d, con (dBody d)) | d <- ds ]
  where
    con (TSum (RCons st RNil)) = PatCon 1 (closedArity st)
    con (TSum row)             = PatCon (rowLen row) 0
    con _                      = PatCon 1 1
    rowLen (RCons _ r) = 1 + rowLen r
    rowLen _           = 0 :: Int

-- one slot of a binder head: a name (or `_`), or a constructor pattern
data PatSlot = PSPlain Token | PSPat String [PatSlot]
  deriving (Eq, Show)

isPatSlot :: PatSlot -> Bool
isPatSlot (PSPat _ _) = True
isPatSlot _           = False

-- how many wires the slot leaves once its own `un` has run
patWidth :: PatSlot -> Int
patWidth (PSPlain _)  = 1
patWidth (PSPat _ fs) = length fs

-- back to tokens: a plain slot is its token, a pattern is written out
-- again (the scan reaches it once it heads a binder of its own)
patToks :: PatSlot -> [Token]
patToks (PSPlain t)  = [t]
patToks (PSPat c fs) =
  TokIdent c : TokLParen : intercalate [TokComma] (map patToks fs) ++ [TokRParen]

-- Rewrite every destructuring binder in a token stream.  `tbl` is the
-- data types in scope; with none (a `parse` of a string at runtime) a
-- pattern is refused by name rather than guessed at.
expandPatterns :: [(String, PatCon)] -> [Token] -> Either String [Token]
expandPatterns tbl = go Nothing
  where
    go _ [] = Right []
    go prev ts@(t : rest)
      | binderPos prev
      , Just (slots, hasRest, after) <- scanHead ts
      , any isPatSlot slots = do
          mapM_ validate slots
          go prev (rewrite slots hasRest after)
      | otherwise = (t :) <$> go (Just t) rest

    -- exactly where `parseProgramToks` consults `binderPrefix`: the
    -- start of a scope, a new line, the inside edge of a bracket, or
    -- the body of a header word
    binderPos Nothing  = True
    binderPos (Just t) =
      isNewlineTok t
        || t `elem` [TokLParen, TokLBrack, TokSeq, TokArrow]

    -- the un-stages, then the plain binder, then the rest of the SCOPE
    -- as its body — which is where the inserted `)` goes
    rewrite slots hasRest after =
      intercalate [TokSeq] stages ++ [TokSeq, TokLParen]
        ++ concatMap headOf slots ++ [TokEllipsis | hasRest] ++ [TokArrow]
        ++ body ++ [TokRParen] ++ tl
      where
        -- a pattern slot becomes its FIELDS; a field that is itself a
        -- pattern is written back out, and the same scan reaches it
        headOf (PSPlain t)  = [t]
        headOf (PSPat _ fs) = concatMap patToks fs
        ws  = map patWidth slots
        n   = length slots
        (body, tl) = splitScope after
        stages =
          [ replicate (sum (take (j - 1) ws)) (TokIdent "_")
              ++ [TokIdent ("un" ++ c)]
              ++ replicate (n - j) (TokIdent "_")
          | (j, PSPat c _) <- zip [1 :: Int ..] slots ]

    validate (PSPlain _) = Right ()
    validate (PSPat c fs) =
      case lookup c tbl of
        Nothing -> Left $ "`" ++ c ++ "(…)` in a binder: `" ++ c
                       ++ "` is not a `data` type in scope, and a pattern "
                       ++ "un-constructs one"
        Just pc
          | pcAlts pc /= 1 ->
              Left $ "`" ++ c ++ "(…)` in a binder: `" ++ c ++ "` has "
                  ++ show (pcAlts pc) ++ " alternatives and a pattern "
                  ++ "un-constructs ONE — use a row, `(… | … | …)`"
          | length fs /= pcFields pc ->
              Left $ "`" ++ c ++ "(…)` in a binder names "
                  ++ show (length fs) ++ " field"
                  ++ (if length fs == 1 then "" else "s") ++ ", but `" ++ c
                  ++ "` has " ++ show (pcFields pc)
          | otherwise -> mapM_ validate fs

    -- the rest of the current scope: up to the bracket that closes it
    splitScope = walk (0 :: Int) []
      where
        walk d acc (x : xs)
          | x == TokLParen || x == TokLBrack = walk (d + 1) (x : acc) xs
          | x == TokRParen || x == TokRBrack =
              if d == 0 then (reverse acc, x : xs) else walk (d - 1) (x : acc) xs
          | otherwise = walk d (x : acc) xs
        walk _ acc [] = (reverse acc, [])

    -- a run of slots closed by `->`, with at least one slot.  Nothing
    -- means "not a binder head", and then not one token is touched.
    scanHead = run []
      where
        run acc (TokEllipsis : TokArrow : r)
          | not (null acc) = Just (reverse acc, True, r)
        run acc (TokArrow : r)
          | not (null acc) = Just (reverse acc, False, r)
        run acc ts = case slotAt ts of
          Just (s, r) -> run (s : acc) r
          Nothing     -> Nothing

    -- `C(f, …)` is a pattern when the parens hold a field list AND
    -- either a comma settles it (a comma is not a program token, so
    -- nothing else can be meant) or `C` is a data type in scope.  Any
    -- other `word (` ends the run, and the head is not a binder head.
    slotAt (TokIdent c : TokLParen : r)
      | Just (inner, r') <- balanced r
      , Just fs <- mapM field (splitCommaToks inner)
      , TokComma `elem` inner || isJust (lookup c tbl) = Just (PSPat c fs, r')
    slotAt (TokIdent n : r) = Just (PSPlain (TokIdent n), r)
    slotAt _                = Nothing

    field piece = case slotAt piece of
      Just (s, []) -> Just s
      _            -> Nothing

    balanced = walk (0 :: Int) []
      where
        walk 0 acc (TokRParen : r) = Just (reverse acc, r)
        walk d acc (x : xs)
          | x == TokLParen || x == TokLBrack = walk (d + 1) (x : acc) xs
          | x == TokRParen || x == TokRBrack = walk (d - 1) (x : acc) xs
          | otherwise                        = walk d (x : acc) xs
        walk _ _ [] = Nothing

    splitCommaToks = walk (0 :: Int) [] []
      where
        walk _ cur acc [] = reverse (addCur cur acc)
        walk d cur acc (x : xs)
          | x == TokComma && d == 0 = walk d [] (addCur cur acc) xs
          | x == TokLParen || x == TokLBrack = walk (d + 1) (x : cur) acc xs
          | x == TokRParen || x == TokRBrack = walk (d - 1) (x : cur) acc xs
          | otherwise                        = walk d (x : cur) acc xs
        addCur []  acc = acc
        addCur cur acc = reverse cur : acc

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
parseProgram = parseProgramIn []

-- ...and the same, with the data types a destructuring binder's
-- patterns are read against (§6.0½).  Every site that has them passes
-- them; `parseProgram` is the site that has none.
parseProgramIn :: [DataDecl] -> String -> Either String Term
parseProgramIn = parseProgramAt id

-- ...and the same, told where in the FILE this text starts.  A def body
-- is a run of consecutive lines, so its map is `(+ (start - 1))`; a main
-- program is the lines a module did not spend on declarations, so its
-- map is a lookup.  Everything downstream of here — every stage stamp,
-- every constraint, every refusal — is already in the file's own
-- numbering (2026-09-15).
parseProgramAt :: (Int -> Int) -> [DataDecl] -> String -> Either String Term
parseProgramAt lineOf datas = fmap fst . parseProgramFrom lineOf datas

-- ...and the line its FIRST stage sits on, which no `>>` introduced and
-- which therefore carries no stamp of its own.  Callers hand it back to
-- inference as the fallback for anything the term did not stamp.
parseProgramFrom :: (Int -> Int) -> [DataDecl] -> String
                 -> Either String (Term, Int)
parseProgramFrom lineOf datas input = first (remapMark lineOf) $ do
  (start, toks0) <- normalizeToksAt <$> tokenize input
  toks  <- expandPatterns (patCons datas) toks0
  (term, rest) <- parseProgramToks start toks
  case rest of
    [] -> Right (remapLines lineOf term, lineOf start)
    _  -> Left $ "Unexpected tokens at end: " ++ show rest

-- Rewrite every stage stamp through a map.  The parser counts lines
-- from 1 within the text it was given; this puts them where the reader
-- can see them.  A 0 stamp is the compiler's own code and stays 0.
-- ...and the same for a refusal the LEXER or PARSER wrote, which
-- counted the lines of the text it was given and knows nothing of the
-- file it came out of.
remapMark :: (Int -> Int) -> String -> String
remapMark f s = case takeLocMark s of
  Just (n, rest) | n /= 0 -> locMark (f n) ++ rest
  _                       -> s

remapLines :: (Int -> Int) -> Term -> Term
remapLines f = go
  where
    go (Seq n a b)       = Seq (if n == 0 then 0 else f n) (go a) (go b)
    go (Tensor ts)       = Tensor (map go ts)
    go (Quote a)         = Quote (go a)
    go (OpenAbs ps r a)  = OpenAbs ps r (go a)
    go (With ap ns a)    = With ap ns (go a)
    go (In ns a)         = In ns (go a)
    go (Alts as r)       = Alts (map go as) r
    go p@(Prim _)        = p

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
-- `def NAME [in T] [with M …] = body` — a def's two header clauses,
-- parsed off the line's left-hand side (2026-09-16).  `in` is
-- MEMBERSHIP (what this def is a morphism of; applies nothing, mints
-- nothing) and `with` is APPLICATION (the functors to apply to the
-- body; a `with` mints its receipt when it changed the body).  At most one `in`, `in` before
-- `with`, both header-only: the body is a pure spine.
data DefHdr = DefHdr { dhIn :: Maybe String, dhWith :: [String] }
  deriving (Show, Eq)

noHdr :: DefHdr
noHdr = DefHdr Nothing []

-- the names a header mentions, for the passes that read source text
-- (family application, self-reference)
hdrNames :: DefHdr -> [String]
hdrNames h = maybe [] pure (dhIn h) ++ dhWith h

parseDefHdr :: String -> String -> Either String DefHdr
parseDefHdr l src
  | all isSpace src = Right noHdr
  | otherwise = do
      toks <- normalizeToks <$> tokenize src
      clauses toks
  where
    clauses (TokIdent w : _) | Just e <- retiredHeader w
                             , w `notElem` headerWords = Left e
    clauses (TokIdent "in" : ts) = case headerNames ts of
      ([], _)  -> Left $ "`in` names the one thing this def is a morphism "
                      ++ "of — a theory (making it a template) or a model "
                      ++ "with a carrier: " ++ l
      ([t], _) | t == recLabel -> Left $ "`" ++ recLabel
                      ++ "` is applied, not lived in: write `with "
                      ++ recLabel ++ "`; the open-recursion body is `fix` "
                      ++ "by hand (MANUAL §8)"
      ([t], r) -> DefHdr (Just t) <$> withClause r
      (ns, _)  -> Left $ "`in " ++ unwords ns ++ "`: a def is ONE thing, so "
                      ++ "`in` names exactly one theory (making this def a "
                      ++ "template) or one model with a carrier (making it "
                      ++ "a word of that category).  `with` is the clause "
                      ++ "that takes a list."
    clauses ts@(TokIdent "with" : _) = DefHdr Nothing <$> withClause ts
    clauses _ = Left badHdr

    withClause [] = Right []
    withClause (TokIdent "with" : ts) = case headerNames ts of
      ([], _) -> Left $ "`with` names what is applied to this def's body — "
                     ++ "a model, a resource, a functor, or `" ++ recLabel
                     ++ "`: " ++ l
      (ns, r) -> do
        case r of
          []                 -> Right ()
          (TokIdent "in" : _) -> Left inLate
          _                  -> Left badHdr
        case [ n | (n, i) <- zip ns [0 :: Int ..], n `elem` take i ns ] of
          (n : _) -> Left $ "`with`: " ++ n ++ " is named twice"
          []      -> Right ns
    withClause (TokIdent "in" : _) = Left inLate
    withClause _ = Left badHdr

    inLate = "`in` comes before `with`: a def says what it IS, then what "
          ++ "is applied to it — `def <name> in <T> with <M> = …` "
          ++ "(MANUAL §8)"
    badHdr = "Malformed definition header (want `def <name> [in <T>] "
          ++ "[with <M> …] = …`): " ++ l

-- THE HEADER CLAUSES, read off a `def` line.
--
-- A run of names, each of which may be an APPLICATION — `with
-- Fwd(Floats)` applies a parameterized model — and the applied form IS
-- the name: one spelling, so the receipt, the transformation that names
-- the model and the header all read the same.
headerNames :: [Token] -> ([String], [Token])
headerNames (TokIdent n : rest)
  | n /= "_", n `notElem` headerWords, isHeaderName n = case rest of
      (TokLParen : r) | Just (as, r') <- headerArgs r ->
        let (ns, r'') = headerNames r'
        in (renderModelApp (ModelApp n as) : ns, r'')
      _ -> let (ns, r') = headerNames rest in (n : ns, r')
headerNames ts = ([], ts)

headerArgs :: [Token] -> Maybe ([ModelApp], [Token])
headerArgs ts = do
  (a, r) <- headerApp ts
  case r of
    (TokComma : r')  -> do (as, r'') <- headerArgs r'
                           pure (a : as, r'')
    (TokRParen : r') -> Just ([a], r')
    _                -> Nothing

headerApp :: [Token] -> Maybe (ModelApp, [Token])
headerApp (TokIdent n : TokLParen : r) = do
  (as, r') <- headerArgs r
  pure (ModelApp n as, r')
headerApp (TokIdent n : r) | n /= "_" = Just (ModelApp n [], r)
headerApp _                = Nothing

-- The two header words, and the two that were retired for them.
headerWords :: [String]
headerWords = ["in", "with"]

-- A name a clause can carry: a declaration's name, never punctuation —
-- so a quotation's `=` ends the run rather than joining it.
isHeaderName :: String -> Bool
isHeaderName n = not (null n) && (isAlpha (head n) || head n == '_')
              && all (\c -> isAlphaNum c || c `elem` ("_'?!" :: String)) n

-- A body is a pure SPINE (2026-09-16): every header word is refused
-- there, and each refusal names the clause to write instead.
retiredHeader :: String -> Maybe String
retiredHeader "use" = Just $
  "`use` is gone since 2026-09-16: applying a model, a resource or a "
  ++ "functor is a def's HEADER CLAUSE, not a stage — write `def <name> "
  ++ "with <X> = …` (MANUAL §8)"
retiredHeader "over" = Just $
  "`over` is gone since 2026-09-16: saying what a def is a morphism of "
  ++ "is a def's HEADER CLAUSE, not a stage — write `def <name> in <X> "
  ++ "= …` (MANUAL §8)"
retiredHeader "with" = Just $
  "`with` is a def's header clause, not a stage: it goes left of the "
  ++ "`=` — `def <name> with <X> = …` (MANUAL §8).  A scope is not a "
  ++ "stage."
retiredHeader "in" = Just $
  "`in` is a def's header clause, not a stage: it goes left of the "
  ++ "`=` — `def <name> in <X> = …` (MANUAL §8).  Membership is not a "
  ++ "stage."
retiredHeader _ = Nothing

parseProgramToks :: Int -> [Token] -> Either String (Term, [Token])
parseProgramToks ln0 toks =
  case toks of
    -- `in` and `with` are a def's HEADER CLAUSES and never stages: a
    -- scope is not a stage, so it is not written in the spine
    -- (2026-09-16).  `use` and `over` were the words until then.
    (TokIdent w : _) | Just e <- retiredHeader w -> Left e
    -- a leading arrow names the wires this scope was handed
    (TokArrow : ts) -> mkName ln0 ts
    _ ->
      case binderPrefix toks of
        Just (ps, rest) -> mkAbs ln0 ps rest
        Nothing -> do
          (t0, rest) <- parseRow ln0 toks
          loop ln0 t0 rest
  where
    -- `stage -> names`: the stage ends at the arrow (parseStage leaves
    -- it), and the names label the wires the stage just produced
    loop ln acc (TokArrow : rest) = do
      (nm, r') <- mkName ln rest
      Right (Seq ln acc nm, r')
    loop _ acc (TokNewline ln : rest)
      | (TokIdent w : _) <- rest, Just e <- retiredHeader w = Left e
      | (TokArrow : ts) <- rest = do
          (nm, r') <- mkName ln ts
          Right (Seq ln acc nm, r')
      | Just (ps, r) <- binderPrefix rest = do
          (abs', r') <- mkAbs ln ps r
          Right (Seq ln acc abs', r')
      | otherwise = do
          (t, rest') <- parseRow ln rest
          loop ln (Seq ln acc t) rest'
    loop _ acc rest = Right (acc, rest)

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
    mkName ln ts = do
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
        (TokArrow : more)     -> Right more     -- `-> names -> body`
        (TokSeq : more)       -> Right more
        (TokNewline _ : more) -> Right more
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
      (body, rest') <- parseProgramToks ln (repush ++ TokNewline ln : bodyToks)
      Right (OpenAbs slots True body, rest')

    slotOf (TokIdent "_") = Right Nothing
    slotOf (TokIdent n)   = Right (Just n)
    slotOf TokEllipsis    =
      Left "'...' is implicit in '-> …' — it always passes the rest along"
    slotOf _              = Left "Malformed parameter list"

    endsScope []              = True
    endsScope (TokRParen : _) = True
    endsScope (TokRBrack : _) = True
    endsScope _               = False

    mkAbs ln toks0 rest = do
      -- split the parameter list into names, `_` passthroughs and a
      -- trailing `...`.  The stage vocabulary applies, with one
      -- ordering rule: names come first (they sit deepest), then any
      -- `_`, then at most one `...` last.
      (slots, hasRest) <- classifyParams toks0
      let ns = [ n | Just n <- slots ]
      case [ p | (p, n) <- zip ns [0 :: Int ..], p `elem` take n ns ] of
        (p : _) -> Left $ "Duplicate parameter: " ++ p
        []      -> Right ()
      (body, rest') <- parseProgramToks ln rest
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
          Just (ids, dropWhile isNewlineTok r)
        _                           -> Nothing
    isParamTok (TokIdent _) = True
    isParamTok TokEllipsis  = True
    isParamTok _            = False

-- row level: sequences joined by |, optional trailing `| ---` residual
parseRow :: Int -> [Token] -> Either String (Term, [Token])
parseRow ln toks =
  case toks of
    -- a leading `|` defaults the first alternative to identity:
    -- `(| f)` ≡ `(pass | f)`, `(| f | g)` ≡ `(pass | f | g)`.  Lets a
    -- vertical row put every arm on a `|`-led line.
    (TokBar : _) -> loop [Prim "pass"] toks
    _            -> do (t0, rest) <- parseKleisli ln toks
                       loop [t0] rest
  where
    -- `| ---` is the RESIDUAL: identity on every remaining alternative.
    loop acc (TokBar : TokDashes : rest)
      | endsRow rest = Right (Alts (reverse acc) True, rest)
      | otherwise    = Left "'| ---' must end its row"
    -- `| ...` meant the residual until 2026-09-12.  Refused rather than
    -- re-read, so no old row silently changes meaning: `...` continues
    -- WIRES, `---` continues ALTERNATIVES, and a row that wanted a third
    -- track that passes says so.
    loop _ (TokBar : TokEllipsis : rest)
      | endsRow rest =
          Left "`| ...` used to mean the residual; write `| ---` for more \
               \alternatives, or `| pass` for a third track that passes"
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
      (t, rest') <- parseKleisli ln rest
      loop (t : acc) rest'
    loop [t] rest = Right (t, rest)
    loop acc rest = Right (Alts (reverse acc) False, rest)

    endsRow (TokNewline _ : _) = True
    endsRow (TokRParen : _)  = True
    endsRow (TokRBrack : _)  = True
    endsRow []               = True
    endsRow _                = False

-- kleisli level: >>-sequences joined by >=>.  Pure parse-time sugar for
-- composition in the sum monad — the desugaring is the `and` idiom:
--   t1 >=> t2   ≡   t1 >> (t2 | alt2) >> merge
-- (t2 runs on the hit track; the miss track re-injects untouched).
parseKleisli :: Int -> [Token] -> Either String (Term, [Token])
parseKleisli ln toks = do
  (s0, rest) <- parseSeqStmt ln toks
  loop (desugarStmt ln s0) rest
  where
    loop acc (TokKleisli : rest) = do
      (s, rest') <- parseSeqStmt ln rest
      loop (kleisli acc (desugarStmt ln s)) rest'
    loop acc (TokOrElse : rest) = do
      (s, rest') <- parseSeqStmt ln rest
      loop (orElse acc (desugarStmt ln s)) rest'
    loop acc (TokOrClose : rest) = do
      (s, rest') <- parseSeqStmt ln rest
      loop (orClose acc (desugarStmt ln s)) rest'
    loop acc rest = Right (acc, rest)

    -- >=> threads the hit track (bind of (·|E)); >?> threads the miss
    -- track (bind of (B|·)): keep an answer, else try the next stage
    kleisli t1 t2 =
      Seq ln t1 (Seq ln (Alts [t2, Prim "alt2"] False) (Prim "merge"))
    orElse t1 t2 =
      Seq ln t1 (Seq ln (Alts [Prim "alt1", t2] False) (Prim "merge"))
    orClose t1 t2 =
      Seq ln t1 (Seq ln (Alts [Prim "pass", t2] False) (Prim "merge"))

-- sequence level: stages joined by >> / >>> only
parseSeqStmt :: Int -> [Token] -> Either String (Stmt, [Token])
parseSeqStmt ln toks = do
  (s0, rest) <- parseStage ln toks
  (ops, rest') <- go [] rest
  Right (Stmt s0 ops, rest')
  where
    go acc (TokSeq : rest')     = next acc StageSeq rest'
    go acc (TokSeqPass : rest') = next acc StageSeqPass rest'
    go acc rest'                = Right (reverse acc, rest')

    next acc op rest' = do
      (stage, rest'') <- parseStage ln rest'
      go ((op, stage) : acc) rest''

parseStage :: Int -> [Token] -> Either String (Stage, [Token])
parseStage ln = go []
  where
    -- a header word at the head of a stage, wherever the stage begins:
    -- `def f = dup ; use Log ; …` reaches here rather than
    -- `parseProgramToks`, and must get the same refusal (2026-09-16)
    go [] (TokIdent w : TokIdent _ : _)
      | Just e <- retiredHeader w = here e
    -- `•` is the glyph spelling of `one`, the identity on the terminal
    -- object (§5, §9).  It dies at the parse, exactly as `...` becomes
    -- `pass` and `->` becomes `⇒`: one morphism, one word, two ways to
    -- type it — and `reflect`/`unparse` show the word.
    go acc (TokIdent "•" : rest)  = go (Prim "one" : acc) rest
    go acc (TokIdent name : rest) = go (Prim name : acc) rest
    go acc (TokInt n : rest)      = go (Prim (show n) : acc) rest
    -- [p] reifies; [x y -> p] is shorthand for [(x y -> p)]
    -- A quotation is the OTHER place a body is written, so it takes the
    -- same `with` clause a def does, introduced by the same `=`:
    -- `[with Fuel = dup ; *]` (2026-09-16).  It declares nothing, so
    -- there is no `in` here.
    go acc (TokLBrack : rest)     = do
      (ns, rest0) <- quoteClause rest
      (t, rest') <- parseDelimited ln rest0
      case rest' of
        (TokRBrack : rest'') ->
          go (Quote (case ns of { [] -> t ; _ -> With Transporting ns t })
                : acc) rest''
        _ -> here "Unclosed quotation (expected ']')"
    -- (p): grouping only — the enclosed program is an ordinary atom,
    -- not reified.  (x y -> p): named open abstraction.
    go acc (TokLParen : rest)     = do
      (t, rest') <- parseDelimited ln rest
      case rest' of
        (TokRParen : rest'') -> go (t : acc) rest''
        _ -> here "Unclosed group (expected ')')"
    go acc (TokEllipsis : rest)   =
      case rest of
        (t : _) | isStageTok t ->
          here "'...' must be the final atom of a tensor stage"
        _ -> Right (Stage (reverse acc) True, rest)
    -- `-> names` closes the stage it follows and is left for
    -- parseProgramToks (the body is the rest of the SCOPE, which only
    -- that level can build).  With no stage to its left — an arrow
    -- straight after `;`/`>>` — the stage is just `pass`.
    go acc rest@(TokArrow : _)
      | null acc  = Right (Stage [Prim "pass"] False, rest)
      | otherwise = Right (Stage (reverse acc) False, rest)
    go acc rest
      | null acc  = here ("Expected a tensor stage" ++ context rest)
      | otherwise = Right (Stage (reverse acc) False, rest)

    -- a parse refusal knows its line the same way a stage does
    here msg = Left (atLine (Just ln) msg)

    isStageTok (TokIdent _) = True
    isStageTok (TokInt _)   = True
    isStageTok TokEllipsis  = True
    isStageTok TokLBrack    = True
    isStageTok TokLParen    = True
    isStageTok _            = False

    -- the clause a quotation may open with, and the `=` that ends it
    quoteClause (TokIdent "with" : r) = case headerNames r of
      ([], _) -> here "`with` names what is applied to the quoted body — \
                      \a model, a resource or a functor: `[with Fuel = \
                      \dup ; *]`"
      (ns, TokIdent "=" : body) -> Right (ns, body)
      _ -> here "a quotation's `with` clause is followed by `=` and then \
                \the quoted body: `[with Fuel = dup ; *]`"
    quoteClause (TokIdent "in" : _) =
      here "`in` says what a DEF is a morphism of, and a quotation is \
           \not a def: a quotation applies (`with`) and declares nothing"
    quoteClause ts = Right ([], ts)


    context []      = " (unexpected end of input)"
    context (t : _) = ", got: " ++ show t

-- The contents of a ( ) or [ ]: an optional `x y ->` parameter prefix
-- (the arrow is required for parameter introduction — bare idents are a
-- tensor stage), then a full program, possibly a |-separated code row.
-- A 1-ary row is plain grouping.  A trailing `| ---` marks the residual:
-- identity on the remaining alternatives (open row).
-- A delimited scope (group or quote body).  Binder recognition lives
-- in parseProgramToks now, so `(x y -> body)` and `[x y -> body]` are
-- handled there (a leading binder in the delimited scope).
parseDelimited :: Int -> [Token] -> Either String (Term, [Token])
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
-- A fourth kind, and the only one a THEORY may declare: `PCon`, a type
-- CONSTRUCTOR parameter, written with its kind visible as underscores —
-- `theory Arrow(k(_, _))`.  A bare name is a wire and `...` is a stack,
-- so a constructor cannot be spelled bare without stealing one of those
-- readings; the underscores are the arity, checked at the model.
-- `k` is not a type: it never reaches inference.  It exists inside the
-- theory's slot signatures only, and `slotArrowAt` substitutes the
-- model's declared constructor NAME for it before any slot is
-- forward-declared or checked (the ML-functor move).
-- A fifth kind (2026-09-12): `PRow`, a ROW — the tail of a sum's
-- ALTERNATIVES, written `---`.  `...` and `---` are the two tails, and
-- they are different things in different positions: `...` after
-- whitespace continues WIRES (ρ), `---` after `|` continues
-- ALTERNATIVES (σ).  Every σ used to be inferred and unwritable; a
-- `---` parameter is what lets a declaration say "at least these
-- alternatives, maybe more".
data TyParam = PWire TVar | PStack SVar | PWidth NVar | PCon String [Bool]
             | PRow RVar
  deriving (Eq, Show)

pName :: TyParam -> String
pName (PWire (TV n))  = n
pName (PStack (SV n)) = n
pName (PWidth (NV n)) = n
pName (PCon n _)      = n
pName (PRow (RV n))   = n

-- how a parameter's kind reads back in an error message
pKind :: TyParam -> String
pKind (PWire _)    = "a wire"
pKind (PStack _)   = "a stack (`...`)"
pKind (PWidth _)   = "a width"
pKind (PCon _ ks)  = "a type constructor of arity " ++ show (length ks)
pKind (PRow _)     = "a row (`---`)"

isStackParam :: TyParam -> Bool
isStackParam (PStack _) = True
isStackParam _          = False

isWidthParam :: TyParam -> Bool
isWidthParam (PWidth _) = True
isWidthParam _          = False

isWireParam :: TyParam -> Bool
isWireParam (PWire _) = True
isWireParam _         = False

isRowParam :: TyParam -> Bool
isRowParam (PRow _) = True
isRowParam _        = False

-- the one `---` parameter of a declaration, if it has one
rowParamOf :: [TyParam] -> Maybe RVar
rowParamOf ps = case [ rv | PRow rv <- ps ] of
                  (rv : _) -> Just rv
                  []       -> Nothing

-- the stack a parameter stands for when the declaration is instantiated
paramStack :: TyParam -> SType
paramStack (PWire tv)  = SCons (TVarTy tv) SEnd
paramStack (PStack sv) = STail sv
paramStack (PWidth nv) =
  -- unreachable: `data` declarations reject width parameters at
  -- declaration time, and only they build a TData spine from params
  error ("paramStack: width parameter " ++ show nv
         ++ " (data declarations reject these)")
paramStack (PCon n _) =
  -- unreachable: only a `theory` head can declare a constructor
  -- parameter, and a theory builds no TData spine from its parameters
  error ("paramStack: constructor parameter " ++ n
         ++ " (only theories declare these)")
-- A row argument rides as the ONE WIRE it always is in a type: the sum
-- whose alternatives it names.  `data Any2(---) = (Int | Str | ---)`
-- therefore gives `Any2 : (Int | Str | s) => Any2((s))` — the inner
-- parens are the row, the outer ones the argument list, and the
-- argument at a `---` position is written exactly as any row is.
paramStack (PRow rv) = SCons (TSum (RTail rv)) SEnd

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
  , dFields :: [String] -- NAMED FIELDS (2026-09-14).  A single-alternative
                        -- `data` declaration may name its positions —
                        -- `data Trade = (sym: Str, px: Float, qty: Int)`
                        -- — and each name becomes a PROJECTION WORD,
                        -- `sym : Trade ⇒ Str`, generated beside `unTrade`
                        -- and `foldTrade`.  The names die at the parse:
                        -- the TYPE is the positional stack it always
                        -- was, and what survives is this list, so
                        -- `unTrade` and a destructuring binder keep
                        -- working unchanged.  Empty when none were
                        -- written; column names are words, never types.
  } deriving (Eq, Show)

-- A THEORY is named slots plus laws.  Not a typeclass: nothing is
-- inferred or dispatched, a model is selected BY NAME with `with`,
-- and the laws are ordinary Braid programs that must evaluate to `true`
-- — so a model is an AUDITED model rather than a promise
-- (design-effects.md: "laws as runnable checks ... the
-- laws-are-programs doctrine given a front door").
data Theory = Theory
  { thName   :: String
  , thParams :: [TyParam]
  , thSlots  :: [(String, Arrow)]    -- declared signatures
  , thLaws   :: [(String, String)]   -- name, program source
  , thIn     :: Maybe String         -- `theory T(…) in D` — T's slots
                                     -- that D also declares are D's, at
                                     -- D's shape, and D's laws are T's
  , thReads  :: [(String, String)]   -- slot -> its canonical BASE word
                                     -- (`copy : • ⇒ k(Float, Float Float)
                                     -- = dup`).  The generators of the
                                     -- WIDE SUBCATEGORY `embed` is
                                     -- defined on: see `readTransport`.
  } deriving (Eq, Show)

-- THE OBJECT MAP (stage 7c, 2026-09-17).  A model is a presentation
-- interpreted in a category, given by an OBJECT MAP and an image for
-- each generator; until now every model carried the identity object map
-- and only the images were written.  `model Mod in Base(Int ↦ Mod7 via
-- reduce)` writes the other half: the map is the SUBSTITUTION `A := B`,
-- applied structurally — under `List`, a data type's arguments, an
-- `Fn` arrow, a stack — and it is principal for the same reason a
-- family's carrier is, because substitution commutes with unification
-- and there is no type-level function anywhere.
--
-- `via c` is the image of the LITERAL FAMILY: every literal of type A
-- becomes `lit ; c`, which is the one generator class a table cannot
-- name (there are infinitely many of them and none of them is a word).
-- `, r` is a RETRACTION `B ⇒ A` with `c ; r = id_A`; where it is given,
-- every generator the table does not name is DERIVED by conjugation.
data ObjMap = ObjMap
  { omFrom :: Ty            -- A: a base type, or a nullary `data` name
  , omTo   :: Ty            -- B: any type
  , omVia  :: String        -- c : A ⇒ B
  , omBack :: Maybe String  -- r : B ⇒ A, if a retraction was declared
  } deriving (Eq, Show)

-- How the object map READS, for a message: `Int ↦ Mod7 via reduce`.
showObjMap :: ObjMap -> String
showObjMap om = show (omFrom om) ++ " ↦ " ++ show (omTo om)
             ++ " via " ++ omVia om
             ++ maybe "" (", " ++) (omBack om)

-- ...and the substitution itself, structural and total.  Nothing here
-- is a type-level function: `A := B` under every constructor the type
-- language has, so `List(Int)` is `List(Mod7)` and `Fn⟨Int ⇒ Int⟩` is
-- `Fn⟨Mod7 ⇒ Mod7⟩` with no rule of their own.
objTy :: ObjMap -> Ty -> Ty
objTy om t | t == omFrom om = omTo om
objTy om (TFn arr)     = TFn (objArrow om arr)
objTy om (TSum row)    = TSum (objRow om row)
objTy om (TData n as)  = TData n (map (objStack om) as)
objTy _  t             = t

objStack :: ObjMap -> SType -> SType
objStack _  SEnd          = SEnd
objStack _  v@(STail _)   = v
objStack om (SCons t r)   = SCons (objTy om t) (objStack om r)
objStack om (SExp b e r)  = SExp (objStack om b) e (objStack om r)

objRow :: ObjMap -> SumRow -> SumRow
objRow _  RNil          = RNil
objRow _  v@(RTail _)   = v
objRow om (RCons st r)  = RCons (objStack om st) (objRow om r)

objArrow :: ObjMap -> Arrow -> Arrow
objArrow om (Arrow i o e) = Arrow (objStack om i) (objStack om o) e

-- Does an arrow MENTION A?  This is the whole of the type-directed
-- refusal: a word whose scheme does not name A is left alone (the
-- functor is the identity off A), and one that does needs an image, a
-- body to unfold, or a conjugation.
mentionsTy :: Ty -> Arrow -> Bool
mentionsTy a (Arrow i o _) = inS i || inS o
  where
    inS SEnd         = False
    inS (STail _)    = False
    inS (SCons t r)  = inT t || inS r
    inS (SExp b _ r) = inS b || inS r
    inT t | t == a   = True
    inT (TFn arr)    = mentionsTy a arr
    inT (TSum row)   = inR row
    inT (TData _ as) = any inS as
    inT _            = False
    inR RNil         = False
    inR (RTail _)    = False
    inR (RCons st r) = inS st || inR r

-- A MODEL fills a theory's slots.  Each binding becomes an ordinary
-- def named `Inst#slot`, so resolution is a renaming at elaboration —
-- once per scope, never a dictionary per call.
data Instance = Instance
  { inName     :: String
  , inTheory   :: String
  , inArgs     :: [InstArg]
  , inBindings :: [(String, String)]  -- slot, program source
  , inParams   :: [ModelParam]
      -- A MODEL PARAMETERIZED BY A MODEL (2026-09-15).  `model Fwd(R :
      -- Smooth(a, g)) : Smooth(Dual(a), a)` is not one model but a
      -- FAMILY — a functor Mod(Smooth) → Mod(Smooth) — and this list is
      -- its parameters.  Empty for every ordinary model, which is what
      -- makes the clause optional rather than a second kind of head.
  , inObjMap   :: [ObjMap]
      -- ...and the OBJECT MAP clause, the head's third (stage 7c).  A
      -- model is a presentation interpreted in a category: an object map
      -- and an image for each generator.  A model that carries `[]` here
      -- is the identity-object-map case — every model before 2026-09-17,
      -- and every model of a theory still, because an object map is a
      -- `Base` model's clause.
  , inScope    :: [String]
      -- The models whose slot names this model's BODIES are written in.
      -- Ordinary model: `[]`, meaning its own (a slot body may call a
      -- sibling slot).  A family instance: the argument model, because a
      -- family's bodies are TEMPLATES over the parameter's theory.
  } deriving (Eq, Show)

-- One parameter of a parameterized model: a name, the theory its
-- argument must model, and BINDERS for that argument's own theory
-- arguments — `R : Smooth(a, g)` names R's carrier `a` and R's exit
-- type `g`, which the head then uses to write its own (`Smooth(Dual(a),
-- a)`).  Substitution, not a type-level function: at `with Fwd(Floats)`
-- the binders take Floats' arguments and the head is read off.
data ModelParam = ModelParam
  { mpTheory  :: String
  , mpBinders :: [TyParam]
  } deriving (Eq, Show)

-- A model APPLICATION as it is written: `Floats`, `Fwd(Floats)`,
-- `Fwd(Fwd(Floats))`.  It is also the generated model's NAME — the one
-- spelling, so a transformation can name it and a receipt can print it.
data ModelApp = ModelApp String [ModelApp]
  deriving (Eq, Show)

renderModelApp :: ModelApp -> String
renderModelApp (ModelApp n []) = n
renderModelApp (ModelApp n as) =
  n ++ "(" ++ intercalate ", " (map renderModelApp as) ++ ")"

-- every application inside one, deepest first: `Fwd(Fwd(Floats))` needs
-- `Fwd(Floats)` generated before it, and this is that order
appClosure :: ModelApp -> [ModelApp]
appClosure a@(ModelApp _ as) = concatMap appClosure as ++ [a]

-- A model's argument, read at the KIND the theory's parameter
-- declares.  A wire or `...` parameter takes a type expression; a
-- constructor parameter takes the NAME of a declared data type — a
-- name, never a type, because `k(a, b)` is applied inside the slot and
-- the application is performed by substitution at the model.
data InstArg = IAStack SType | IACon String
  deriving (Eq, Show)

-- A MODEL THAT TRANSPORTS.  `model Circuits : Arrow(Circuit)` is an
-- ordinary model; what makes `with Circuits` take over `;` is the SHAPE
-- of the theory it models — a hom-object `k(_, _)` and slots declared
-- at the three shapes below.  The model's own name is then a LABEL
-- WITH A CARRIER: `with Circuits` mints `Circuits` exactly as any
-- functor scope does, and the carrier `Circuit(a, b)` is an ordinary
-- data type the display folds against the label.
--
-- Nothing here is a name convention.  `arrC`/`compC` are what
-- `examples/circuits.braid` happens to call its slots; what the
-- elaborator reads is the DECLARED arrow of each slot, which is a
-- written type (invariant five).
data Transport = Transport
  { tpName     :: String          -- the model, which is also its label
  , tpTheory   :: String          -- the theory it models
  , tpCarrier  :: String          -- the hom-object's constructor
  , tpCompose  :: Maybe String    -- k(a, b) k(b, c) ⇒ k(a, c)
  , tpEmbed    :: Maybe String    -- Fn⟨ρ ⇒ σ⟩ ⇒ k(ρ, σ)
  , tpExits    :: [String]        -- slots taking the carrier, returning base
  , tpEnters   :: [String]        -- slots building a carrier out of base alone
  , tpResource :: Maybe String    -- REPRESENTABLE at a resource wire
                                  -- (stage 7b): the carrier's body is
                                  -- `Fn\10216E \961 \8658 E \963\10217` for a declared
                                  -- `resource E` that is this model's
                                  -- own name.  Then the fibre's
                                  -- hom-object IS an object of the
                                  -- base, `embed` is `_`-padding and
                                  -- `compose` is `;`, so transport
                                  -- FUSES to what the routing pass
                                  -- already writes (design-7b.md §3.2).
  , tpRead     :: [(String, String, Maybe Arrow)]
                                  -- THE READER (stage 9, 2026-09-21):
                                  -- base atom -> slot, with the arrow
                                  -- that atom must have in the base when
                                  -- the slot is an ENTRY (`• ⇒ k(ρ, σ)`
                                  -- reads as `ρ ⇒ σ`), and `Nothing`
                                  -- when it is a WHISKERING, which takes
                                  -- a carrier and gives one back.  The
                                  -- theory's base spellings, inverted.
                                  -- See `readTransport`.
  } deriving (Eq, Show)

-- the two levels `with M` needs, and the message when one is missing.
-- A READER is the third: `embed` on a subcategory (stage 9).
tpTransports :: Transport -> Bool
tpTransports tp =
  isJust (tpCompose tp) && (isJust (tpEmbed tp) || not (null (tpRead tp)))

-- NOT `#`: that starts a comment, so a generated name using it would be
-- eaten by the lexer the moment it appeared in emitted source.
slotDefName :: String -> String -> String
slotDefName inst slot = inst ++ "@" ++ slot

lawDefName :: String -> String -> String
lawDefName inst lawNm = inst ++ "@law@" ++ lawNm

-- a generated law def, and the (model, law) it came from
-- A REGISTERED CHECK (stage 8).  `test squares = \8230` becomes a def
-- in the compiler's `@` namespace, which source may not write, and
-- `runModule` runs it at module start exactly as it runs a law.
testDefName :: String -> String
testDefName n = "test@" ++ n

testParts :: String -> Maybe String
testParts = stripPrefix "test@"

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

-- WHAT REFLECTION READS (2026-09-16).  The reflection words answer with
-- facts the checker already has, so the runtime has to be handed the
-- same four tables the checker holds: the environment (every word's
-- scheme), the `data`/`resource` declarations, the `type` aliases (the
-- display folds against them, exactly as the REPL does) and the
-- theories.  It travels where `Env` alone used to, which is why it is
-- one record rather than four arguments — a prim that reads a
-- declaration is reading the prefix scope, and the prefix scope is one
-- thing.
data RCtx = RCtx
  { rcEnv      :: Env
  , rcDatas    :: [DataDecl]
  , rcAliases  :: [Alias]
  , rcTheories :: [Theory]
  } deriving (Eq, Show)

-- the context a caller who has only an environment can offer: nothing
-- is declared, so `declOf` answers "not declared" and `typeOfWord`
-- still works
rctxOf :: Env -> RCtx
rctxOf env = RCtx env [] [] []

dataSig :: DataDecl -> (String, [TyParam])
dataSig d = (dName d, dParams d)

-- The schemes and runtime entries a data declaration contributes:
--   Name   : ∀params. body ⇒ Name(params)      (roll)
--   unName : ∀params. Name(params) ⇒ body      (unroll)
dataDeclArtifacts :: DataDecl
                  -> ([(String, Scheme)], [(String, (Int, Bool, Term))])
dataDeclArtifacts d =
  ( [ (dName d,          Forall tvs svs rvs nvs [] [] (Arrow bodyStack namedStack effPure))
    , ("un" ++ dName d,  Forall tvs svs rvs nvs [] [] (Arrow namedStack bodyStack effPure)) ]
      ++ mergeSchemes ++ foldSchemes ++ map fst fieldArts
  , [ (dName d,         (rollArity, rollOpen, rollTerm))
    , ("un" ++ dName d, (1, False, unrollTerm)) ]
      ++ mergeRuns ++ foldRuns ++ map snd fieldArts )
  where
    fieldArts  = dataFieldArtifacts d
    (foldSchemes, foldRuns) =
      case dataFoldArtifact d of
        Just (fn, fsc, frun, _) -> ([(fn, fsc)], [(fn, frun)])
        Nothing                 -> ([], [])
    ps         = dParams d
    tvs        = [ tv | PWire tv  <- ps ]
    svs        = [ sv | PStack sv <- ps ]
    rvs        = [ rv | PRow   rv <- ps ]
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
            , Forall [] [SV "ρ"] [] [] [] []
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
          (st, closedArity st, Prim "alt1", Prim "merge")
        _ ->
          (SCons (dBody d) SEnd, 1, Prim "_", Prim "_")
    -- (rollOpen marks splice-shaped field stacks segment-consuming)

-- NAMED FIELDS, as words (2026-09-14).  One PROJECTION per name a
-- single-alternative declaration wrote:
--
--   data Trade = (sym: Str, px: Float, qty: Int)
--     sym : Trade ⇒ Str      px : Trade ⇒ Float      qty : Trade ⇒ Int
--
-- Each is `unTrade` and then the tensor stage that keeps one wire —
-- ordinary wiring, compiler-written exactly as `unTrade` and
-- `foldTrade` are, so it is an ordinary word: it shows in `:defs`, it
-- reflects, it can be quoted and handed to `map`.  Nothing about the
-- TYPE changes; the positional door and the destructuring binder are
-- untouched, and a field name is a WORD rather than a piece of the
-- type, which is what lets a frame's column names be ordinary
-- definitions (MANUAL §5, §12).
dataFieldArtifacts :: DataDecl
                   -> [((String, Scheme), (String, (Int, Bool, Term)))]
dataFieldArtifacts d =
  [ ( (f, Forall tvs svs rvs nvs [] [] (arrPure namedStack (SCons t SEnd)))
    , (f, (1, False, Seq 0 (Prim "merge") (Tensor (keepOnly i)))) )
  | (i, f, t) <- zip3 [0 :: Int ..] (dFields d) elems ]
  where
    ps         = dParams d
    tvs        = [ tv | PWire tv  <- ps ]
    svs        = [ sv | PStack sv <- ps ]
    rvs        = [ rv | PRow   rv <- ps ]
    nvs        = [ nv | PWidth nv <- ps ]
    namedStack = SCons (TData (dName d) (map paramStack ps)) SEnd
    elems      = case dBody d of
                   TSum (RCons st RNil) -> stackElems st
                   t                    -> [t]
    n          = length elems
    keepOnly i = [ if j == i then Prim "_" else Prim "drop"
                 | j <- [0 .. n - 1] ]
    stackElems (SCons t st) = t : stackElems st
    stackElems _            = []

-- Generated eliminator: definition by points — and, since 5a½, a
-- STRUCTURAL RECURSOR rather than a definition that called itself.  For
--   type Name(ps) = (alt1 | … | altk)
-- the declaration contributes
--   foldName : Fn⟨Σ1 ⇒ R⟩ … Fn⟨Σk ⇒ R⟩ Name(ps) ⇒ R
-- where Σi is alternative i's payload with every recursive slot (an
-- element whose type is exactly Name(ps)) already folded and moved to
-- the FRONT, so a case sees FOLDED-then-payload however the alternative
-- was written.  Recursion nested under another constructor (List(Rose(a)))
-- is not a slot and is passed to the case untransformed; a resource is
-- unrolled, not eliminated by points, and gets no recursor.
--
-- The recursor is a BUILTIN — a runtime primitive carrying the shape it
-- was derived from — not a def and not a `fix` term.  That is the whole
-- point: it descends on a strictly smaller value at every step, so it
-- terminates by construction on finite data, and `foldName` (hence the
-- prelude's `fold`, `map`, `filter`, …) is not an unbounded site.
--
-- A payload of no closed elements (`•`, or an alternative that is a bare
-- stack parameter as in `data Box(…) = (…)`) hands the case the whole
-- bundle; that is what `fi … >> ev` did in the source generator.
dataFoldArtifact :: DataDecl
                 -> Maybe (String, Scheme, (Int, Bool, Term), String)
dataFoldArtifact d
  | dResource d = Nothing
  | otherwise =
      case dBody d of
        TSum row -> do
          alts <- rowAlts row
          if null alts then Nothing else Just ()   -- no alternatives, no points
          let fname    = "fold" ++ dName d
              selfTy   = TData (dName d) (map paramStack (dParams d))
              tvs0     = [ tv | PWire tv  <- dParams d ]
              svs0     = [ sv | PStack sv <- dParams d ]
              rvs0     = [ rv | PRow   rv <- dParams d ]
              nvs0     = [ nv | PWidth nv <- dParams d ]
              payloads = map stackElems alts
              flagsOf  = map (== selfTy)
              specs    = [ if null pl then Nothing else Just (flagsOf pl)
                         | pl <- payloads ]
              -- reordered: recursive slots first, source order within
              slotsOf pl = [ t | t <- pl, t == selfTy ]
                             ++ [ t | t <- pl, t /= selfTy ]
              -- every slot but the last is passed over by a `_` in the
              -- generated spine, so it must be exactly one wire.  The
              -- result is therefore a WIRE as soon as some alternative
              -- has a recursive slot that is not its only slot; with no
              -- such alternative the fold may return a whole stack.
              oneWire = or [ any (== selfTy) pl && length pl >= 2
                           | pl <- payloads ]
              resTy    = TVarTy resTV
              -- the fold's own result variable, named apart from the
              -- declaration's parameters so a raw scheme reads cleanly
              fresh b used = head [ c | c <- b : [ b ++ show i
                                                 | i <- [1 :: Int ..] ]
                                      , c `notElem` used ]
              resTV    = TV (fresh "β" [ n | PWire  (TV n) <- dParams d ])
              resSV    = SV (fresh "ρ" [ n | PStack (SV n) <- dParams d ])
              resStack | oneWire   = SCons resTy SEnd
                       | otherwise = STail resSV
              eps      = EV "ε"
              arrE i o = Arrow i o (Eff S.empty (Just eps))
              sigma (alt, pl)
                | null pl   = alt
                | otherwise = go (slotsOf pl)
                where
                  go []       = SEnd            -- unreachable (pl non-null)
                  go [t] | t == selfTy = resStack
                         | otherwise   = SCons t SEnd
                  go (t : ts) = SCons (if t == selfTy then resTy else t)
                                      (go ts)
              sigmas  = map sigma (zip alts payloads)
              inStack = foldr (\sg rest -> SCons (TFn (arrE sg resStack)) rest)
                              (SCons selfTy SEnd) sigmas
              sc = Forall (tvs0 ++ [ resTV | oneWire ])
                          (svs0 ++ [ resSV | not oneWire ])
                          rvs0 nvs0 [eps] []
                          (arrE inStack resStack)
              doc = "definition by points: one quoted case per constructor of "
                      ++ dName d ++ ", recursive slots pre-folded"
          pure ( fname, sc
               , (length specs + 1, False, Prim (foldPrimName specs))
               , doc )
        _ -> Nothing
  where
    rowAlts RNil         = Just []
    rowAlts (RTail _)    = Nothing
    rowAlts (RCons st r) = (st :) <$> rowAlts r
    stackElems (SCons t st) = t : stackElems st
    stackElems _            = []

-- The recursor's shape, carried in the name of the prim that runs it:
-- one entry per alternative, `*` for "hand the case the whole bundle",
-- otherwise one character per payload slot, `r` for a recursive slot.
foldPrimName :: [Maybe [Bool]] -> String
foldPrimName specs = "#fold:" ++ intercalate "," (map enc specs)
  where
    enc Nothing   = "*"
    enc (Just fs) = [ if f then 'r' else 'x' | f <- fs ]

-- distK, the OPEN distributivity generator (stage 5a⅞).  Abstraction
-- elimination needs `P (ρ₁ | … | ρₖ | σ) ⇒ (P ρ₁ | … | P ρₖ | σ)` for the
-- row it is actually looking at, and that is not one word: the arity of
-- a WRITTEN row is not something polymorphism reaches, and the residual
-- σ cannot be distributed into at all (you cannot write a handler for a
-- track you cannot name).  So it is a family, synthesized per K exactly
-- like `#fold:` — and a GENERATOR, not a derivation: the prelude's
-- `dist2`/`dist3` are the CLOSED models, proved through `capture`,
-- and they are what `theory Distributive` runs.
-- The name is unspellable (`#` opens a comment), so nothing can shadow
-- it — the same protection `capture`/`dist2` need `elimEmits` for.
distPrimName :: Int -> String
distPrimName k = "#dist:" ++ show k

distPrimArity :: String -> Maybe Int
distPrimArity nm
  | ("#dist:", ds@(_ : _)) <- splitAt 6 nm
  , all isDigit ds
  , k >= 1 = Just k
  | otherwise = Nothing
  where k = read (drop 6 nm) :: Int

foldPrimSpec :: String -> Maybe [Maybe [Bool]]
foldPrimSpec nm
  | ("#fold:", rest) <- splitAt 6 nm = mapM dec (commaParts rest)
  | otherwise                        = Nothing
  where
    dec "*" = Just Nothing
    dec cs | not (null cs), all (`elem` "rx") cs = Just (Just (map (== 'r') cs))
           | otherwise                           = Nothing
    commaParts str = case break (== ',') str of
      (a, [])       -> [a]
      (a, _ : rest) -> a : commaParts rest

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

-- STRICT POSITIVITY (2026-09-18).  A `data` body may mention the name
-- it is declaring, but never to the LEFT of an arrow.  A negative
-- self-occurrence is a second door into general recursion, and one
-- with no guard on it: `data Rec(a, b) = Fn⟨Rec(a, b) ⇒ Fn⟨a ⇒ b⟩⟩`
-- makes the typed Z combinator writable, so `fac` types `• ⇒
-- Fn⟨Int ⇒ Int⟩` — PURE — and runs.  `#fix` is the other door and it
-- is guarded: it is unspellable, `with Recursive` is the only thing
-- that opens it, and the knot it ties mints `=Recursive>`.  One door
-- beats two, so this one is closed rather than made to mint: with it
-- shut, provenance and the semantic property coincide again, which is
-- what MANUAL §8's claim rests on.
--
-- Codata stays legal: an occurrence in an arrow's OUTPUT is positive
-- (`data Circuit(a…, b…) = Fn⟨Box(a) =Recursive> Box(b) Circuit(a, b)⟩`),
-- and so is one under no arrow at all (`List`, `Tree`).
--
-- Polarity is tracked THROUGH other declared types, by their
-- parameters' variance: `data Neg(a) = Fn⟨a ⇒ Int⟩` makes `a`
-- negative, so `data Bad = Neg(Bad)` is refused even though `Bad`
-- reads as an argument.  `type` aliases need no separate treatment —
-- they are expanded by the parser, so the body checked here is already
-- alias-free.

-- | Which polarities a value substituted for each parameter can reach:
-- (can land positive, can land negative).
type ParamVariance = [(Bool, Bool)]

-- | Every name a type body mentions, tagged with the polarity it sits
-- at: `Left` a declared type's name, `Right` a parameter's.  True is
-- positive — right of every arrow it is under.
polarityOccs :: (String -> ParamVariance) -> Bool -> Ty
             -> [(Either String String, Bool)]
polarityOccs var = goT
  where
    goT p (TVarTy (TV a))     = [(Right a, p)]
    goT p (TFn (Arrow i o _)) = goS (not p) i ++ goS p o
    goT p (TSum r)            = goR p r
    goT p (TData m as)        =
      (Left m, p)
        : concat [ occ
                 | (a, (pos, neg)) <- zip as (var m ++ repeat (True, True))
                 , occ <- [ goS p a | pos ] ++ [ goS (not p) a | neg ] ]
    goT _ _                   = []
    goR p (RCons st r)        = goS p st ++ goR p r
    goR p (RTail (RV v))      = [(Right v, p)]
    goR _ RNil                = []
    goS p (SCons t st)        = goT p t ++ goS p st
    goS p (STail (SV s))      = [(Right s, p)]
    goS p (SExp b _ r)        = goS p b ++ goS p r
    goS _ SEnd                = []

-- | Each declared type's parameter variances, to a fixed point.  The
-- start is "reaches nothing" and each pass can only add, so it
-- terminates; the pass is needed because a type's variance can depend
-- on its own (`Circuit`'s `a` is negative only through `Circuit`).
paramVariances :: [DataDecl] -> M.Map String ParamVariance
paramVariances ds = settle (M.fromList [ (dName d, blank d) | d <- ds ])
  where
    blank d = [ (False, False) | _ <- dParams d ]
    settle m = let m' = pass m in if m' == m then m else settle m'
    pass m = M.fromList [ (dName d, varianceOf m d) | d <- ds ]
    varianceOf m d =
      [ (any (hit q True) occs, any (hit q False) occs)
      | q <- map pName (dParams d) ]
      where
        occs = polarityOccs (look m) True (dBody d)
        hit q b (Right n, p) = n == q && p == b
        hit _ _ _            = False
    look m n = M.findWithDefault (repeat (True, True)) n m

-- | The refusal.  `d` is the declaration being added; `ds` is what is
-- already in scope (`d` shadows an earlier one of its name).
checkPositive :: [DataDecl] -> DataDecl -> Either String ()
checkPositive ds d
  | any neg (polarityOccs look True (dBody d)) =
      Left $ "Type " ++ n ++ ": `" ++ n ++ "` occurs to the LEFT of an "
          ++ "arrow in its own declaration, which admits general "
          ++ "recursion with no `" ++ recLabel ++ "` on the arrow.  "
          ++ "Recursion enters through `with " ++ recLabel
          ++ "` and nowhere else (MANUAL §8).  An occurrence in an "
          ++ "arrow's OUTPUT is codata and is fine (`data Stream(a) = "
          ++ "(a Fn⟨• =" ++ recLabel ++ "> Stream(a)⟩)`); if what you "
          ++ "want is a self-applying value, it is not expressible."
  | otherwise = Right ()
  where
    n    = dName d
    vs   = paramVariances (d : filter ((/= n) . dName) ds)
    look m = M.findWithDefault (repeat (True, True)) m vs
    neg (Left m, p) = m == n && not p
    neg _           = False

lookupAlias :: String -> [Alias] -> Maybe Alias
lookupAlias n = go
  where
    go [] = Nothing
    go (al : rest) | aName al == n = Just al
                   | otherwise     = go rest

-- the type names that are always in scope and are never variables
builtinTyNames :: [String]
builtinTyNames = ["Int", "Str", "Sym", "Fn", "Fin"] ++ terminalSpellings

-- The empty stack, both ways of typing it (2026-09-20).  `•` is the one
-- name in the language that needed a character most keyboards cannot
-- produce; every other glyph already had an ASCII spelling (`Fn(Σ -> Θ)`
-- for `Fn⟨Σ ⇒ Θ⟩`, `->!` for `=IO>`, `^n` for the superscripts).  The
-- word is `one`, so the type and the WORD for its identity read the
-- same: `Fn(one -> a)` is `Fn⟨• ⇒ a⟩`.  Input only — the display stays
-- `•`, exactly as `->` displays as `⇒`.
terminalSpellings :: [String]
terminalSpellings = ["•", "one"]

-- Parse a whole `type …` declaration line (aliases and data types in
-- scope are needed to resolve references in the RHS; the declared name
-- itself is in scope for self-reference, which makes the declaration a
-- nominal data type rather than a transparent alias).
-- `theory Name(params)` + indented `slot : Σ ⇒ Θ` and `law nm = prog`
parseTheory :: [Alias] -> [(String, [TyParam])] -> String -> [String]
            -> Either String Theory
parseTheory aliases dataSigs header body = do
  (name, params, ext) <- parseHead
  entries <- mapM (parseEntry params) (filter (not . blank) body)
  let slots = [ (n, a) | Left  (n, a, _) <- entries ]
      laws  = [ e      | Right e         <- entries ]
      reads' = [ (n, w) | Left (n, _, Just w) <- entries ]
  case slots of
    [] -> Left $ "theory " ++ name ++ " declares no operations"
    _  -> Right ()
  -- THE TABLE IS INJECTIVE ON GENERATORS, which is what makes it
  -- invertible at all: `read : B ⇀ B[T]` is a model read BACKWARDS, and
  -- two slots spelled the same way would give one base atom two images.
  case [ w | (_, w) <- reads', length [ () | (_, w') <- reads', w' == w ] > 1 ] of
    (w : _) -> Left $ "theory " ++ name ++ ": two slots are spelled `" ++ w
                   ++ "` in the base, and the base spelling is READ "
                   ++ "BACKWARDS — one atom, one slot, or `with` a model "
                   ++ "of " ++ name ++ " could not say which generator `"
                   ++ w ++ "` is"
    []      -> Right ()
  pure (Theory name params slots laws ext reads')
  where
    blank l = all isSpace (takeWhile (/= '#') l)
    parseHead = do
      -- the header carries the block's `=`; it is punctuation, not a name
      toks <- normalizeToks <$> tokenize (takeWhile (/= '=') header)
      case toks of
        (TokIdent "theory" : TokIdent n : TokLParen : rest) -> do
          (ps, after) <- theoryParams rest
          (,,) n ps <$> extClause after
        (TokIdent "theory" : TokIdent n : rest) ->
          (,,) n [] <$> extClause rest
        _ -> Left $ "Malformed theory declaration: " ++ header
    -- `in D` — one clause, at most one theory, because a presentation
    -- extends by inclusion and two inclusions want a pushout nobody
    -- asked for yet.  A theory that extends another is a presentation
    -- OF that doctrine's shape: membership, so `in` (2026-09-16).
    extClause []                                  = Right Nothing
    extClause [TokIdent "in", TokIdent d]         = Right (Just d)
    extClause (TokIdent "over" : _) = Left $
      "`over` is gone since 2026-09-16: a theory extending another is "
        ++ "MEMBERSHIP — write `theory " ++ takeWhile (/= '=') header
        ++ "` with `in <Theory>` where the `over` is (MANUAL §8)"
    extClause _ = Left $
      "Malformed theory declaration: after the parameters a theory head "
        ++ "takes at most `in <Theory>` (this theory's slots that the "
        ++ "named one also declares are ITS slots, at its shape, and its "
        ++ "laws are this theory's): " ++ header
    -- A bare name is a WIRE, `...` a STACK, and `k(..., ...)` a type
    -- CONSTRUCTOR — the arity written as one `...` per argument, because
    -- the two bare readings are already taken and a kind that is
    -- invisible is a kind that is guessed.  Every argument of a
    -- constructor parameter is a STACK (2026-09-16): a hom-object
    -- `k(ρ, σ)` names a whole side of a diagram, not one wire, which is
    -- what deleted the pairing from the Doctrine.
    theoryParams (TokIdent p : TokLParen : r) = do
      (ar, r1) <- conArity [] r
      case r1 of
        (TokComma : r2)   -> first' (PCon p ar :) <$> theoryParams r2
        (TokRParen : r2)  -> Right ([PCon p ar], r2)
        _ -> Left "Malformed theory parameter list"
    theoryParams (TokIdent p : TokComma : r) =
      first' (PWire (TV p) :) <$> theoryParams r
    theoryParams (TokIdent p : TokRParen : r) = Right ([PWire (TV p)], r)
    theoryParams (TokEllipsis : TokRParen : r) = Right ([PStack (SV "s")], r)
    theoryParams (TokEllipsis : TokComma : TokDashes : TokRParen : r) =
      Right ([PStack (SV "s"), PRow (RV "r")], r)
    theoryParams (TokDashes : TokRParen : r)  = Right ([PRow (RV "r")], r)
    theoryParams _ = Left "Malformed theory parameter list"

    first' f (xs, r) = (f xs, r)

    -- `_` and `...`, one per argument: the KINDS of a constructor
    -- parameter's arguments.  `_` is a wire, `...` a stack — the same
    -- two readings a declaration's own parameter list has — so a
    -- hom-object over stacks is `k(..., ...)` and a parameterized exit
    -- over one wire is still `d(_)` (2026-09-16).
    conArity ks (TokEllipsis : TokComma : r)  = conArity (ks ++ [True]) r
    conArity ks (TokEllipsis : TokRParen : r) = Right (ks ++ [True], r)
    conArity ks (TokIdent "_" : TokComma : r)  = conArity (ks ++ [False]) r
    conArity ks (TokIdent "_" : TokRParen : r) = Right (ks ++ [False], r)
    conArity _ _ = Left ("A constructor parameter's kind is written with "
                      ++ "one mark per argument — `_` for a wire, `...` "
                      ++ "for a stack: k(..., ...), d(_)")

    -- `law nm = program` | `slot : Σ ⇒ Θ` | `slot : Σ ⇒ Θ = <base word>`
    --
    -- THE BASE SPELLING (stage 9, 2026-09-21).  A generator of a theory
    -- may say how it is written in the AMBIENT presentation, and that
    -- table is what makes `embed` definable on a SUBCATEGORY: see
    -- `readTransport`.  It is split on ` = ` with spaces, because `=`
    -- with none is part of a labelled arrow (`=IO>`).
    parseEntry params l =
      case words l of
        ("law" : nm : "=" : _) ->
          Right (Right (nm, drop 1 (dropWhile (/= '=') l)))
        _ -> case break (== ':') l of
          (_, ':' : sig0) | ';' `elem` sig0 -> Left (separatorErr "slots")
          (lhs, ':' : sig0)
            | [nm] <- words lhs -> do
                (sig, spelled) <- splitSpelling nm sig0
                -- SLOT-LOCAL VARIABLES.  A slot may name variables the
                -- theory does not declare (`thenP : k(a,b) k(b,c) ⇒
                -- k(a,c)` needs `a b c`), and each is local to its own
                -- slot: the slot's arrow is generalized over them, which
                -- `declaredSlots` already does and which `checkInstance`
                -- already reads by subsumption.  Generalize-at-parse,
                -- not a checker change.  Any lowercase name that is not
                -- a theory parameter and not a type in scope is such a
                -- variable; a `...` with no stack parameter to attach to
                -- is a slot-local stack.
                locals <- slotLocals params sig
                ty <- parseTyBody aliases dataSigs (params ++ locals)
                                  ("Fn⟨" ++ sig ++ "⟩")
                case ty of
                  TFn arr -> Right (Left (nm, arr, spelled))
                  _ -> Left $ "theory: slot '" ++ nm
                           ++ "' needs a signature like `Σ ⇒ Θ`"
          _ -> Left $ "Malformed theory entry: " ++ dropWhile isSpace l

    -- ` = <word>` after a slot's signature: its spelling in the base.
    splitSpelling nm sig = case breakOn " = " sig of
      Nothing        -> Right (sig, Nothing)
      Just (s, rest) -> case words (takeWhile (/= '#') rest) of
        [w] -> Right (s, Just w)
        _   -> Left $ "theory: slot '" ++ nm ++ "' is spelled `"
                   ++ trimSpace rest ++ "` in the base, and a base "
                   ++ "spelling is ONE WORD — a generator of the ambient "
                   ++ "presentation, which is what the subcategory is "
                   ++ "generated by.  A composite is not a generator."

    breakOn sep s = go "" s
      where
        go _   []          = Nothing
        go acc r@(c : cs)
          | sep `isPrefixOf` r = Just (reverse acc, drop (length sep) r)
          | otherwise          = go (c : acc) cs

    -- the variables a slot introduces on its own, in order of first use
    slotLocals params sig = do
      toks <- tokenize sig
      let known n = isJust (lookupParam n params)
                 || isJust (lookup n dataSigs)
                 || isJust (lookupAlias n aliases)
                 || n `elem` builtinTyNames
          fresh acc (TokIdent n : rest)
            | not (null n), isLower (head n), not (known n)
            , n `notElem` acc = fresh (acc ++ [n]) rest
          fresh acc (_ : rest) = fresh acc rest
          fresh acc []         = acc
          -- A slot-local name used as an ARGUMENT OF A CONSTRUCTOR
          -- PARAMETER is a STACK, because every such argument is one
          -- (2026-09-16): `compose : k(a, b) k(b, c) ⇒ k(a, c)` names
          -- three stacks, and `embed : Fn⟨a ⇒ b⟩ ⇒ k(a, b)` names the
          -- same two on both sides of the arrow.  The kind is declared
          -- once, in the theory head, and read off here — nothing is
          -- annotated twice.
          -- ...and it is the LAST element of that argument that is the
          -- stack: `under : k(a, b) => k(c a, c b)` names a WIRE `c`
          -- riding under a STACK `a`, because a stack variable can only
          -- sit in tail position (a splice is unspellable).
          cons  = [ (pName q, ks) | q@(PCon _ ks) <- params ]
          inCon = nub (scan toks)
          scan (TokIdent n : TokLParen : rest)
            | Just ks <- lookup n cons
            , (grps, rest') <- argGroups rest =
                concat (zipWith stackArgNames (ks ++ repeat False) grps)
                  ++ concatMap scan grps ++ scan rest'
          scan (_ : rest) = scan rest
          scan []         = []
          stackArgNames isStk grp =
            [ n | isStk, (TokIdent n : _) <- [reverse grp]
                , not (null n), isLower (head n) ]
          -- the top-level comma-separated groups of an argument list,
          -- and what follows its closing paren
          argGroups = go (0 :: Int) [] []
            where
              go _ grp acc []                 = (reverse (reverse grp : acc), [])
              go 0 grp acc (TokRParen : r)    = (reverse (reverse grp : acc), r)
              go 0 grp acc (TokComma : r)     = go 0 [] (reverse grp : acc) r
              go d grp acc (t : r)
                | t == TokLParen || t == TokLAngle = go (d + 1) (t : grp) acc r
                | t == TokRParen || t == TokRAngle = go (d - 1) (t : grp) acc r
                | otherwise                        = go d (t : grp) acc r
          names = fresh [] toks
          wires = [ PWire (TV n) | n <- names, n `notElem` inCon ]
          stacks = [ PStack (SV n) | n <- names, n `elem` inCon ]
          -- one slot-local stack for the whole slot, named so that no
          -- source identifier can shadow it (`…` lexes as `...`)
          stk = [ PStack (SV "…")
                | TokEllipsis `elem` toks
                , not (any isStackParam params) ]
      pure (wires ++ stacks ++ stk)

-- `model Name : Theory(args)` + indented `slot = program`
-- Split a type-argument list on commas that are not nested inside
-- `(…)` or `Fn⟨…⟩`, dropping the trailing `)` that closed the list.
splitTopCommas :: String -> [String]
splitTopCommas = go 0 ""
  where
    go :: Int -> String -> String -> [String]
    go _ acc []                     = [reverse acc | not (blankStr acc)]
    go d acc (c : cs)
      | c `elem` ("(\10216" :: String) = go (d + 1) (c : acc) cs
      | c == ')' && d == 0          = [reverse acc | not (blankStr acc)]
      | c `elem` (")\10217" :: String) = go (d - 1) (c : acc) cs
      | c == ',' && d == 0          = reverse acc : go 0 "" cs
      | otherwise                   = go d (c : acc) cs
    blankStr = all isSpace

-- The arrow of the OBJECT MAP.  One glyph, and it is not `⇒`: `⇒` is
-- the arrow of every WRITTEN TYPE in Braid, and an object map is not a
-- type — it is a function on objects.  `↦` is the mathematician's
-- spelling for exactly that, the lexer already admits it as an ordinary
-- identity character, and nothing else in the language claims it.
mapsTo :: String
mapsTo = "↦"

-- `A ↦ B via c`, or `A ↦ B via c, r` — the object map clause, parsed
-- off the head's own text.  `A` is a NOMINAL name: a base type, or a
-- `data`/`type` name of arity zero.  Anything else would need the map
-- to be a type-level FUNCTION (what is `List(a) ↦ …` at an unknown
-- `a`?), and the whole reason substitution is principal is that it is
-- not one.
parseObjMap :: [Alias] -> [(String, [TyParam])] -> String -> String
            -> Either String ObjMap
parseObjMap aliases dataSigs nm src = do
  (lhs, rhs) <- case splitOnStr mapsTo src of
    [l, r] -> Right (l, r)
    _      -> Left $ here ++ "an object map is written `A " ++ mapsTo
                  ++ " B via c` (and `, r` for a retraction), not: "
                  ++ trimSpace src
  (bsrc, csrc) <- case breakWord "via" rhs of
    Just p  -> Right p
    Nothing -> Left $ here ++ "an object map needs `via`: `A " ++ mapsTo
                   ++ " B via c` names the image of the LITERAL FAMILY, "
                   ++ "the one generator class a table cannot name"
  a <- parseTyBody aliases dataSigs [] lhs
  b <- parseTyBody aliases dataSigs [] bsrc
  case a of
    TData _ (_ : _) -> Left (nominalErr lhs)
    TFn _           -> Left (nominalErr lhs)
    TSum _          -> Left (nominalErr lhs)
    TVarTy _        -> Left (nominalErr lhs)
    TFin _          -> Left (nominalErr lhs)
    _               -> Right ()
  if a == b
    then Left $ here ++ "`" ++ show a ++ " " ++ mapsTo ++ " " ++ show b
             ++ "` is the identity object map, which every model already "
             ++ "has: drop the clause"
    else Right ()
  case [ w | w <- splitTopCommas csrc, not (all isSpace w) ] of
    [c] | [c'] <- words c -> Right (ObjMap a b c' Nothing)
    [c, r] | [c'] <- words c, [r'] <- words r ->
      Right (ObjMap a b c' (Just r'))
    _ -> Left $ here ++ "`via` names the image of the literal family, and "
             ++ "optionally a RETRACTION beside it: `via c` or `via c, r` "
             ++ "— one word each, not: " ++ trimSpace csrc
  where
    here = "model " ++ nm ++ ": "
    nominalErr l = here ++ "`" ++ trimSpace l ++ "` is not a NOMINAL type: "
                ++ "an object map's source is a base type or a `data`/`type` "
                ++ "name of arity zero, because the map is the substitution "
                ++ "`A := B` and a parameterized source would make it a "
                ++ "type-level function"

-- split on a standalone word at paren depth zero: `Mm via toMm` is
-- (`Mm`, `toMm`), and a type named `viability` is left alone
breakWord :: String -> String -> Maybe (String, String)
breakWord w = go (0 :: Int) ""
  where
    go _ _   [] = Nothing
    go d acc cs@(c : rest)
      | d == 0, Just r <- atWord cs = Just (reverse acc, r)
      | c == '(' || c == '⟨'   = go (d + 1) (c : acc) rest
      | c == ')' || c == '⟩'   = go (d - 1) (c : acc) rest
      | otherwise                  = go d (c : acc) rest
    atWord cs = case stripPrefix w (dropWhile isSpace cs) of
      Just r@(c : _) | isSpace c, cs /= dropWhile isSpace cs -> Just r
      _                                                     -> Nothing

-- THE MODEL HEAD, ONE GRAMMAR (stage 7c, 2026-09-17).
--
--   model NAME [ ( PARAM ) ] in THEORY [ ( ARGS ) ] [ ( A ↦ B via c [, r] ) ]
--
-- Three optional clauses around one required one, and every kind of
-- model Braid has is a SETTING of them: a plain model writes the
-- arguments, a family writes the parameter, a `Base` model writes
-- neither, an object-mapped `Base` model writes the third.  The two
-- parenthesized clauses after the theory are told apart by CONTENT and
-- not by position: a group containing `↦` is the object map, and any
-- other group is the theory's arguments.  There is nothing to
-- disambiguate, because a type expression never contains `↦`.
parseModelHead :: [Alias] -> [(String, [TyParam])] -> [Theory] -> String
               -> Either String (String, [ModelParam], String, [InstArg], [ObjMap])
parseModelHead aliases dataSigs theories header = do
      let hdr = takeWhile (/= '=') (takeWhile (/= '#') header)
      after0 <- case stripWord "model" (dropWhile isSpace hdr) of
        Just r  -> Right r
        Nothing -> Left $ "Malformed model declaration: " ++ header
      let (nm, after1) = span isIdentish (dropWhile isSpace after0)
      (psrc, after2) <- case dropWhile isSpace after1 of
        ('(' : r) -> first' Just <$> balanced r
        r         -> Right (Nothing, r)
      ps <- maybe (Right []) (mapM (modelParam nm) . splitTopCommas') psrc
      case ps of
        (_ : _ : _) -> Left $ "model " ++ nm ++ ": a parameterized model "
                           ++ "takes ONE parameter — two would give one "
                           ++ "slot name two meanings inside a body, since "
                           ++ "a family's bodies are written in the "
                           ++ "parameter's vocabulary"
        _           -> Right ()
      case dropWhile isSpace after2 of
        rhs0 | Just rhs <- stripWord "in" (dropWhile isSpace rhs0)
             , not (null nm) -> do
          let (th, afterTh) = span (\c -> not (isSpace c) && c /= '(')
                                   (dropWhile isSpace rhs)
          grps <- groups (dropWhile isSpace afterTh)
          if null th then Left ("Malformed model head: " ++ header)
                     else Right ()
          let oms  = [ g | g <- grps, mapsTo `isInfixOf` g ]
              asrc = [ g | g <- grps, not (mapsTo `isInfixOf` g) ]
          case asrc of
            (_ : _ : _) -> Left $ "model " ++ nm ++ ": a head names its "
                               ++ "theory's arguments ONCE: `model " ++ nm
                               ++ " in " ++ th ++ "(…)`"
            _ -> Right ()
          case oms of
            (_ : _ : _) -> Left $ "model " ++ nm ++ ": a head carries ONE "
                               ++ "object map — a model sends each object to "
                               ++ "one thing, and two clauses would be two "
                               ++ "functors"
            _ -> Right ()
          om <- mapM (parseObjMap aliases dataSigs nm) oms
          args nm ps th (concatMap splitTopCommas asrc)
            >>= \as -> Right (nm, ps, th, as, om)
        (':' : _) -> Left $ "`:` types a slot and nothing else since "
                         ++ "2026-09-16: a model's head says which theory "
                         ++ "it interprets, which is MEMBERSHIP — write "
                         ++ "`model " ++ nm ++ " in <Theory>(…)` "
                         ++ "(MANUAL §8)"
        _ -> Left $ "Malformed model declaration: " ++ header
  where
    -- successive parenthesized clauses, in the order they were written
    groups s0 = case dropWhile isSpace s0 of
      ""        -> Right []
      ('(' : r) -> do (g, r') <- balanced r
                      (g :) <$> groups r'
      _         -> Left $ "Malformed model head: " ++ header

    stripWord w s0 = case splitAt (length w) s0 of
      (pre, r@(c : _)) | pre == w, isSpace c -> Just r
      _                                      -> Nothing

    -- the text up to the `)` that closes an already-opened `(`
    balanced = go (0 :: Int) ""
      where
        go _ _   []       = Left $ "Malformed model head: " ++ header
        go 0 acc (')':cs) = Right (reverse acc, cs)
        go d acc (c  :cs)
          | c == '('  = go (d + 1) (c : acc) cs
          | c == ')'  = go (d - 1) (c : acc) cs
          | otherwise = go d (c : acc) cs

    -- like `splitTopCommas`, but over text that is already unwrapped
    splitTopCommas' s0 = splitTopCommas (s0 ++ ")")

    -- `Smooth(a, _)` — the parameter's THEORY and the names it gives
    -- that theory's arguments, so the head can write its own.  There is
    -- no name for the parameter itself and there was never a use for
    -- one: a family's bodies are written in the theory's vocabulary,
    -- not in the parameter's (2026-09-16).  `_` is a binder the head
    -- does not need.
    modelParam nm src = case break (== '(') (dropWhile isSpace src) of
      (t, "") | [tn] <- words t -> ModelParam tn <$> binders nm tn []
      (t, _ : inner) | [tn] <- words t ->
        ModelParam tn <$> binders nm tn (splitTopCommas inner)
      _ -> Left (badParam nm src)

    badParam nm src = "model " ++ nm ++ ": a parameter is written "
                   ++ "`Theory(a, b)` — the theory its argument must "
                   ++ "model, and a name for each of that model's own "
                   ++ "arguments (`_` for one the head does not use), "
                   ++ "not: " ++ dropWhile isSpace src

    -- the binder names are read AT THE THEORY'S KINDS, so `Dual(a)` in
    -- the head parses with `a` as a wire and a constructor binder as a
    -- constructor
    binders nm tn srcs = case [ thParams x | x <- theories, thName x == tn ] of
      [] -> Left $ "model " ++ nm ++ ": the parameter names an unknown "
                ++ "theory: " ++ tn
      (qs : _)
        | length qs /= length srcs ->
            Left $ "model " ++ nm ++ ": the parameter names theory "
                ++ tn ++ ", which takes " ++ show (length qs)
                ++ " argument(s)"
        | otherwise -> sequence (zipWith bindOne qs srcs)
      where
        bindOne q src = case words (takeWhile (/= '#') src) of
          [b] | all isIdentish b -> Right (case q of
                                             PCon _ ar -> PCon b ar
                                             _         -> PWire (TV b))
          _ -> Left (badParam nm tn)

    first' f (x, r) = (f x, r)
    -- Arguments are read AT THE THEORY'S KINDS: a constructor parameter
    -- takes a bare name, everything else a type expression.  The theory
    -- is looked up leniently — an unknown one is reported by
    -- `instanceDefs`, and a count mismatch by the same message
    -- `checkInstance` uses.
    args nm mps t srcs =
      case [ thParams x | x <- theories, thName x == t ] of
        (ps : _)
          | length ps /= length srcs ->
              Left $ "model " ++ nm ++ ": theory " ++ t ++ " expects "
                  ++ show (length ps) ++ " argument(s)"
          | otherwise -> sequence (zipWith (one nm mps t) (map Just ps) srcs)
        [] -> mapM (one nm mps t Nothing) srcs
    one nm _ t (Just q@(PCon _ ar)) src =
      case words (takeWhile (/= '#') src) of
        [c] | all isIdentish c -> do
          ps <- case lookup c dataSigs of
            Just ps -> Right ps
            Nothing -> Left $ "model " ++ nm ++ ": theory " ++ t
                    ++ " declares '" ++ pName q ++ "' as " ++ pKind q
                    ++ ", so its argument names a declared data type; '"
                    ++ c ++ "' is not one" ++ conHint c
          if length ps /= length ar
            then Left $ "model " ++ nm ++ ": theory " ++ t
                     ++ " declares '" ++ pName q ++ "' with arity "
                     ++ show (length ar) ++ ", but " ++ c ++ " takes "
                     ++ show (length ps) ++ " argument(s)"
            else case [ (k, q') | (k, q') <- zip ar ps
                      , k /= isStackParam q' ] of
              ((k, _) : _) -> Left $ "model " ++ nm ++ ": " ++ c
                       ++ " cannot fill the constructor parameter '"
                       ++ pName q ++ "' — theory " ++ t ++ " declares it "
                       ++ "at " ++ pName q ++ "("
                       ++ intercalate ", " [ if b then "..." else "_" | b <- ar ]
                       ++ "), so " ++ c ++ "'s parameters must be declared "
                       ++ (if k then "`...` (a stack) where that says `...`"
                                else "bare (a wire) where that says `_`")
              [] -> Right (IACon c)
        _ -> Left $ "model " ++ nm ++ ": theory " ++ t ++ " declares '"
                 ++ pName q ++ "' as " ++ pKind q ++ ", so its argument "
                 ++ "must be a bare constructor name, not '"
                 ++ dropWhile isSpace src ++ "'"
    -- A FAMILY's argument is written over its parameter's binders
    -- (`Smooth(Dual(a), a)` over `R : Smooth(a, g)`), so they are the
    -- type parameters this piece is parsed with.  An ordinary model has
    -- none and reads exactly as before.
    one _ mps _ _ src = do
      ty <- parseTyBody aliases dataSigs (concatMap mpBinders mps) src
      Right (IAStack (SCons ty SEnd))
    -- `@` is the compiler's character, and a generated declaration may
    -- name a type with it: `model R in Doctrine` writes `model R in R@t(R@k)`
    -- (stage 7b).  Source cannot reach those names \8212 `elabHeaders`
    -- refuses `@` in a term \8212 so admitting it here costs nothing.
    isIdentish ch = isAlphaNum ch || ch `elem` ("_'?!@" :: String)
    conHint "Fn" = " (`Fn` is built in and takes an arrow, not wires; "
                ++ "wrap it — `data Arr(a, b) = Fn⟨a ⇒ b⟩` — to name it here)"
    conHint c | isJust (lookupAlias c aliases) =
      " (it is a transparent `type` alias; a constructor parameter needs "
      ++ "a `data` declaration, which is nominal)"
    conHint _ = ""

parseInstance :: [Alias] -> [(String, [TyParam])] -> [Theory] -> String
              -> [String] -> Either String Instance
parseInstance aliases dataSigs theories header body = do
  (nm, ps, th, args, om) <- parseModelHead aliases dataSigs theories header
  -- AN OBJECT MAP IS A `Base` MODEL'S CLAUSE (stage 7c).  A model of a
  -- theory already has an object map — the theory's parameters,
  -- instantiated at this model's arguments — and a second one at a
  -- mapped type would be a functor into a category whose objects nobody
  -- has named.  Refused for now, and recorded as the open question.
  case om of
    (o : _) | th /= baseTheoryName ->
      Left $ "model " ++ nm ++ ": `" ++ showObjMap o ++ "` is an OBJECT "
          ++ "MAP, and an object map is a `Base` model's clause — a model "
          ++ "of theory " ++ th ++ " already maps objects by instantiating "
          ++ th ++ "'s parameters at its own arguments.  Write `model "
          ++ nm ++ " in Base(" ++ showObjMap o ++ ")`, or drop the clause."
    _ -> Right ()
  -- BOTH body forms, exactly as `def` has both: the bindings after the
  -- head's own `=`, separated by top-level commas, and/or one per
  -- indented line.  Balanced brackets make the comma exact, so `mul =
  -- dup ; *` is one binding whose body composes (2026-09-16).
  let inline = [ r | r <- splitTopCommas
                         (drop 1 (dropWhile (/= '=') (takeWhile (/= '#') header)))
                   , not (blankL r) ]
  binds <- mapM parseBind (inline ++ filter (not . blankL) body)
  pure (Instance nm th args binds ps om [])
  where
    blankL l = all isSpace (takeWhile (/= '#') l)
    parseBind l =
      case break (== '=') l of
        (lhs, '=' : rhs)
          | [_] <- words lhs, secondBinding rhs ->
              Left (separatorErr "bindings")
          | [nm] <- words lhs -> Right (nm, rhs)
        _ -> Left $ "Malformed model binding: " ++ dropWhile isSpace l

-- A MODEL PARAMETERIZED BY A MODEL, instantiated (2026-09-15).
--
-- `model Fwd(R : Smooth(a, g)) : Smooth(Dual(a), a)` is a FAMILY: a
-- functor Mod(Smooth) → Mod(Smooth), not a model.  `with Fwd(Floats)`
-- APPLIES it, and what that mints is an ordinary model named
-- `Fwd(Floats)` — same record, same slot defs, same laws, so everything
-- downstream (a transformation naming it, a receipt printing it, the
-- laws running at module start) needs no case of its own.  Iteration is
-- then free: `Fwd(Fwd(Floats))` is the family applied to a member.
--
-- The carrier is read by SUBSTITUTION and nothing else: the head's
-- binders take the argument model's own theory arguments, and
-- `Smooth(Dual(a), a)` is read off.  No type-level functions.
familyInstances :: [Instance] -> [Instance] -> [ModelApp]
                -> Either String [Instance]
familyInstances fams concrete apps = do
    -- heads first, outer and inner alike: `with Floats(Fwd)` is about
    -- `Floats`, and reporting the `Fwd` inside it would name the wrong
    -- half of the mistake
    mapM_ checkHead wanted
    reverse . snd <$> foldM one (concrete, []) wanted
  where
    wanted = nub (concatMap appClosure apps)
    checkHead (ModelApp f as@(_ : _)) | f `notElem` famNames =
      Left $ "`with " ++ renderModelApp (ModelApp f as) ++ "`: " ++ f
          ++ " is not a parameterized model at this point — a model is "
          ++ "applied to another model only when its own head declares a "
          ++ "parameter (`model " ++ f ++ "(<Theory>(…)) in …`)"
    checkHead _ = Right ()
    famNames = map inName fams
    one (known, made) app
      | any ((== renderModelApp app) . inName) known = Right (known, made)
      | ModelApp f [] <- app, f `elem` famNames =
          Left $ "`with " ++ f ++ "`: " ++ f ++ " is a model PARAMETERIZED "
              ++ "by a model, so it is a family and not a model — apply it, "
              ++ "`with " ++ f ++ "(<model of "
              ++ head ([ mpTheory p | x <- fams, inName x == f
                                    , p <- inParams x ] ++ ["its theory"])
              ++ ">)`"
      | ModelApp _ [] <- app = Right (known, made)   -- an ordinary name
      | otherwise = do
          i <- build known app
          Right (i : known, i : made)

    build known app@(ModelApp f as) = do
      fam <- case [ x | x <- fams, inName x == f ] of
        (x : _) -> Right x
        [] -> Left $ "`with " ++ renderModelApp app ++ "`: " ++ f
                  ++ " is not a parameterized model at this point — a model "
                  ++ "is applied to another model only when its own head "
                  ++ "declares a parameter (`model " ++ f
                  ++ "(<Theory>(…)) in …`)"
      if length as == length (inParams fam) then Right () else
        Left $ "model " ++ f ++ " takes " ++ show (length (inParams fam))
            ++ " model argument(s), given " ++ show (length as)
      argInsts <- sequence (zipWith (resolve f) (inParams fam) as)
      (tm, sm, rm, cm) <- foldM bind (M.empty, M.empty, M.empty, M.empty)
                            (concat (zipWith (\p i -> zip (mpBinders p) (inArgs i))
                                             (inParams fam) argInsts))
      let sub (IAStack st) = IAStack (substParamsS tm sm rm cm st)
          sub (IACon c)    = IACon (M.findWithDefault c c cm)
      pure (Instance (renderModelApp app) (inTheory fam)
                     (map sub (inArgs fam)) (inBindings fam) []
                     (inObjMap fam) (map inName argInsts))
      where
        resolve nm mp a =
          let an = renderModelApp a in
          case [ x | x <- known, inName x == an ] of
            (x : _)
              | inTheory x == mpTheory mp -> Right x
              | otherwise -> Left $ "`with " ++ renderModelApp app
                          ++ "`: the parameter of model "
                          ++ nm ++ " takes a model of " ++ mpTheory mp
                          ++ ", and " ++ an ++ " models " ++ inTheory x
            [] -> Left $ "`with " ++ renderModelApp app ++ "`: " ++ an
                      ++ " is not a model declared at this point"
        bind (tm, sm, rm, cm) (PWire tv, IAStack (SCons t SEnd)) =
          Right (M.insert tv t tm, sm, rm, cm)
        bind (tm, sm, rm, cm) (PRow rv, IAStack (SCons (TSum row) SEnd)) =
          Right (tm, sm, M.insert rv row rm, cm)
        bind (tm, sm, rm, cm) (PStack sv, IAStack st) =
          Right (tm, M.insert sv st sm, rm, cm)
        bind (tm, sm, rm, cm) (PCon n _, IACon c) =
          Right (tm, sm, rm, M.insert n c cm)
        bind _ (q, _) =
          Left $ "model " ++ f ++ ": the binder '" ++ pName q
              ++ "' and the argument model's own argument are not at one kind"

-- The applications a def's `with` clause writes.  EVERY name is read,
-- whatever heads it, so that `with Floats(Fwd)` is refused as "Floats
-- is not parameterized" rather than as an unknown scope name.
headerApps :: [String] -> [String] -> [ModelApp]
headerApps _ = concatMap one
  where
    one n = case tokenize n of
      Right ts | Just (a, []) <- headerApp ts -> [a]
      _                                       -> []

-- Every model APPLICATION a piece of source writes.  Filtered by the
-- family names, because `Dual(x, dx) -> …` is a destructuring binder and
-- only a declared family's name can head an application.
modelApps :: [String] -> String -> [ModelApp]
modelApps fams src = case tokenize src of
  Left _     -> []
  Right toks -> go toks
  where
    -- Anywhere else only a declared family's name can head an
    -- application: `Dual(x, dx) -> …` is a destructuring binder.
    go ts@(TokIdent f : TokLParen : _)
      | f `elem` fams, Just (a, r) <- appTok ts = a : go r
    -- a family's name ALONE is collected too, so that `with Fwd` is
    -- refused as "apply it" rather than as an unknown scope name
    go (TokIdent f : r) | f `elem` fams = ModelApp f [] : go r
    go (_ : r) = go r
    go []      = []


    -- inside a name, parentheses are always application
    appTok (TokIdent n : TokLParen : r) = do
      (as, r') <- appList r
      pure (ModelApp n as, r')
    appTok (TokIdent n : r) = Just (ModelApp n [], r)
    appTok _                = Nothing
    appList ts = do
      (a, r) <- appTok ts
      case r of
        (TokComma : r')  -> do (as, r'') <- appList r'
                               pure (a : as, r'')
        (TokRParen : r') -> Just ([a], r')
        _                -> Nothing

-- FIELD NAMES, and where they die (2026-09-14).
--
--   data Trade = (sym: Str, px: Float, qty: Int)
--
-- names the POSITIONS OF ONE CONSTRUCTOR.  The names are stripped here,
-- before a single type is parsed: `parseTyBody` sees `(Str Float Int)`,
-- the positional body the declaration always had.  So the TYPE is
-- unchanged — `Trade : Str Float Int ⇒ Trade`, `unTrade` the other way,
-- and `Trade(s, p, q) -> …` still destructures by position — and what
-- travels on is a list of WORDS, which `dataFieldArtifacts` turns into
-- one projection each.  Column names are words, not types, and this is
-- the line where that is decided.
parseFieldNames :: String -> String -> String
                -> Either String ([String], String)
parseFieldNames kw name rhs
  | all isNothing leads = Right ([], rhs)
  | kw /= "data" =
      Left $ "Type " ++ name ++ ": field names are for `data` "
          ++ "declarations.  A `type` alias is transparent, so there is "
          ++ "no wire to project from, and a `resource` is threaded "
          ++ "rather than read.  Write `data " ++ name ++ " = …`."
  | any hasTopBar pieces =
      Left $ "Type " ++ name ++ ": field names name the positions of ONE "
          ++ "constructor, and this declaration has more than one "
          ++ "alternative.  Drop the names, or give the alternative you "
          ++ "meant to name its own single-alternative `data` type."
  | otherwise = do
      fs <- sequence [ maybe (Left (unnamed p)) Right l
                     | (p, l) <- zip pieces leads ]
      let ns = map fst fs
      mapM_ checkName ns
      case [ n | n <- ns, length (filter (== n) ns) > 1 ] of
        (n : _) -> Left $ "Type " ++ name ++ ": duplicate field name '"
                       ++ n ++ "' — one name per position, and each one "
                       ++ "becomes a word of its own."
        []      -> Right ()
      Right (ns, "(" ++ unwords (map snd fs) ++ ")")
  where
    pieces = splitTopLevel ',' (stripOuterParens (trimSpace rhs))
    leads  = map leadingFieldName pieces
    unnamed p = "Type " ++ name ++ ": every field is named, or none is — '"
             ++ trimSpace p ++ "' has no name.  Write `name: type`."
    checkName n
      | tokenize n == Right [TokIdent n], n /= "_" = Right ()
      | otherwise = Left $ "Type " ++ name ++ ": '" ++ n
                        ++ "' is not a word, so it cannot name a field — "
                        ++ "a field name becomes an ordinary definition."

-- split on a separator that is not nested inside brackets of any kind
splitTopLevel :: Char -> String -> [String]
splitTopLevel sep = go (0 :: Int) ""
  where
    go _ cur []       = [reverse cur]
    go d cur (c : cs)
      | c == sep, d == 0             = reverse cur : go d "" cs
      | c `elem` ("([\10216" :: String) = go (d + 1) (c : cur) cs
      | c `elem` (")]\10217" :: String) = go (d - 1) (c : cur) cs
      | otherwise                    = go d (c : cur) cs

-- `(a, b)` → `a, b`; anything whose outer parens are not a matched pair
-- wrapping the WHOLE body is left alone
stripOuterParens :: String -> String
stripOuterParens s
  | ('(' : rest) <- s, not (null rest), last rest == ')'
  , balanced (init rest) = trimSpace (init rest)
  | otherwise            = s
  where
    balanced = go (0 :: Int)
      where
        go d []       = d == 0
        go d (c : cs)
          | c `elem` ("([\10216" :: String) = go (d + 1) cs
          | c `elem` (")]\10217" :: String) = d > 0 && go (d - 1) cs
          | otherwise                    = go d cs

hasTopBar :: String -> Bool
hasTopBar = go (0 :: Int)
  where
    go _ []       = False
    go d (c : cs)
      | c == '|', d == 0             = True
      | c `elem` ("([\10216" :: String) = go (d + 1) cs
      | c `elem` (")]\10217" :: String) = go (d - 1) cs
      | otherwise                    = go d cs

leadingFieldName :: String -> Maybe (String, String)
leadingFieldName p =
  case span isFieldChar (trimSpace p) of
    (nm, ':' : rest) | not (null nm) -> Just (nm, rest)
    _                                -> Nothing
  where isFieldChar ch = isAlphaNum ch || ch `elem` ("_'?!" :: String)

-- how many wires a parsed body stands for; Nothing when it is open
-- (a stack parameter or an exponent), which a named field list cannot
-- account for
bodyWireCount :: Ty -> Maybe Int
bodyWireCount (TSum (RCons st RNil)) = go st
  where
    go SEnd        = Just 0
    go (SCons _ r) = (1 +) <$> go r
    go _           = Nothing
bodyWireCount _ = Just 1

parseTypeLine :: [Alias] -> [DataDecl] -> String
              -> Either String (Either Alias DataDecl)
parseTypeLine aliases datas line =
  case break (== '=') line of
    (lhs, '=' : rhs0) -> do
      (kw, name, params) <- parseHead lhs
      (fields, rhs) <- parseFieldNames kw name rhs0
      let sigs = (name, params) : dataSigs
      body <- parseTyBody aliases sigs params rhs
      case (fields, bodyWireCount body) of
        ([], _) -> Right ()
        (fs, Just k) | length fs == k -> Right ()
        (fs, k) ->
          Left $ "Type " ++ name ++ ": " ++ show (length fs)
              ++ " field names for "
              ++ maybe "an open stack of" show k
              ++ " field positions — a named field is exactly one wire."
      -- KINDS BY USE: every named parameter parses as a wire, and an
      -- occurrence under `^` makes it an exponent variable in the body.
      -- So the body's own free-variable sets settle the kinds.
      let (bodyTVs, bodySVs, bodyRVs, bodyNVs, _) = varsOfTy body
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
          -- unreachable: only a `theory` head parses a constructor
          -- parameter; `paramList` below never builds one
          occurs (PCon _ _)  = True
          occurs (PRow rv)   = rv `elem` bodyRVs
      if all occurs params
        then Right ()
        else Left $ "Type alias " ++ name
                 ++ ": every parameter must occur in the body"
      -- a width parameter would have to ride in TData's argument list,
      -- which carries stacks only; aliases are transparent, so they are
      -- fine.  Reject the nominal case with direction.
      case [ q | q <- params, isWidthParam q ] of
        (q : _) | kw == "data" || kw == resourceKw || occursData name body ->
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
      -- ONE DOOR (2026-09-18): a nominal declaration may not put its
      -- own name to the left of an arrow.  Checked here, where the
      -- body is parsed and aliases are already expanded, so the
      -- refusal reaches every path that declares a type — the
      -- keyword, `resource`'s fold into `model`, a `table`'s generated
      -- line, and `dataW` called from a program.
      if kw == "data" || kw == resourceKw || occursData name body
        then checkPositive datas (DataDecl name params body
                                           (kw == resourceKw) fields)
        else Right ()
      pure $ if kw == "data" || kw == resourceKw || occursData name body
               then Right (DataDecl name params body (kw == resourceKw) fields)
               else Left  (Alias name params body)
    _ -> Left $ "Malformed type declaration (missing '='): " ++ line
  where
    parseHead lhs = do
      toks <- normalizeToks <$> tokenize lhs
      case toks of
        -- `model R in Doctrine = Ty` is a resource declaration (the
        -- fold of 2026-09-18): a model of as much of the Doctrine as
        -- the state construction at `Ty` supports.  The body is a
        -- STACK, which is what tells this head from a table; the
        -- keyword branch below is the only thing that changed, and the
        -- DataDecl it makes is the one `resource` made.
        [TokIdent "model", TokIdent name, TokIdent "in", TokIdent d]
          | d == doctrineName, validName name ->
              Right (resourceKw, name, [])
        [TokIdent kw, TokIdent name]
          | kw `elem` declKws, validName name ->
              Right (kw, name, [])
        (TokIdent kw : TokIdent name : TokLParen : rest)
          | kw `elem` declKws, validName name ->
              (,,) kw name <$> paramList rest
        _ -> Left $ "Malformed type declaration: " ++ line
    -- a bare name is ONE WIRE; `...` is a whole stack.  An ANONYMOUS
    -- `...` may only be the last parameter (`data Box(...)`), because
    -- the body spells it `...` and one spelling can name one thing.
    -- A NAMED stack parameter — `data Circuit(a..., b...)` — may sit
    -- anywhere and there may be several (2026-09-16): the body names
    -- each one, and the placement rule that keeps a stack variable in
    -- tail position is enforced where it belongs, in the BODY, by
    -- `goStack`'s "must be the last thing in its stack".  That is what
    -- lets a hom-object range over stacks.
    paramList (TokIdent p : TokEllipsis : TokComma : rest) =
      (PStack (SV p) :) <$> paramList rest
    paramList [TokIdent p, TokEllipsis, TokRParen] = Right [PStack (SV p)]
    paramList (TokIdent p : TokComma : rest) = (PWire (TV p) :) <$> paramList rest
    paramList [TokIdent p, TokRParen]        = Right [PWire (TV p)]
    paramList [TokEllipsis, TokRParen]       = Right [PStack (SV "s")]
    -- the two tails may share a head, in their own order: wires first,
    -- then alternatives
    paramList [TokEllipsis, TokComma, TokDashes, TokRParen] =
      Right [PStack (SV "s"), PRow (RV "r")]
    paramList (TokEllipsis : _) =
      Left "'...' must be the last type parameter"
    paramList [TokDashes, TokRParen]         = Right [PRow (RV "r")]
    paramList (TokDashes : _) =
      Left "'---' must be the last type parameter"
    paramList _ = Left "Malformed type parameter list"
    dataSigs = map dataSig datas
    declKws = ["type", "data"]
    validName n = n `notElem` ([ "Int", "Str", "Sym", "Fn", "Fin"
                               , "type", "data", "model" ]
                               ++ terminalSpellings)
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
    (alts, end, rest') <- goAlts rest
    pure (TSum (foldr RCons end alts), rest')
  (TokIdent "Int" : rest) -> pure (TInt, rest)
  (TokIdent "Float" : rest) -> pure (TFloat, rest)
  (TokIdent "Str" : rest) -> pure (TStr, rest)
  (TokIdent "Sym" : rest) -> pure (TSym, rest)
  -- A theory's CONSTRUCTOR parameter, applied: `k(a, b)`.  It shadows
  -- any type of the same name for the length of the slot signature, and
  -- it is recorded as a TData under the parameter's own name — which
  -- `slotArrowAt` renames to the model's constructor before the slot
  -- is ever forward-declared, so no constructor variable reaches
  -- inference.
  (TokIdent name : TokLParen : rest)
    | Just (PCon _ ks) <- lookupParam name params -> do
        -- each argument is parsed at its DECLARED kind: `_` takes one
        -- wire, `...` takes a whole stack (2026-09-16 — which is what
        -- lets a hom-object name a side of a diagram)
        (args, rest') <- goArgs [ if k then PStack (SV "_") else PWire (TV "_")
                                | k <- ks ] rest
        if length args /= length ks
          then Left $ "Type constructor parameter '" ++ name
                   ++ "' takes " ++ show (length ks) ++ " argument(s), but was "
                   ++ "given " ++ show (length args)
          else do
            sts <- mapM (stackArg name) args
            case [ a | (False, a) <- zip ks sts
                     , closedArity a /= 1 || openTailedS a ] of
              (a : _) -> Left $ "Type constructor parameter '" ++ name
                             ++ "': an argument declared `_` is one wire, "
                             ++ "but was given '" ++ show a ++ "'"
              [] -> pure (TData name sts, rest')
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
    | Just (PRow _) <- lookupParam name params ->
        Left $ "Type parameter " ++ name
             ++ " is a row (`---`): write it as the last alternative of a "
             ++ "sum — (A | ---)"
    | Just (PCon _ ks) <- lookupParam name params ->
        Left $ "Type parameter " ++ name ++ " is a type constructor of "
             ++ "arity " ++ show (length ks) ++ ": it is not a wire, write it "
             ++ "applied — " ++ name ++ "("
             ++ intercalate ", " [ if k then "..." else "_" | k <- ks ] ++ ")"
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
    -- sum alternatives: stack (| stack)* [| ---] )
    -- `---` is the ROW TAIL: "at least these alternatives, maybe more".
    -- It is last by construction, which is what keeps a row variable in
    -- tail position exactly as `...` keeps a stack variable there.
    -- `( --- )` alone is the sum that is ALL residual — `into`'s result.
    goAlts (TokDashes : TokRParen : rest) =
      case rowParamOf params of
        Just rv -> pure ([], RTail rv, rest)
        Nothing ->
          Left "'---' needs a `---` parameter on the declaration"
    goAlts (TokDashes : _) =
      Left "'---' must be the last alternative of its row"
    goAlts ts = do
      (st, rest) <- goStack ts
      case rest of
        (TokBar : rest')    -> do
          (alts, end, rest'') <- goAlts rest'
          pure (st : alts, end, rest'')
        (TokRParen : rest') -> pure ([st], RNil, rest')
        _ -> Left "Expected '|' or ')' in sum type"
    -- a stack: • or a run of elements; a parameter occurrence splices.
    -- `one` is `•`'s ASCII spelling (2026-09-20) and is read here, in
    -- the same position, so there is one rule and not two.
    --
    -- `•^n` is the zero-wide bundle, and it is a legal exponent base
    -- WITHOUT parentheses since 2026-09-20: `(•)^n` and `(• )^n` both
    -- parsed before, and the bare form fell out of the stack parser
    -- into *Expected '|' or ')' in sum type* for no reason but the
    -- order of these two equations.  It is the k = 0 case of the width
    -- schema (design-exponents.md, 2026-09-20).
    goStack (TokIdent t : TokCaret : rest)
      | t `elem` terminalSpellings = do
          (e, rest1) <- expLit rest
          (suffix, rest') <- goStackEnd rest1
          pure (sexp SEnd e suffix, rest')
    goStack (TokIdent t : rest)
      | t `elem` terminalSpellings = pure (SEnd, rest)
    goStack (TokEllipsis : rest)
      | Just (PStack sv) <- stackParam params = do
          (suffix, rest') <- goStackEnd rest
          case suffix of
            SEnd -> pure (STail sv, rest')
            _ -> Left "'...' must be the last thing in its stack"
      | otherwise = Left "'...' needs a `...` parameter on the declaration"
    goStack (TokDashes : _) =
      Left "'---' continues a row's ALTERNATIVES: it can only follow '|'"
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
      (TokEffArrow _ : _) -> pure (SEnd, rest) -- Fn⟨Σ =IO> …⟩ boundary
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
                 (TokEffArrow ls : r) -> Right (r, Eff (S.fromList ls) Nothing)
                 _ -> Left "Expected '⇒' (or '->', '=IO>', '=Recursive>') \
                           \inside a Fn type"
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
    -- the ANONYMOUS `...` in a body names the declaration's stack
    -- parameter, and only when there is exactly one to name: with
    -- several, each is named in the head and spelled by its name
    stackParam ps = case [ q | q@(PStack _) <- ps ] of
                      [q] -> Just q
                      _   -> Nothing
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
      (tm, sm, rm, nm) <- foldM bind (M.empty, M.empty, M.empty, M.empty)
                            (zip (aParams al) args)
      pure (substParams tm sm rm nm (aBody al))
  where
    -- a wire parameter takes exactly one wire; a `...` parameter takes
    -- the whole argument stack; a `^` parameter takes a width; a `---`
    -- parameter takes the ROW of the one sum wire it is given
    bind (tm, sm, rm, nm) (PWire tv, AStack (SCons t SEnd)) =
      Right (M.insert tv t tm, sm, rm, nm)
    bind _ (PWire tv, AStack st) =
      Left $ "Type " ++ aName al ++ ": parameter '" ++ show tv
           ++ "' takes one wire, but was given '" ++ show st
           ++ "' (declare it '...' to take a stack)"
    bind (tm, sm, rm, nm) (PStack sv, AStack st) =
      Right (tm, M.insert sv st sm, rm, nm)
    bind (tm, sm, rm, nm) (PWidth nv, AWidth e)  =
      Right (tm, sm, rm, M.insert nv e nm)
    bind (tm, sm, rm, nm) (PRow rv, AStack (SCons (TSum row) SEnd)) =
      Right (tm, sm, M.insert rv row rm, nm)
    bind _ (PRow rv, AStack st) =
      Left $ "Type " ++ aName al ++ ": parameter '" ++ show rv
           ++ "' is a row (`---`): its argument is a sum's alternatives, "
           ++ "written as a row — (A | B) — but was given '" ++ show st ++ "'"
    bind _ (q, a) =
      Left $ "Type " ++ aName al ++ ": parameter '" ++ pName q
           ++ "' was given the wrong kind of argument ("
           ++ (case a of AWidth e -> "width " ++ show e
                         AStack st -> "stack " ++ show st) ++ ")"

substStackVars :: Map SVar SType -> Ty -> Ty
substStackVars m = substParams M.empty m M.empty M.empty

substParams :: Map TVar Ty -> Map SVar SType -> Map RVar SumRow
            -> Map NVar Exp -> Ty -> Ty
substParams tmap m rmap nmap = goT
  where
    goT t@(TVarTy v) = M.findWithDefault t v tmap
    goT TInt         = TInt
    goT TFloat       = TFloat
    goT TStr         = TStr
    goT TSym         = TSym
    -- substitute inside Fn, KEEPING its grade: a nested written arrow
    -- (`Fn⟨a =Recursive> b⟩` in a theory slot, `Fn⟨a =IO> •⟩` in an alias)
    -- carries a manifest, and dropping it here silently turned every
    -- parameterized Fn pure (found 2026-09-09 by the Recursive label).
    goT (TFn (Arrow i o e)) = TFn (Arrow (goS i) (goS o) e)
    goT (TSum r)     = TSum (goR r)
    goT (TData n as) = TData n (map goS as)
    goT (TFin e)     = TFin (goE e)
    goR RNil         = RNil
    -- SPLICING a row tail: a row variable only ever sits in tail
    -- position, so replacing it with the argument row IS the splice
    -- (the same reason `...` needs no splice machinery).
    goR t@(RTail v)  = M.findWithDefault t v rmap
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
    goT TFloat TFloat m = Just m
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
-- the carriered labels — which fold onto the ARROW rather than onto a
-- wire, so they cannot ride in the alias list.
--
-- ONE CARRIER TABLE (2026-09-17, stage 7b).  Every carriered label,
-- paired with the type constructor its carrier is built from: a
-- resource's carrier is a nullary wire of its own name (`Log`), a
-- category model's is the hom-object (`Logged`).  Until 7b these were
-- two fields and two fold clauses, which is why a label named `R` and
-- a resource named `R` printed the name twice (`=R R>`).  A carrier is
-- a carrier; where it SITS is the only difference, and the stack says
-- that, not the table.
data Disp = Disp { dispAliases  :: [Alias]
                 , dispCarriers :: [(String, String)] }  -- label -> its carrier

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
      TFloat    -> "Float"
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
--
-- The folded names are SUBTRACTED from the sorted set and appended in
-- CARRIER ORDER (2026-09-17): a carriered label's display position is
-- its carrier's position, because the carrier segment is an ordered
-- object and the grade is not.  That is what keeps `=Log Counter>` in
-- `with` order once the label is minted (stage 7b commit 6), and it is
-- what stops a label and its own carrier printing the name twice.
arrowBetween :: EffRow -> [String] -> String
arrowBetween e [] = arrowGlyph e
arrowBetween e ns =
  " =" ++ unwords (S.toList (eLabels e S.\\ S.fromList ns) ++ ns) ++ "> "

showArrowA :: Disp -> Arrow -> String
-- THE CARRIER FOLD.  A carrier is what its label adds to the objects, so a
-- word that builds exactly one `K(a, b)` out of nothing, carrying `K`,
-- IS the arrow `a =K> b` — the same move that folds a threaded resource
-- onto the glyph.  It is a FOLD, not inference: the label must be there
-- and the carrier must be its declared constructor, or the type prints
-- as the two wires it is.  Two carriers side by side (`f g` outside the
-- scope) stay unfolded, which is how you see that `;` there is not
-- composition in K.
showArrowA as (Arrow SEnd (SCons (TData c [a, b]) SEnd) e)
  | any (\(k, cn) -> cn == c && k `S.member` eLabels e) (dispCarriers as)
  = showStackA as a ++ arrowGlyph e ++ showStackA as b
showArrowA as (Arrow s1 s2 e)
  -- a carrier PREFIX shared by both sides is what "threaded through"
  -- means, so that is exactly when the name is earned.  Works on open
  -- stacks: the carriers are at the bottom, the tail is far away.
  | r1 <- leadingCarriers (dispCarriers as) s1
  , r2 <- leadingCarriers (dispCarriers as) s2
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
showSchemeA as (Forall tvars svars rvars nvars evars _ arr) =
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
desugarStmt :: Int -> Stmt -> Term
desugarStmt ln (Stmt firstStage rest) =
  let stages    = firstStage : map snd rest
      followOps = map (Just . fst) rest ++ [Nothing]
      desugared = zipWith openIf stages followOps
  in foldl1 (Seq ln) desugared
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
-- `with` is written out by `elabHeaders` between parse and infer.  If one
-- reaches here the caller skipped elaboration, which used to crash with
-- a pattern-match failure; say so instead.
infer _   (With _ _ _)   = pure ( arrPure SEnd SEnd
                                , [CFail "`with` reached inference \
                                    \unelaborated (internal)"] )
infer _   (In _ _)       = pure ( arrPure SEnd SEnd
                                , [CFail "`in` reached inference \
                                    \unelaborated (internal)"] )
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
               , CFail ("An open-arity atom must \
                        \be the final atom of its tensor stage") : cs0 )
      inS    = foldr1 appendStack [ i | Arrow i _ _ <- arrows ]
      outS   = foldr1 appendStack [ o | Arrow _ o _ <- arrows ]
      -- One stage, one grade: the stage's grade is the JOIN of its
      -- atoms'.  A single atom IS the stage, so no variable is minted
      -- for it (and no constraint); otherwise the stage gets a fresh
      -- row that each atom's row flows into.
      grades = [ g | Arrow _ _ g <- arrows ]
  (stageG, gcs) <- case grades of
    [g] -> pure (g, [])
    _   -> do
      sg <- freshEffRow
      pure (sg, [ CSubEff g sg | g <- grades ])
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

infer env (Seq ln t u) = do
  (Arrow i1 o1 e1, c1) <- infer env t
  (Arrow i2 o2 e2, c2) <- infer env u
  let c = CEqStack o1 i2
  -- Composition JOINS grades: the composite is a FRESH row that each
  -- part flows into (`⊆`), never one part forced equal to the other.
  -- Forcing them equal is what pushed a composite's labels back into a
  -- parameter's `Fn` row through the row `ev` shares — the bug this
  -- constraint form exists to fix (design-effects.md, 2026-09-12).
  e <- freshEffRow
  -- everything the RIGHT stage said, and the cut between the two, is
  -- reported at the right stage's line: that is the stage that did not
  -- fit, and the one a reader has to change.
  pure ( Arrow i1 o2 e
       , c1 ++ stampAt ln c2
            ++ stampAt ln [c] ++ [CSubEff e1 e] ++ stampAt ln [CSubEff e2 e] )

-- Infer one operand of a tensor chain.  Only the final operand may keep
-- its remainder variable open; all earlier operands are closed (ρ := •).
inferOperand :: Env -> Bool -> Term -> Infer (Arrow, [Constraint])
inferOperand env final (Prim name)
  | isIntLiteral name = pick intLitScheme
  | isFloatLiteral name = pick floatLitScheme
  | isStrLiteral name =
      pick (Forall [] [] [] [] [] [] (arrPure SEnd (SCons TStr SEnd)))
  | isSymLiteral name =
      pick (Forall [] [] [] [] [] [] (arrPure SEnd (SCons TSym SEnd)))
  | Just n <- injIndex name, not (M.member name env) = pick (injScheme n)
  | Just k <- distPrimArity name = pick (distScheme k)
  | Just k <- finIndex name, not (M.member name env) = pick (finScheme k)
  -- a receipt is `pass` that the type can see; `with` mints it and `@`
  -- keeps it unwritable, so resolving it here needs no registration
  | Just l <- receiptLabel name, not (M.member name env) =
      pick (receiptScheme l)

  | otherwise =
      case M.lookup name env of
        Nothing ->
          -- inferProgram pre-checks names, so this is unreachable from
          -- the driver; kept as a guard for direct calls.
          error $ "Unknown primitive: " ++ name
        Just sc -> pick sc
  where
    pick sc = if final then instantiateC sc else instantiateClosedC sc
inferOperand env _ (Quote p) = do
  -- Terminal-source constant: • ⇒ Fn⟨…⟩.  The quoted program is inferred
  -- as a whole; its remainder variables stay as metavariables inside
  -- Fn⟨…⟩, solved (monomorphically) at the use site.
  (arrP, cs) <- infer env p
  -- The effect lives INSIDE the Fn: pushing an io action is pure, and
  -- `ev` is where the grade transfers back out.  The outer row is
  -- open (openEff) so a quote may share a stage with an effectful atom.
  q <- openEff (arrPure SEnd (SCons (TFn arrP) SEnd))
  pure (q, cs)
inferOperand env _ (Alts comps residual) = do
  -- Code row (p₁ | … | pₙ [| ---]): the sum functor action.  A one-wire
  -- atom (Δ-in-sum ⇒ Δ-out-sum); component i maps alternative i,
  -- re-tagging into the same position.  The residual `| ---` shares one
  -- row variable between input and output: identity on the rest.
  results <- mapM (infer env) comps
  end <- if residual then RTail <$> freshRVarName else pure RNil
  let arrows = map fst results
      cs     = concatMap snd results
      inRow  = foldr RCons end [ i | Arrow i _ _ <- arrows ]
      outRow = foldr RCons end [ o | Arrow _ o _ <- arrows ]
      grades = [ g | Arrow _ _ g <- arrows ]
  -- exactly one arm runs, but either might, so the row's grade is the
  -- JOIN of the arms': an io branch grades the whole row, and a pure
  -- arm beside it stays pure
  (rowG, gcs) <- case grades of
    []  -> pure (effPure, [])
    [g] -> pure (g, [])
    _   -> do
      rg <- freshEffRow
      pure (rg, [ CSubEff g rg | g <- grades ])
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
  let paramScheme av = Forall [] [] [] [] [] [] (arrPure SEnd (SCons (TVarTy av) SEnd))
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

-- A Float literal: optional `-`, digits, `.`, digits.  Nothing else
-- lexes to this shape, so the test is exact rather than a heuristic.
isFloatLiteral :: String -> Bool
isFloatLiteral s0 =
  let s = case s0 of { '-' : r -> r ; _ -> s0 }
  in case break (== '.') s of
       (ds@(_:_), '.' : fs@(_:_)) -> all isDigit ds && all isDigit fs
       _                          -> False

-- THE DISPLAY CONVENTION, pinned 2026-09-14: the shortest decimal that
-- reads back as the same Double, never in exponent notation, always
-- with a point.  So every finite Float prints as a Float LITERAL and
-- re-reads as itself; `showFFloat Nothing` is Haskell's own
-- shortest-round-trip digits laid out in fixed notation.  The three
-- non-finite values have no literal form and print as themselves.
showFloatLit :: Double -> String
showFloatLit d
  | isNaN d      = "NaN"
  | isInfinite d = if d < 0 then "-Infinity" else "Infinity"
  | otherwise    = showFFloat Nothing d ""

isStrLiteral :: String -> Bool
isStrLiteral ('"' : _) = True
isStrLiteral _         = False

isSymLiteral :: String -> Bool
isSymLiteral ('.' : _ : _) = True
isSymLiteral _             = False

-- The lexical injection family: alt1, alt2, … — position fixed, width
-- open via the row tail.
injIndex :: String -> Maybe Int
injIndex "here"  = Just 1         -- here ≡ alt1: start a sum at the front
injIndex "ok"    = Just 1         -- ok ≡ alt1: return of the sum monad
injIndex "miss"  = Just 2         -- miss ≡ alt2: stay on the miss track
injIndex "again" = Just 1         -- loop protocol: continue with new state
injIndex "done"  = Just 2         -- loop protocol: exit with this result
-- ONE SPELLING: `alt1..altN`, with no `inN` alias kept (2026-09-12 —
-- `[h >> alt1] into` read badly, and `in` is the prefix `into` lives
-- beside).  `def alt1 = ...` is not the migration; a rename is.
injIndex ('a':'l':'t':ds)
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
  Forall [] [] [] [NV "n"] [] []
    (arrPure SEnd (SCons (TFin (Exp (k + 1) (Just (NV "n")))) SEnd))

-- altN : ∀ Δ₁…Δₙ σ. Δₙ ⇒ (Δ₁ | … | Δₙ | σ) — bundle the whole input
-- segment, tagged at position N; other alternatives are placeholders.
injScheme :: Int -> Scheme
injScheme n =
  let d   = SV "Δ"
      ps  = [ SV ("Δ" ++ show i) | i <- [1 .. n - 1] ]
      rv  = RV "σ"
      row = foldr (RCons . STail) (RCons (STail d) (RTail rv)) ps
  in Forall [] (ps ++ [d]) [rv] [] [] []
       (arrPure (STail d) (SCons (TSum row) SEnd))

-- #dist:K : a (ρ₁ | … | ρₖ | σ) ⇒ (a ρ₁ | … | a ρₖ | σ) — push one wire
-- into the first K alternatives of a row and PASS the residual.  One
-- wire, not a block: elimination applies it once per block wire
-- (shallowest first), which is what lands the block in its own order at
-- the bottom of every track.  The residual is the same variable on both
-- sides, so a CLOSED row instantiates it to nothing and the output row
-- stays closed — which is why this covers both of 5a¾'s corners.
distScheme :: Int -> Scheme
distScheme k =
  let a    = TV "a"
      rhos = [ SV ("\961" ++ show i) | i <- [1 .. k] ]
      sig  = RV "\963"
      inRow  = foldr (RCons . STail) (RTail sig) rhos
      outRow = foldr (\r -> RCons (SCons (TVarTy a) (STail r))) (RTail sig) rhos
  in Forall [a] rhos [sig] [] [] []
       (arrPure (SCons (TVarTy a) (SCons (TSum inRow) SEnd))
                (SCons (TSum outRow) SEnd))

-- Integer literals are terminal-source: • ⇒ Int.  Constants have NO
-- implicit remainder — pushing onto a nonempty stack requires explicit
-- `...` (e.g. `1 ...` : ρ ⇒ Int ρ).  See spec-update-exponentials.md.
intLitScheme :: Scheme
intLitScheme = Forall [] [] [] [] [] [] (arrPure SEnd (SCons TInt SEnd))

-- …and a Float literal is the same terminal source at the other base
-- type.  There is no coercion between them: `toFloat` and `floor` are
-- words, written where they are meant.
floatLitScheme :: Scheme
floatLitScheme = Forall [] [] [] [] [] [] (arrPure SEnd (SCons TFloat SEnd))

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
--  ev : ∀Γ Δ. Fn⟨Γ ⇒ Δ⟩ Γ ⇒ Δ   (Γ is consumed, not passed)
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
      -- ε: the grade a higher-order word passes THROUGH.  The inner
      -- Fn's row and the outer arrow's row are the same variable, so
      -- running a pure quote is pure and running an io one is io — one
      -- prim, both readings (design-effects.md's shared variable sort).
      epsV = EV "ε"
      epsR = Eff S.empty (Just epsV)
      arrEps i o = Arrow i o epsR
      -- `{Recursive} ∪ ε`: the same passed-through grade, plus the receipt
      -- that this arrow may recurse without bound.  Open, like an io
      -- prim's row after `openEff`, so a pure neighbour absorbs it.
      recR = Eff (S.singleton recLabel) (Just epsV)
      arrRec i o = Arrow i o recR
      fnGD = TFn (arrEps (STail gam) (STail del))
      evTy = Forall [] [gam, del] [] [] [epsV] []
        (arrEps (SCons fnGD (STail gam)) (STail del))
      -- merge : (Θ | Θ) ⇒ Θ — the binary codiagonal ∇
      mergeTy = Forall [] [SV "Θ"] [] [] [] []
        (arrPure (SCons (TSum (RCons (STail (SV "Θ"))
                       (RCons (STail (SV "Θ")) RNil))) SEnd)
               (STail (SV "Θ")))
      -- into : Fn⟨Γ ⇒ (σ)⟩ (Γ | σ) ⇒ (σ) — the OPEN eliminator.  The
      -- copairing [h, id]: handle the FIRST alternative by mapping it
      -- into the remaining row, and tag-shift everything else down one.
      -- Over a residual that is the only copairing that can be written
      -- at all (a handler for a track hidden in σ is unwritable), which
      -- is why it is a prim and not `caseN`.  ε is shared with the
      -- handler exactly as `ev` shares it.
      intoTy =
        let sig = RV "σ"
            resSum = one (TSum (RTail sig))
        in Forall [] [gam] [sig] [] [epsV] []
             (arrEps (SCons (TFn (arrEps (STail gam) resSum))
                            (one (TSum (RCons (STail gam) (RTail sig)))))
                     resSum)
      -- there : (σ) ⇒ (Δ | σ) — widen a sum with a new front track
      -- (tags shift by one; here ≡ alt1, altN ≡ here >> there^(n-1))
      thereTy = Forall [] [SV "Δ"] [RV "σ"] [] [] []
        (arrPure (SCons (TSum (RTail (RV "σ"))) SEnd)
               (SCons (TSum (RCons (STail (SV "Δ")) (RTail (RV "σ")))) SEnd))
      -- #fix : Fn⟨Fn⟨Σ ⇒ Θ⟩ Σ ⇒ Θ⟩ ⇒ Fn⟨Σ ⇒ Θ⟩ — the parameterized (Conway)
      -- fixpoint operator on Fn.  The body receives the knotted function
      -- DEEPEST, then its own arguments, so a recursive call is spelled
      -- `… >> self >> ev` exactly like any other quoted call; `fix`
      -- itself runs nothing, it ties the knot and hands back the Fn.
      -- This is to recursion what `loop` is to iteration: the operator
      -- that carries the laws (fixpoint, dinaturality, parameter), and
      -- the ONE place a program may be unbounded.  ε is shared with the
      -- inner Fn, like `ev`/`loop`: a pure body ties a pure knot.
      --
      -- Since 2026-09-14 no source program can name it: `with Recursive`
      -- emits it, `fix` is a prelude def written under that scope, and
      -- the prim set is 47 without it.
      --
      -- The `Recursive` label rides on the KNOT, not on `#fix`:
      -- tying it runs nothing, so its own arrow is pure and openEff
      -- freshens it, while the self handed in and the Fn handed back
      -- are `{Recursive} ∪ ε`.  A body that never calls self is asked for no
      -- grade at all; one that does absorbs Recursive through ε, which is the
      -- fixpoint of the grade and settles in one step.
      fixTy =
        let sgF = SV "Σf"; thF = SV "Θf"
            selfF = TFn (arrRec (STail sgF) (STail thF))
            bodyF = TFn (arrEps (SCons selfF (STail sgF)) (STail thF))
        in Forall [] [sgF, thF] [] [] [epsV] []
             (arrPure (one bodyF) (one selfF))
      int2 = SCons TInt (one TInt)
      codeStructTy = codeTy
      int2Router = Forall [] [] [] [] [] []
        (arrPure int2
               (one (TSum (RCons int2 (RCons int2 RNil)))))
      eqTy = Forall [a] [] [] [] [] []
        (let aa = SCons ta (one ta)
         in arrPure aa (one (TSum (RCons aa (RCons aa RNil)))))
      binIntTy = Forall [] [] [] [] [] []
        (arrPure (SCons TInt (one TInt)) (one TInt))
      -- Float (2026-09-14).  Every one of these is an IMPLEMENTATION
      -- prim, in the kernel for the same reason the Int arithmetic and
      -- the four io words are: a double is a machine number and nothing
      -- in the language can build one.  NO word is shared with Int.
      binFloatTy = Forall [] [] [] [] [] []
        (arrPure (SCons TFloat (one TFloat)) (one TFloat))
      unFloatTy = Forall [] [] [] [] [] []
        (arrPure (one TFloat) (one TFloat))
      float2Router = Forall [] [] [] [] [] []
        (let ff = SCons TFloat (one TFloat)
         in arrPure ff (one (TSum (RCons ff (RCons ff RNil)))))
      -- Bool ≡ (• | •): two payload-free tracks; true = alt1, false = alt2
      tBool    = TSum (RCons SEnd (RCons SEnd RNil))
      boolLit  = Forall [] [] [] [] [] [] (arrPure SEnd (one tBool))
      -- mapAccumN: the tier's ONE catamorphism.  `Aⁿ` is the initial
      -- algebra of `n ↦ Aⁿ` in [ℕ, C], and every fold-shaped word over
      -- a bundle is this same catamorphism at a different MOTIVE:
      -- `foldExp` at the constant carrier `n ↦ r`, `mapN` at
      -- `n ↦ bⁿ`, and the general one here at `n ↦ (r ⇒ r bⁿ)` —
      -- traversal in the State applicative, which for a finitary
      -- container is all of traversability (design-exponents.md,
      -- amendment 2026-09-21).  THE ACCUMULATOR IS A WIRE: with a wire
      -- the runtime reads n off the segment as `total − 1` and the
      -- split is determined; a stack accumulator would leave
      -- `|ρ| + n = total` with nothing to fix it, which is the same
      -- erasure argument that rules out segment variables.  Elements
      -- are one wire too; a wider element boxes (`Box`).
      nExp = Exp 0 (Just (NV "n"))
      mapAccumNTy =
        let d  = TV "D"
            td = TVarTy d
            stepArr = arrEps (SCons td (one ta)) (SCons td (one tb))
        in Forall [a, b, d] [] [] [NV "n"] [epsV] []
             (arrEps (SCons (TFn stepArr)
                      (SCons td (SExp (one ta) nExp SEnd)))
                    (SCons td (SExp (one tb) nExp SEnd)))
      -- the Naperian half: powers preserve products, `aⁿ bⁿ ≅ (a b)ⁿ`.
      -- BOTH SIDES BOX (2026-09-21), so the element either one hands
      -- `mapAccumN` is ONE WIRE — the discipline that lets one
      -- catamorphism serve every element width (MANUAL §13) — and so
      -- that the iso is an iso: `zipN >> unzipN` and `unzipN >> zipN`
      -- are both the identity, which they were not while `unzipN`
      -- took the flat form.  `splitN` is the flat chunker, kept under
      -- its own name because `(a b)ⁿ` is what the stack-native
      -- two-wire words (`foldExp2`, `mapN2`, `indicesN`'s output) see.
      zipNTy = Forall [a, b] [] [] [NV "n"] [] []
        (arrPure (SExp (one ta) nExp (SExp (one tb) nExp SEnd))
               (SExp (one (TData "Box" [SCons ta (one tb)])) nExp SEnd))
      unzipNTy = Forall [a, b] [] [] [NV "n"] [] []
        (arrPure (SExp (one (TData "Box" [SCons ta (one tb)])) nExp SEnd)
               (SExp (one ta) nExp (SExp (one tb) nExp SEnd)))
      -- de-interleave a FLAT pair bundle into two bundles
      splitNTy = Forall [a, b] [] [] [NV "n"] [] []
        (arrPure (SExp (SCons ta (one tb)) nExp SEnd)
               (SExp (one ta) nExp (SExp (one tb) nExp SEnd)))
      -- INDICES (design-indices.md).  Every introduction's n is forced
      -- by a relevant input: `indicesN` and `checkedAt` read a live
      -- bundle, and the finK literals carry their bound as an offset.
      -- There is deliberately no `tabulate`/`asFin`: an output-only n
      -- has no witness, exactly as for `zeroN`.
      atTy = Forall [a] [] [] [NV "n"] [] []
        (arrPure (SCons (TFin nExp) (SExp (one ta) nExp SEnd))
               (one ta))
      indicesNTy = Forall [a] [] [] [NV "n"] [] []
        (arrPure (SExp (one ta) nExp SEnd)
               (SExp (SCons (TFin nExp) (one ta)) nExp SEnd))
      -- the dynamic discharge: check an Int against the LIVE width;
      -- the hit track carries the index and the untouched bundle
      checkedAtTy = Forall [a] [] [] [NV "n"] [] []
        (arrPure (SCons TInt (SExp (one ta) nExp SEnd))
               (one (TSum (RCons (SCons (TFin nExp) (SExp (one ta) nExp SEnd))
                          (RCons (SCons TInt (SExp (one ta) nExp SEnd))
                                 RNil)))))
      weakenTy = Forall [] [] [] [NV "n"] [] []
        (arrPure (one (TFin nExp)) (one (TFin (Exp 1 (Just (NV "n"))))))
      finIntTy = Forall [] [] [] [NV "n"] [] []
        (arrPure (one (TFin nExp)) (one TInt))
  in M.fromList $
         -- `_` is the identity: the positional spelling, a wire this
         -- stage does not touch.  `id` is the WORD for the same
         -- morphism and is therefore a prelude def (`def id = _`), not
         -- a second prim.
       [ ("_",     Forall [a]    [] [] [] [] [] (arrPure (one ta) (one ta)))
       , ("swap",  Forall [a, b] [] [] [] [] []
           (arrPure (SCons ta (one tb)) (SCons tb (one ta))))
       , ("dup",   Forall [a]    [] [] [] [] [] (arrPure (one ta) (SCons ta (one ta))))
       , ("drop",  Forall [a]    [] [] [] [] [] (arrPure (one ta) SEnd))
       , ("pass",  Forall []     [rho] [] [] [] [] (arrPure (STail rho) (STail rho)))
         -- the terminal morphism: forget the whole segment
       , ("forget", Forall []    [rho] [] [] [] [] (arrPure (STail rho) SEnd))
         -- `one` is the IDENTITY ON THE TERMINAL OBJECT, and it is a
         -- prim rather than a prelude def for the same reason `pass`
         -- is: it must RUN NOTHING.  `1 ; drop : • ⇒ •` was the only
         -- way to write this morphism before 2026-09-20, and it
         -- allocates an Int in order to discard it.  Its type is
         -- MONOMORPHIC and that is the whole point — `pass : ρ0 ⇒ ρ0`
         -- names the same morphism at every width and therefore PINS
         -- NOTHING, so `[pass]` cannot serve where `[one] : • ⇒
         -- Fn⟨• ⇒ •⟩` is wanted.  `•` is the second spelling of this
         -- word in term position (parseStage); the display is `one`.
       , ("one",   Forall []     []   [] [] [] [] (arrPure SEnd SEnd))
       , ("+",     binIntTy)
       , ("*",     binIntTy)
       , ("print", Forall [a]    [] [] [] [] [] (arrIO (one ta) SEnd))
       , ("true",  boolLit)
       , ("false", boolLit)
       , ("eq?",       eqTy)
       , ("lt?",       int2Router)
       , ("-",         binIntTy)
       , ("div",       binIntTy)
       , ("mod",       binIntTy)
         -- the Float words: `f` + the operation, spelled out.  A
         -- symbolic scheme (`f+ f- f*`) cannot be had — `-` is not an
         -- identifier character, so `f-` is two atoms — and a scheme
         -- that breaks on subtraction is not a scheme.  `fneg` and
         -- `fabs` are prelude defs; equality is the polymorphic `eq?`,
         -- which already reaches a Float.
       , ("fadd",      binFloatTy)
       , ("fsub",      binFloatTy)
       , ("fmul",      binFloatTy)
       , ("fdiv",      binFloatTy)
       , ("flt?",      float2Router)
       , ("fexp",      unFloatTy)
       , ("fsin",      unFloatTy)
       , ("fcos",      unFloatTy)
       , ("fsqrt",     unFloatTy)
         -- the two crossings, both written where they are meant: there
         -- is no coercion and no numeric tower
       , ("toFloat",   Forall [] [] [] [] [] [] (arrPure (one TInt) (one TFloat)))
       , ("floor",     Forall [] [] [] [] [] [] (arrPure (one TFloat) (one TInt)))
       , ("cat",       Forall [] [] [] [] [] []
           (arrPure (SCons TStr (one TStr)) (one TStr)))
       , ("toStr",     Forall [a] [] [] [] [] [] (arrPure (one ta) (one TStr)))
         -- a RENDERER for a whole stack, not a class: `showStack` is the
         -- REPL's own `:s` printer as a word, so what a program prints
         -- of its stack and what a session shows of one are the same
         -- convention.  Consuming and open-tailed (`ρ0 ⇒ Str`), so the
         -- open-tailed convention already says where it may stand: it
         -- takes the whole segment as the final atom of its stage and
         -- is closed to the empty one anywhere else, exactly as
         -- `forget` is.  A binder (`(b -> b >> unBox >> showStack)`)
         -- is what aims it at part of a stack.  It does NOT compose
         -- into user-defined
         -- rendering — `toStr` is the per-wire word, and there is no
         -- class for either of them.
       , ("showStack", Forall [] [rho] [] [] [] [] (arrPure (STail rho) (one TStr)))
       , ("asInt?",    Forall [] [] [] [] [] []
           (arrPure (one TStr)
                  (one (TSum (RCons (one TInt)
                        (RCons (one TStr) RNil))))))
         -- `asInt?`'s Float twin (2026-09-14), and it reads exactly the
         -- SOURCE notation for a Float literal — optional `-`, digits,
         -- point, digits.  That is also what the display prints, so
         -- `toStr ; asFloat?` is the identity on every finite Float and
         -- the reader and the printer are one convention rather than two.
       , ("asFloat?",  Forall [] [] [] [] [] []
           (arrPure (one TStr)
                  (one (TSum (RCons (one TFloat)
                        (RCons (one TStr) RNil))))))
         -- `s sep ; split` — cut a Str at every occurrence of a
         -- separator.  A machine fact about a machine string, like
         -- `cat` and `asInt?`: n+1 pieces for n occurrences, so the
         -- pieces and the separators reconstruct the original, empty
         -- pieces included.  An empty separator cuts nothing (one
         -- piece, the whole string) — the only total reading, since
         -- "every occurrence of nothing" has no finite answer.
       , ("split",     Forall [] [] [] [] [] []
           (arrPure (SCons TStr (one TStr))
                    (one (TData "List" [one TStr]))))
       , ("symStr",    Forall [] [] [] [] [] [] (arrPure (one TSym) (one TStr)))
       , ("unparse",   Forall [] [] [] [] [] []
           (arrPure (SCons codeStructTy SEnd) (one TStr)))
       , ("parse",     Forall [] [] [] [] [] []
           (arrPure (one TStr)
                  (one (TSum (RCons (one codeStructTy)
                        (RCons (one TStr) RNil))))))
       -- η ; checkedStage — η, having been CHECKED to be a unit
       -- endomorphism (`ρ ⇒ ρ`, or `E ρ ⇒ E ρ` over a resource
       -- prefix), so that a stage inserted at every cut leaves the
       -- program's type where it was.  The check is the whole of it:
       -- the weaving is `interposeRaw`, an ordinary prelude word, and
       -- `interpose` is the two composed (2026-09-18).
       , ("checkedStage", Forall [] [] [] [] [] []
           (arrPure (one codeStructTy) (one codeStructTy)))
       , ("readLine",  Forall [] [] [] [] [] []
           (arrIO SEnd
                  (one (TSum (RCons (one TStr)
                        (RCons (one TStr) RNil))))))
       , ("readFile",  Forall [] [] [] [] [] []
           (arrIO (one TStr)
                  (one (TSum (RCons (one TStr) (RCons (one TStr) RNil))))))
       , ("writeFile", Forall [] [] [] [] [] []
           (arrIO (SCons TStr (one TStr))
                  (one (TSum (RCons SEnd (RCons (one TStr) RNil))))))
       -- Run code that will only exist at runtime, AGAINST A WITNESS.
       -- The witness is never applied: its arrow is the expectation the
       -- loaded code must meet, written as a value because Braid has no
       -- type syntax in terms.  The context types against Γ ⇒ Δ with
       -- ordinary variables — no existentials anywhere — and at runtime
       -- the loaded code must SUBSUME the witness (§12).  Sharing ε with
       -- the witness is the sandbox: a pure witness admits only pure
       -- code, and running it stays pure.
       , ("evalAs",  Forall [] [gam, del] [] [] [epsV] []
           (arrEps (SCons fnGD (SCons codeStructTy (STail gam)))
                  (one (TSum (RCons (STail del)
                        (RCons (SCons TStr (STail gam)) RNil))))))
       , ("reflect",   Forall [] [gam, del] [] [] [epsV] []
           (arrPure (one (TFn (arrEps (STail gam) (STail del))))
                  (one (TSum (RCons (one codeStructTy)
                        (RCons (one TStr) RNil))))))
       -- decide equality of two programs by NORMALIZING them, rather
       -- than testing them at chosen inputs (§12.9).  Both must lie in
       -- the structural fragment; outside it this is an error, not a
       -- `false`, because "I cannot tell" is not "they differ".
       -- REFLECTED TYPES (2026-09-16).  Four words that answer with
       -- what the checker already knows, and one that lists it.  All
       -- pure, all on the miss track when there is nothing to answer:
       -- they read the PREFIX SCOPE, so a `functor` may call them and
       -- an elaboration-time derivation is an ordinary Braid word
       -- (MANUAL §12).
       , ("typeOfWord", Forall [] [] [] [] [] []
           (arrPure (one TStr)
                  (one (TSum (RCons (one typeRepTy)
                        (RCons (one TStr) RNil))))))
       , ("declOf",    Forall [] [] [] [] [] []
           (arrPure (one TStr)
                  (one (TSum (RCons (one declReprTy)
                        (RCons (one TStr) RNil))))))
       , ("showType",  Forall [] [] [] [] [] []
           (arrPure (one typeRepTy) (one TStr)))
       , ("typeOfCode", Forall [] [] [] [] [] []
           (arrPure (one codeStructTy)
                  (one (TSum (RCons (one typeRepTy)
                        (RCons (one TStr) RNil))))))
       , ("envOf",     Forall [] [] [] [] [] []
           (arrPure SEnd
                  (one (TData "List"
                         [one (TData "Box"
                                [SCons TStr (one typeRepTy)])]))))
       , ("sameCode",  Forall [] [gam, del] [] [] [epsV] []
           (arrPure (SCons (TFn (arrEps (STail gam) (STail del)))
                          (one (TFn (arrEps (STail gam) (STail del)))))
                    (one tBool)))
       -- the Code-level twin (§12.9).  A functor's output IS Code, so a
       -- law about a functor can only be stated over Code; and Code has
       -- already been through abstraction elimination, so `sameCodeC`
       -- DECIDES programs `sameCode` refuses for carrying a binder.
       , ("sameCodeC", Forall [] [] [] [] [] []
           (arrPure (SCons codeStructTy (one codeStructTy)) (one tBool)))
       -- `froms tos c >> rewrite` — rename atoms by a table, everywhere
       -- in the spine: quotes, rows (the residual flag is carried) and
       -- groups included.  The ENGINE of a rule set, and unchecked on
       -- its own: `rules` is where the table is blessed (§8), exactly
       -- as `interposeRaw` is the unchecked half of `interpose`.
       , ("rewrite",   Forall [] [] [] [] [] []
           (arrPure (SCons (TData "List" [one TSym])
                      (SCons (TData "List" [one TSym])
                        (one codeStructTy)))
                    (one codeStructTy)))
       , ("ev",        evTy)
       , ("into",      intoTy)
       , ("there",     thereTy)
       , ("merge",     mergeTy)
       , (knotPrimName, fixTy)
       , ("mapAccumN", mapAccumNTy)
       , ("at",        atTy)
       , ("indicesN",  indicesNTy)
       , ("checkedAt", checkedAtTy)
       , ("weaken",    weakenTy)
       , ("finInt",    finIntTy)
       , ("splitN",    splitNTy)
       , ("unzipN",    unzipNTy)
       , ("zipN",      zipNTy)
       -- THE DECLARATION WORDS (stage 8).  Ordinary words, with the
       -- manifest in the arrow: `defW : Code Str =Dict> \8226`.  They
       -- are prims for the kernel's own reason \8212 they touch the
       -- implementation, acting on the dictionary the checker holds,
       -- exactly as `print` touches the world.
       ] ++ [ (dwWord w, declWordScheme w) | w <- declWordTable ]

--------------------------------------------------------------------------------
-- 8. Driver: parse + infer + solve
--------------------------------------------------------------------------------

primsIn :: Term -> [String]
primsIn (Prim n)        = [n]
primsIn (Tensor ts)     = concatMap primsIn ts
primsIn (Seq _ t u)     = primsIn t ++ primsIn u
primsIn (Quote t)       = primsIn t
primsIn (OpenAbs slots _ t) =
  [ n | n <- primsIn t, n `notElem` [ x | Just x <- slots ] ]
primsIn (Alts comps _)  = concatMap primsIn comps
primsIn (With _ _ b)   = primsIn b
primsIn (In _ b)       = primsIn b

-- Infer a term's principal arrow in a given environment.
inferTermIn :: Env -> Term -> Either String Arrow
inferTermIn = inferTermInAt 0

-- ...and the same, told which line to blame for anything the term did
-- not stamp itself — a def's or a main program's FIRST stage, which no
-- `>>` introduced and which therefore carries no stamp of its own
-- (2026-09-15).  0 means "no line", and the refusal then names only the
-- def it is in.
inferTermInAt :: Int -> Env -> Term -> Either String Arrow
inferTermInAt ln env = fmap fst . inferTermSubAt ln env

-- …and the ⊆ constraints that survive, for callers about to
-- GENERALIZE the result (a def, a runtime `evalAs` check).  A caller
-- that only wants to read the arrow can drop them: they relate rows
-- the display hides anyway.
inferTermSub :: Env -> Term -> Either String (Arrow, [EffSub])
inferTermSub = inferTermSubAt 0

inferTermSubAt :: Int -> Env -> Term -> Either String (Arrow, [EffSub])
inferTermSubAt ln0 env term =
  case nub [ n | n <- primsIn term
               , not (isIntLiteral n)
               , not (isFloatLiteral n)
               , not (isStrLiteral n)
               , not (isSymLiteral n)
               , not (M.member n env)
               , Nothing <- [injIndex n]
               , Nothing <- [finIndex n]
               , Nothing <- [receiptLabel n]
               , Nothing <- [distPrimArity n] ] of
    (n : _) -> Left $ atLine (whichStage n) ("Unknown primitive: " ++ n)
    [] -> do
      let (arr, cs0) = runInfer0 (infer env term)
          cs           = stampAt ln0 cs0
      s <- solve cs
      pure (apply s arr, residualSubs s cs)
  where
    -- an unknown word is named where it is WRITTEN: the first stage
    -- that mentions it, quotes and groups included
    whichStage n =
      listToMaybe ([ l | (l, atoms) <- spineLines term
                       , n `elem` concatMap primsIn atoms
                       , l /= 0 ] ++ [ ln0 | ln0 /= 0 ])

-- A definition is not in scope in its own body (5a½): recursion is
-- written with `fix`, at a typed boundary, so every def is a CLOSED
-- SPINE over its prefix scope -- every stage's scheme is computable
-- without knowing the def's own type, and a functor out of it is total.
selfReferenceError :: String -> Bool -> String
selfReferenceError name viaRecurse =
  "`" ++ name ++ "` refers to itself"
    ++ (if viaRecurse then " (`recurse` named the definition being written)"
                      else "")
    ++ ": write `with " ++ recLabel ++ "` in its header (MANUAL §8)"


inferProgram :: String -> Either String Arrow
inferProgram src = first (locFor [] src) $ do
  term <- parseProgram src
  inferTermInAt 1 primEnv term

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
  let (tvs0, svs0, rvs0, nvs0, evs) = varsOfArrow arr
      (rigT, tvs) = partition isRigidT tvs0
      -- existentials get their own stable numbering and keep the tag, so
      -- a displayed type says WHICH parts are frozen
      (rigS, svs) = partition isRigidS svs0
      (rigR, rvs) = partition isRigidR rvs0
      (rigN, nvs) = partition isRigidN nvs0
      tm = M.fromList
             (zip tvs [ TVarTy (TV ("a" ++ show n)) | n <- [0 :: Int ..] ]
              ++ zip rigT [ TVarTy (TV (rigidTag ++ show n)) | n <- [0 :: Int ..] ])
      sm = M.fromList
             (zip svs [ STail (SV ("ρ" ++ show n)) | n <- [0 :: Int ..] ]
              ++ zip rigS [ STail (SV (rigidTag ++ show n)) | n <- [0 :: Int ..] ])
      rm = M.fromList
             (zip rvs [ RTail (RV ("σ" ++ show n)) | n <- [0 :: Int ..] ]
              ++ zip rigR [ RTail (RV (rigidTag ++ show n)) | n <- [0 :: Int ..] ])
      nm = M.fromList
             (zip nvs [ Exp 0 (Just (NV ("n" ++ show n))) | n <- [0 :: Int ..] ]
              ++ zip rigN [ Exp 0 (Just (NV (rigidTag ++ show n))) | n <- [0 :: Int ..] ])
      -- effect tails are invisible in display, but normalizing them
      -- keeps `:t!` deterministic
      em = M.fromList
             (zip evs [ Eff S.empty (Just (EV ("ε" ++ show n)))
                      | n <- [0 :: Int ..] ])
  in substOnce (Subst tm sm rm nm em) arr

--------------------------------------------------------------------------------
-- 9.5 The ambient elaborator (`with`)
--
-- Resources ride DEEPEST, in `with` order, so every offset here is a
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

-- ...and the same run read through the display's carrier table, as the
-- LABELS those wires carry.  A hom-object carrier never matches here —
-- it takes two stack arguments and it is the whole arrow, not a wire
-- beneath one — so the two fold clauses partition the cases without
-- overlapping.
leadingCarriers :: [(String, String)] -> SType -> [String]
leadingCarriers tbl (SCons (TData n []) r)
  | (l : _) <- [ k | (k, cn) <- tbl, cn == n ] = l : leadingCarriers tbl r
leadingCarriers _ _                            = []

elabHeadersTop :: Env -> Term -> Either String Term
elabHeadersTop env = elabHeaders (elabCtx0 env [])

-- `with` names RESOURCES (wires to thread) and MODELS (slots to
-- resolve) — and, in a def's own header, the THEORY whose model the
-- def is waiting for.  Both are scoped selection with no inference and no
-- dispatch: a model's operations are renamed to that model's
-- defs, once, for the rest of the scope.
-- What a `with` scope needs to know: the environment and the runnable
-- prefix scope (a functor is EVALUATED here), which model names
-- carry which slots, and which functor names are implemented by which
-- word.
data ElabCtx = ElabCtx
  { ecEnv   :: Env
  , ecRun   :: RunDefs
  , ecSlots :: SlotTable
  , ecFuncs :: [(String, String)]
  , ecTmpls :: TemplateTable
  , ecThs   :: [String]          -- theory names, so `with T` is read right
  , ecTrans :: [Transport]         -- models with a carrier: the categories
                                   -- a `with` may transport into
  , ecKWords :: [(String, String)] -- def name -> the model it is a word of
  , ecBases :: [BaseInstance]      -- partial models of the ambient
                                   -- presentation: word -> its image
  , ecSelf  :: [String]           -- the models this def is a COMPONENT
                                   -- of, if any: their `with` resolves
                                   -- slot names and mints nothing, because
                                   -- a model does not apply itself.  A
                                   -- FAMILY instance's slot body names the
                                   -- PARAMETER's slots, so the parameter is
                                   -- on this list beside the instance.
  , ecGen   :: Bool                -- a def the COMPILER wrote (a
                                   -- transformation's squares), which may name
                                   -- a slot in the compiler's own
                                   -- spelling.  Source may not, and that
                                   -- refusal is what makes a slot
                                   -- reachable only through its scope.
  , ecDef   :: Maybe String        -- the def whose body this is, if any:
                                   -- the ONE name `with Recursive` puts
                                   -- back in scope.  Nothing at the top
                                   -- level, where there is no name to tie.
  , ecTables :: [String]           -- the module's `table` row types, so
                                   -- that `Trades@cellAt` is refused as
                                   -- a TABLE's insides rather than as a
                                   -- model's slot
  , ecRes   :: [String]           -- the module's RESOURCE names (stage
                                   -- 7b).  A resource generates a model
                                   -- of its own name, so the name is in
                                   -- `ecSlots` too; `with R` on a
                                   -- resource is routing, and this is
                                   -- what says which reading wins.
  , ecRefl  :: RCtx                -- what the REFLECTION words read
                                   -- (2026-09-16).  A functor is an
                                   -- ordinary pure word run at
                                   -- elaboration, so `declOf` inside one
                                   -- must see the declarations the
                                   -- prefix scope has made; `rcEnv` here
                                   -- is ignored in favour of `ecEnv`,
                                   -- which is the same scope kept up to
                                   -- date in one place.
  }

-- the reflection context a scope evaluates in: its own environment over
-- the declarations it was built with
ecRCtx :: ElabCtx -> RCtx
ecRCtx ctx = (ecRefl ctx) { rcEnv = ecEnv ctx }

-- `with Recursive` (2026-09-14): the MARKER that puts a def's own name
-- back in scope in its own body.  It is not a functor and not a model —
-- it is a SYNTACTIC rewrite to the closed form the language already
-- had, run before inference and INNERMOST among a header's scopes, so
-- `with Traced Recursive` traces the closed spine:
--
--   def fac with Recursive = BODY
--     ↦   use@Recursive
--         [ (#self ... -> BODY[fac := #self ... >> ev]) ] ...
--         #fix ...
--         ev
--
-- so every elaborated def is STILL a closed spine over its prefix
-- scope: `reflect`, the per-stage schemes and every functor keep the
-- totality stage 5a½ bought.  No types are consulted — the rewrite is
-- textual in the Term, and a binder parameter named like the def
-- shadows it exactly as it shadows any other word.
selfCallTerm :: Term
selfCallTerm = Seq 0 (Tensor [Prim selfKnotName, Prim "pass"]) (Prim "ev")

-- A GENUINE NO-OP WHEN THERE IS NOTHING TO TIE (2026-09-18).  A body
-- that never names the def needs no knot, and wrapping one round it
-- anyway put `#fix` into code that could not recurse — which is both a
-- wasted `ev` at runtime and, since 2026-09-18, a lie: a scope mints
-- its receipt iff it CHANGED the code, so an unconditional wrap would
-- make `with Recursive` mint on a body it did nothing to.  The
-- substitution decides: it is the only thing the rewrite does.
tieKnot :: String -> Term -> Term
tieKnot name body
  | tied == body = body
  | otherwise =
      Seq 0 (Seq 0 (Tensor [Quote (OpenAbs [Just selfKnotName] True tied),
                            Prim "pass"])
                   (Tensor [Prim knotPrimName, Prim "pass"]))
            (Prim "ev")
  where
    tied = subst body
    subst (Prim n) | n == name = selfCallTerm
    subst (Seq n a b)          = Seq n (subst a) (subst b)
    subst (Tensor ts)          = Tensor (map subst ts)
    subst (Quote t)            = Quote (subst t)
    subst (Alts cs r)          = Alts (map subst cs) r
    subst t@(OpenAbs sl h b)
      -- a parameter of the def's own name shadows it, as it shadows
      -- any word: the rewrite stops at the binder that rebinds it
      | name `elem` [ n | Just n <- sl ] = t
      | otherwise                        = OpenAbs sl h (subst b)
    subst (With ap ns b)       = With ap ns (subst b)
    subst (In ns b)            = In ns (subst b)
    subst t                    = t

-- the refusal `with Recursive` fixes, and the one it gets itself when
-- there is no name to tie
noSelfToTieErr :: String
noSelfToTieErr =
  "`with " ++ recLabel ++ "` names the def it heads, and there is no def "
    ++ "here: it puts a definition's OWN NAME in scope in its own body, so "
    ++ "it may only be a def's header (MANUAL §8)"

-- `model Opt : Base = dupInt = dup` — a PARTIAL model of the
-- ambient presentation.  `Base` is the theory whose generators are every
-- word in scope, each with its own scheme as the slot's declared type;
-- a binding names a generator and gives its image; every generator not
-- named maps to itself.  So the table is the bindings, and `with Opt` is
-- the same renaming `with Inst` performs — with the image a word that
-- already exists, so no slot def is generated.
-- ONE RECORD FOR EVERY MODEL (stage 7c).  A model of `Base` is an
-- `Instance` like every other: its theory is the ambient presentation,
-- its arguments are none, its bindings are the table, and `inObjMap`
-- carries the object map when one was written.  The separate list it
-- lives in says only that its theory is not one anybody declared.
type BaseInstance = Instance

-- the base model of this name a scope names, if any
lookupBase :: String -> [BaseInstance] -> Maybe BaseInstance
lookupBase n bs = listToMaybe [ b | b <- bs, inName b == n ]

-- What a `with` scope needs to know about a model: the THEORY it
-- models, and the slot names that rename to it.  The theory is what
-- makes a template resolvable — a body written over `with Monoid` is
-- instantiated by whichever `with IntSum` it stands inside.
type SlotTable = [(String, (String, [String]))]

-- A TEMPLATE: name ↦ (theory, unelaborated body).  It is not a def and
-- never reaches the environment or the runtime scope — there is no body
-- that runs before a model says what its slots mean.  It is
-- recorded here, expanded at the call inside the model's scope, and
-- re-inferred there, so every instantiation gets its own principal type
-- and the rank-1 wall is never met.
type TemplateTable = [(String, (String, Term))]

elabCtx0 :: Env -> SlotTable -> ElabCtx
elabCtx0 env slots =
  ElabCtx env M.empty slots [] [] [] [] [] [] [] False Nothing [] []
          (rctxOf env)

-- Apply one functor to a scope body: reify the code, RUN the
-- EXTENSION of the declared graph morphism (purely, on a step budget),
-- splice the result back.  The morphism was checked
-- `Fn⟨Stage ⇒ Code⟩` and pure where the functor was declared.
runFunctor :: ElabCtx -> (String, String) -> Term -> Either String Term
runFunctor ctx (fname, gm) body = do
  -- declarations are hoisted above defs, so the morphism is checked at
  -- the first USE, where the prefix scope is what it will be at run
  -- time.  That is the ordering rule made concrete.
  ext <- either (Left . (pre ++)) Right
           (checkFunctorWord (ecEnv ctx) (rcDatas (ecRefl ctx)) fname gm)
  cv  <- inF (reflectPure (ecEnv ctx) body)
  out <- inF (runPureEval (evalTerm (ecRCtx ctx) (ecRun ctx) emptyVarEnv
                            ext [cv]))
  case fst out of
    [c] -> inF (codeToTermV c)
    vs  -> Left $ pre ++ "a functor must return exactly one Code value, "
                ++ "but " ++ gm ++ " returned " ++ show (length vs)
  where
    pre  = "`with " ++ fname ++ "`: "
    inF  = either (Left . (pre ++)) Right

-- Apply a MODEL to a scope body: the free category's spine becomes a
-- composite in the category the model presents.  `;` is the model's
-- COMPOSITION and every stage is its EMBEDDING of that stage as a
-- quotation — a functor out of `Free(G)` determined on generators,
-- which is why it needs no check of its own beyond the types of the
-- code it emits.  Which slot is which is read off the theory's declared
-- arrows (`transportOf`), never off a slot's name.
--
-- WIDTH — and there is nothing to do about it (2026-09-16).  A
-- hom-object `k(ρ, σ)` names a whole STACK on each side, so a stage of
-- any width embeds as itself: `embed [stage]`, whatever `stage` covers.
-- The base already makes every stage cover the stack it is handed —
-- that is what `_` and `...` are for — so the base's own widths ride
-- through the functor untouched.  Until this date the carrier was ONE
-- WIRE, which is why there was an arity to read, a pairing to pack
-- with, and a strength to whisker by: three warts with one cause.  They
-- are gone with the cause.
--
-- The one thing it must know without any of that is which atoms are
-- ALREADY carriers: the defs declared under `with M` or `in M`, held
-- syntactically in `ecKWords`.  That table is exact because exits are
-- refused here — so every transported def produces a carrier, and
-- nothing else can.
runTransport :: ElabCtx -> Transport -> Term -> Either String Term
-- THE FUSED PATH (stage 7b).  A REPRESENTABLE fibre's hom-object is an
-- object of the base, so `embed [s] >> compose` has a NORMAL FORM \8212
-- `_^k s ...` \8212 and that is character for character what `elabScope`
-- emits.  Running the unfused path here would build and immediately
-- destroy an `R@k` wrapper at every stage: every reflected program
-- would change, and `metered.braid` would count a different number of
-- stages.  So the routing pass is not deleted, it is RESTATED as the
-- fused evaluator of the resource model, and what goes is the idea
-- that routing is a separate kind of scope.
--
-- One model here; `elabHeaders` calls the same evaluator with the
-- whole GROUP a clause names, because the carrier SEGMENT is ordered
-- and the padding depth is the group's size.
runTransport ctx tp body
  | Just e <- tpResource tp = elabScope (ecEnv ctx) [e] body
-- THE READER (stage 9, 2026-09-21).  A theory with no `embed` and a
-- table of base spellings transports ATOM-WISE instead of stage-wise.
runTransport ctx tp body
  | isNothing (tpEmbed tp), not (null (tpRead tp)) = readTransport ctx tp body
runTransport ctx tp body = do
  embW <- maybe (Left noEmbed) Right (fmap (slotDefName nm) (tpEmbed tp))
  thenW <- maybe (Left "internal: transport with no composition") Right
                 (fmap (slotDefName nm) (tpCompose tp))
  case [ e | (dn, e) <- exits, dn `elem` primsIn body ] of
    (e : _) -> Left $ "`" ++ e ++ "` leaves " ++ nm
                   ++ "; call it outside `with " ++ nm ++ "` (a category is "
                   ++ "entered by a marker and left by a model: inside the "
                   ++ "scope every word builds a carrier, `" ++ tpCarrier tp
                   ++ "(a, b)`).  `in " ++ nm ++ "` opens the same "
                   ++ "vocabulary and transports nothing."
    []      -> Right ()
  -- A word of ANOTHER model is a stage that builds that model's carrier
  -- out of nothing, and an embedding embeds programs, not carriers.  Say
  -- so here: inference would only say `Cannot unify stacks: • vs a16`.
  case [ (n, k) | [Prim n] <- stages, Just k <- [lookup n (ecKWords ctx)]
                , k /= nm ] of
    ((n, k) : _) ->
      Left $ "`with " ++ nm ++ "`: " ++ n ++ " is a word of " ++ k
          ++ ", so it builds a carrier rather than being a program "
          ++ fromMaybe "the embedding" (tpEmbed tp) ++ " could embed.  A "
          ++ "category is entered from the BASE: compose " ++ n
          ++ " under `with " ++ k ++ "`, or write the crossing as a word "
          ++ "that leaves " ++ k ++ " first."
    [] -> Right ()
  case stages of
    []       -> Left $ "`with " ++ nm ++ "`: the scope is empty, and a "
                    ++ "transported scope must build a " ++ tpCarrier tp
    (s : ss) ->
      pure (chainTerm (concat (zipWith (step embW thenW)
                                       (True : repeat False) (s : ss))))
  where
    nm     = tpName tp
    stages = filter (not . null) (spineOf body)
    exits  = [ (slotDefName nm e, e) | e <- tpExits tp ]
    -- a stage that is one atom and is ALREADY a carrier is left alone:
    -- a def written under `with M` or `in M`, or one of the theory's
    -- own entry slots (`sample`), whose type said so in writing
    enters = map (slotDefName nm) (tpEnters tp)
    kword [Prim n] = lookup n (ecKWords ctx) == Just nm || n `elem` enters
    kword _        = False

    -- the stages one source stage becomes, given nothing on the stack:
    -- they build its carrier.  A carrier already on the stack is put
    -- underneath with `_` and composed.
    carrierOf embW s
      | kword s   = [s]
      | otherwise = [[Quote (chainTerm [s])], [Prim embW]]

    step embW thenW first s =
      let cs = carrierOf embW s
      in if first then cs else map (Prim "_" :) cs ++ [[Prim thenW]]

    noEmbed = "`with " ++ nm ++ "`: theory " ++ tpTheory tp ++ " takes "
           ++ doctrineName ++ "'s `" ++ doctrineCompose ++ "` and not its `"
           ++ doctrineEmbed ++ "` (`Fn\10216\961 \8658 \963\10217 \8658 k(\961, \963)`): `with "
           ++ nm ++ "` cannot transport a base stage; `in " ++ nm ++ "` and "
           ++ "compose by hand."

--------------------------------------------------------------------------------
-- `embed` ON A SUBCATEGORY (stage 9, 2026-09-21)
--
-- The Doctrine's `embed : Fn⟨ρ ⇒ σ⟩ ⇒ k(ρ, σ)` asserts an
-- identity-on-objects functor from the WHOLE base.  For linear maps
-- that is false, and declaring it anyway makes `embed [fsin]` a linear
-- map.  What IS true is a WIDE SUBCATEGORY `B_lin ⊆ B` and a functor
-- `B_lin → K`, so `embed` is PARTIAL — and the partiality is the
-- guarantee.
--
-- A wide subcategory is determined by a set of GENERATORS closed under
-- composition.  The base is PRESENTED, so every program is a composite
-- of generators and "is this program in the subcategory" reduces to "is
-- every atom in the generator set" — a syntactic scan, decidable.
-- `examples/transpose.braid`'s `linear?` asks exactly that at RUNTIME
-- and answers with a Bool; this asks it at ELABORATION and answers with
-- a refusal.
--
-- THE MECHANISM IS A MODEL READ BACKWARDS.  A theory's base spellings
-- are a model of it IN THE BASE (`copy ↦ dup`, `add ↦ fadd`); the table
-- is injective on generators (checked at the `theory` line), so it has
-- a PARTIAL INVERSE `read : B ⇀ B[T]`, undefined off the table, and
-- transport is `read` then the model.  Not new machinery: one table
-- used as a PARSER composed with another used as an interpreter, and
-- the universal property does the rest — a functor out of a free
-- category IS a graph morphism, so an image per generator extends to
-- every program.
--
-- THE TABLE IS THE THEORY'S, NOT A MODEL'S, and that is the design
-- decision.  `B_lin` is a property of the PRESENTATION — which base
-- programs are linear is not something two models of one theory may
-- disagree about — so the spelling is written beside the signature,
-- where the generator is, and every model of the theory reads through
-- the same one.  A reference model named at the scope (`with Dense via
-- Funcs`) would put it in the wrong place twice: it would let two
-- models define two different subcategories, and it would ask the
-- inverse of a model whose slot bodies are PROGRAMS, which is not a
-- table at all.
--
-- ATOM-WISE, NOT STAGE-WISE.  Standard transport sends `f ; g` to
-- `embed [f] embed [g] ; compose`, embedding each STAGE opaquely; this
-- must send `dup ; fadd` to `copy add ; compose`, reading each ATOM
-- into a slot.  It is a MODE rather than a parameterization: the two
-- share the composition and the K-word and exit rules, and differ in
-- what one stage becomes, which is the whole of `carrierOf`.
--
-- SOUND BUT INCOMPLETE.  It accepts only programs built from the
-- theory's generators; it rejects base programs that are semantically
-- in the subcategory but spelled with an atom off the table; it never
-- accepts one that is not.  That is the direction that matters.
readTransport :: ElabCtx -> Transport -> Term -> Either String Term
readTransport ctx tp body = do
  mapM_ spellingOK (tpRead tp)
  case [ e | (dn, e) <- exits, dn `elem` primsIn body ] of
    (e : _) -> Left $ "`" ++ e ++ "` leaves " ++ nm
                   ++ "; call it outside `with " ++ nm ++ "` (a category is "
                   ++ "entered by a marker and left by a model: inside the "
                   ++ "scope every word builds a carrier, `" ++ tpCarrier tp
                   ++ "(a, b)`).  `in " ++ nm ++ "` opens the same "
                   ++ "vocabulary and transports nothing."
    []      -> Right ()
  case stages of
    [] -> Left $ "`with " ++ nm ++ "`: the scope is empty, and a "
              ++ "transported scope must build a " ++ tpCarrier tp
    ss -> do
      cs <- mapM carrierOf ss
      pure (chainTerm (concat (zipWith step (True : repeat False) cs)))
  where
    nm     = tpName tp
    thenW  = slotDefName nm (fromMaybe doctrineCompose (tpCompose tp))
    stages = filter (not . null) (spineOf body)
    exits  = [ (slotDefName nm e, e) | e <- tpExits tp ]
    enters = map (slotDefName nm) (tpEnters tp)
    kword [Prim n] = lookup n (ecKWords ctx) == Just nm || n `elem` enters
    kword _        = False

    -- a carrier already on the stack is put underneath and composed,
    -- exactly as the stage-wise path does
    step first cs = if first then cs else map (Prim "_" :) cs ++ [[Prim thenW]]

    -- THE CHECK, at the first USE rather than at the declaration:
    -- declarations are hoisted above defs, so a theory's base spelling
    -- may name a word this module defines, and the prefix scope is what
    -- it will be at run time.  The same rule a `functor`'s graph
    -- morphism obeys (2026-09-06).
    spellingOK (_, _, Nothing)   = Right ()   -- a whiskering: `_` has no scheme
    spellingOK (w, slot, Just a) = case M.lookup w (ecEnv ctx) of
      Nothing -> Left $ here ++ "theory " ++ tpTheory tp ++ " spells its "
        ++ "generator `" ++ slot ++ "` `" ++ w ++ "`, and `" ++ w
        ++ "` is not defined at this point: a base spelling is read where "
        ++ "the scope is written, so the word must be in scope there."
      Just sc -> case subsumes sc a of
        Right () -> Right ()
        Left _   -> Left $ here ++ "theory " ++ tpTheory tp ++ " spells its "
          ++ "generator `" ++ slot ++ "` `" ++ w ++ "`, and the two do not "
          ++ "agree: the slot says the base atom is `"
          ++ show (normalizeArrow a) ++ "` and `" ++ w ++ "` is `"
          ++ show (normalizeArrow (runInfer0 (instantiate sc)))
          ++ "`.  A base spelling is the generator ITSELF, written in the "
          ++ "ambient presentation."

    -- A STAGE the reader can transport is `_`\8230 followed by exactly ONE
    -- generator: the `_`s are the whiskering, and the generator is the
    -- carrier they ride under.  Two generators side by side IS a tensor,
    -- and there is nothing to send it to — a hom-object over stacks
    -- writes only one of the two whiskerings, so `m \8855 n` is not
    -- constructible from a theory's own slots (MANUAL \167\&8).
    carrierOf s
      | kword s   = Right [s]
      | otherwise = do
          named <- mapM readAtom s
          let gens = [ sl | (_, sl, Just _)  <- named ]
              whs  = [ sl | (_, sl, Nothing) <- named ]
          case (gens, named) of
            ([g], _) | (_, _, Just _) <- last named ->
              Right ( [[Prim (slotDefName nm g)]]
                   ++ [ [Prim (slotDefName nm w)] | w <- reverse whs ] )
            ([_], _) -> Left $ stageHere s ++ "ends in a whiskering: a `"
                     ++ "_` rides UNDER what follows it, so the generator "
                     ++ "goes last in its stage."
            ([], _)  -> Left $ stageHere s ++ "is all whiskering and no "
                     ++ "generator, so there is no carrier to ride under."
            _        -> Left $ stageHere s ++ "puts two of "
                     ++ tpTheory tp ++ "'s generators side by side, which "
                     ++ "is their TENSOR — and a hom-object over stacks "
                     ++ "writes only one of the two whiskerings "
                     ++ "(`k(\964 \961, \964 \963)` declares, `k(\961 \964, \963 \964)` "
                     ++ "does not), so " ++ tpTheory tp ++ " has nothing to "
                     ++ "send it to.  Write the stages one at a time."

    stageHere s = here ++ "the stage `" ++ renderTerm (chainTerm [s]) ++ "` "

    -- ...and this is the refusal the whole construction exists for.
    readAtom (Prim n)
      | Just (sl, a) <- lookup3 n (tpRead tp) = Right (n, sl, a)
      | isLiteralAtom n = Left $ here ++ "`" ++ n ++ "` has no image under "
          ++ tpTheory tp ++ ": a LITERAL is not a generator of it.  A "
          ++ "literal is a stage `\8226 \8658 \964`, and a constant introduced into "
          ++ "a diagram is what makes a map AFFINE rather than linear "
          ++ "(`x ; " ++ n ++ " ; fadd` is the shortest example).  A "
          ++ "scalar IS a generator of the presentation, but one per "
          ++ "value and never a word, so no literal can enter the table "
          ++ "and this one is refused rather than quietly admitted."
      | otherwise = Left $ here ++ "`" ++ n ++ "` has no image under "
          ++ tpTheory tp ++ ": its generators are "
          ++ intercalate ", " [ "`" ++ w ++ "`" | (w, _, _) <- tpRead tp ]
          ++ ", and `" ++ n ++ "` is not one of them, so the functor has "
          ++ "nothing to send it to.  `with " ++ nm ++ "` admits exactly "
          ++ "the programs built from those atoms — sound, and "
          ++ "deliberately incomplete: call `" ++ n ++ "` outside the "
          ++ "scope, or write the word it belongs to under `with " ++ nm
          ++ "` too."
    readAtom t = Left $ here ++ "`" ++ renderTerm t ++ "` is not an atom of "
      ++ "the base presentation, so there is no generator to read it as: a "
      ++ "scope transported by a reader is a composite of "
      ++ tpTheory tp ++ "'s generators and nothing else."

    lookup3 n tbl = listToMaybe [ (sl, a) | (w, sl, a) <- tbl, w == n ]
    here = "`with " ++ nm ++ "`: "

-- A LITERAL IS NOT A GENERATOR.  Its family is infinite and none of its
-- members is a word, which is why an object-mapped model needs `via`
-- for it — and why a reader must refuse it: see `readTransport`.
isLiteralAtom :: String -> Bool
isLiteralAtom n =
  isIntLiteral n || isFloatLiteral n || isStrLiteral n || isSymLiteral n

-- The RECEIPT of a functor: a stage that does nothing and says so.
--
-- `with F` mints `F` onto the manifest of everything it elaborated, and
-- the only way to put a label on an inferred arrow is to compose with
-- an arrow that carries it — which is how `print` has always minted io.
-- So the receipt is `pass` with a label: `∀ρ. ρ =F> ρ`, a unit
-- endomorphism (stage 4's fragment again), prepended to the expansion.
-- It costs nothing at runtime, it whiskers at any width, and it cannot
-- be written by hand — only `with` mints, which is what makes a label
-- evidence rather than an annotation.
receiptName :: String -> String
receiptName f = "with@" ++ f

receiptLabel :: String -> Maybe String
receiptLabel = stripPrefix "with@"

receiptScheme :: String -> Scheme
receiptScheme f =
  Forall [] [rho] [] [] [] [] (Arrow (STail rho) (STail rho) (effLabel f))
  where rho = SV "ρ"

-- every declared functor's receipt, ready for the environment defs and
-- main are inferred in
receiptEnv :: [(String, String)] -> Env -> Env
receiptEnv funcs env =
  foldr (\(f, _) e -> M.insert (receiptName f) (receiptScheme f) e) env funcs

-- A FUNCTOR IS A GRAPH MORPHISM (2026-09-18).  A presentation is
-- generators and relations, and a functor out of the category it
-- presents is determined by one image per generator — that is the
-- universal property, and a free category's functors ARE exactly its
-- graph morphisms.  So `functor F = w` asks `w` for one image per
-- generator, `Fn⟨Stage ⇒ Code⟩`, and the EXTENSION to the whole of
-- `Code` is the meaning of the declaration rather than something the
-- author writes.
--
-- Pure, because it runs at elaboration and the io grade IS the phase
-- distinction.  `Recursive` is admitted (the budget is what stands
-- between a looping functor and a hung compiler) and rides on the
-- receipt.
--
-- Returns the extension, parsed: `runFunctor` runs it and the word `F`
-- the declaration generates is the same source, so there is one
-- spelling of what a functor DOES.
checkFunctorWord :: Env -> [DataDecl] -> String -> String
                 -> Either String Term
checkFunctorWord env datas fname gm = do
  g   <- ordering (parseProgramIn datas gm)
  arr <- ordering (inferTermIn env g)
  let Arrow i o eff = arr
      sOne t        = SCons t SEnd
      isCodeCode    = either (const False) (const True)
                        (solve [ CEqStack i (sOne codeTy)
                               , CEqStack o (sOne codeTy) ])
  case o of
    SCons (TFn (Arrow gi go geff)) SEnd
      | Right _ <- solve [ CEqStack i SEnd
                         , CEqStack gi (sOne stageTy)
                         , CEqStack go (sOne codeTy) ] ->
          if eIO eff || eIO geff
            then Left $ here ++ "must be pure — a functor runs while the "
                             ++ "module is being elaborated, so it cannot "
                             ++ "do IO"
            else Right ()
    _ | isCodeCode -> Left wholeSpine
    _ -> Left $ here ++ "must be a GRAPH MORPHISM — `\8226 \8658 "
             ++ graphMorphismTy ++ "`, one image per generator, which is "
             ++ "what a functor out of a free category is determined by "
             ++ "— but is " ++ show (normalizeArrow arr)
  parseProgramIn datas (functorExtSrc gm)
  where
    here = "functor " ++ fname ++ ": " ++ gm ++ " "
    ordering = first (\e -> here ++ "— " ++ e
                         ++ " (a functor's graph morphism must be defined "
                         ++ "before the functor line)")
    -- THE WHOLE-SPINE SCOPE IS GONE, and nothing is lost: the two
    -- honest homes for a `Code ⇒ Code` word are named here rather than
    -- left for the reader to find.
    wholeSpine =
      here ++ "is Code ⇒ Code — an ENDOMAP OF THE OBJECT OF MORPHISMS, "
        ++ "not a functor: it has no object map, no generator images and "
        ++ "nothing that makes it commute with `;`.  `functor` takes a "
        ++ "graph morphism, " ++ graphMorphismTy ++ ".  A "
        ++ "Code \8658 Code word has two homes: `lift2 [" ++ gm
        ++ "]` applies it at RUNTIME, checked against the program's own "
        ++ "type with the original as the fallback; and a top-level "
        ++ "declaration program (`[code] \"name\" ; " ++ defWordName
        ++ "`) DECLARES what it generates, for code that is generated "
        ++ "rather than rewritten.  MANUAL \167\&8."

-- The `Code ⇒ Code` EXTENSION of a graph morphism, as source.  `with
-- F` runs this and the word `F` the declaration generates IS this, so
-- a functor's action has one spelling.  `stagewise` is the extension
-- operator (`flatMap` on the spine): the image of a composite is the
-- composite of the images, which is the universal property computed.
functorExtSrc :: String -> String
functorExtSrc gm = "(" ++ gm ++ ") ... >> stagewise"

-- what a functor's declaration asks for, spelled as the manual spells
-- it (the display folds `Stage` and `Code` only with the alias table in
-- hand, and a refusal should read the way the docs read)
graphMorphismTy :: String
graphMorphismTy = "Fn\10216Stage \8658 Code\10217"

-- `Stage = List(Atom)`, the generators a graph morphism is defined on
stageTy :: Ty
stageTy = TData "List" [SCons (TData "Atom" []) SEnd]

-- the declaration word a generated def goes through, named once
defWordName :: String
defWordName = "defW"

-- The generated TRANSPORT word of a model with a carrier is a
-- `Code ⇒ Code` word the compiler wrote, and this is its check: if a
-- model's slots ever stop composing, the message says so at the
-- declaration rather than at some use.  It is not a functor
-- declaration's check — a functor takes a graph morphism — which is
-- why it is a routine of its own.
checkCodeWord :: Env -> String -> Either String ()
checkCodeWord env word =
  case M.lookup word env of
    Nothing -> Left $ "model " ++ word ++ ": the transport word is not "
                   ++ "defined at this point"
    Just sc ->
      let arr@(Arrow i o g) = runInfer0 (instantiate sc)
          codeS = SCons codeTy SEnd
      in case solve [CEqStack i codeS, CEqStack o codeS] of
           Left _ -> Left $ "model " ++ word ++ ": the transport word must "
                         ++ "be Code \8658 Code, but is "
                         ++ show (normalizeArrow arr)
           Right _
             | eIO g -> Left $ "model " ++ word ++ ": the transport word "
                            ++ "must be pure"
             | otherwise -> Right ()

elabHeaders :: ElabCtx -> Term -> Either String Term
elabHeaders ctx t0 = do
  t1 <- expandTemplates ctx [] [] t0
  strayRec t1
  go t1
  where
    -- `with Recursive` is a def's HEADER.  The name it puts back in
    -- scope is the DEF's, so a knot tied around part of a body would
    -- quietly name that part instead — refused where it is written.
    strayRec (With _ _ b) = strayRec b
    strayRec (In _ b)     = strayRec b
    strayRec t
      | deepRec t = Left $ "`with " ++ recLabel ++ "` is a def's header — "
                        ++ "the first thing in its body: the name it puts "
                        ++ "back in scope is the DEF's, so a scope opened "
                        ++ "part-way down would name only that part "
                        ++ "(MANUAL §8)"
      | otherwise = Right ()

    deepRec (With _ ns b)  = recLabel `elem` ns || deepRec b
    deepRec (In _ b)       = deepRec b
    deepRec (Seq _ a b)    = deepRec a || deepRec b
    deepRec (Tensor ts)    = any deepRec ts
    deepRec (Quote t)      = deepRec t
    deepRec (Alts cs _)    = any deepRec cs
    deepRec (OpenAbs _ _ b) = deepRec b
    deepRec (Prim _)       = False

    go (With ap ns0 b) = do
      b0 <- go b
      -- `Recursive` first, and INNERMOST: it is a rewrite to the closed
      -- form, so every other scope on this header — a model's renaming,
      -- a resource's routing, a functor's walk — sees the tied knot
      -- rather than a name that is not in scope yet.
      -- One spelling per thing: the marker owns the name, so a functor,
      -- model or theory of the same name is a collision, not a shadow.
      case [ () | recLabel `elem` ns0
                , recLabel `elem` ecThs ctx
                  || isJust (lookup recLabel (ecFuncs ctx))
                  || isJust (lookup recLabel (ecSlots ctx))
                  || isJust (lookupBase recLabel (ecBases ctx)) ] of
        (_ : _) -> Left $ "`" ++ recLabel ++ "` is the built-in recursion "
                       ++ "marker (MANUAL §8), so `with " ++ recLabel
                       ++ "` cannot name your declaration: rename it"
        []      -> Right ()
      let ns = filter (/= recLabel) ns0
      b' <- if length ns == length ns0
              then pure b0
              else case ecDef ctx of
                     Just d  -> pure (tieKnot d b0)
                     Nothing -> Left noSelfToTieErr
      -- THE ORDER IS ACTIONS, NOT KEYWORDS (restated 2026-09-18, when
      -- `resource` folded into `model` and there were fewer keywords to
      -- order by).  Templates EXPAND (a phase earlier, in
      -- `expandTemplates`); then renames, then routes, then composes,
      -- then rewrites — so a rewrite always sees fully renamed, fully
      -- routed code, and an expanded template body is routed by the
      -- scopes it landed in.
      --
      -- Nothing here ever read a keyword.  Each name is looked up in
      -- the table its DECLARATION put it in, and the table is decided
      -- by what the name's theory is: a carrier declared `model R in
      -- Doctrine` is in `ecRes` and ROUTES; a model whose theory has
      -- slots is in `ecSlots` and RENAMES; a model of `Base` is in
      -- `ecBases` and REWRITES by its table; a model whose theory has a
      -- hom-object is in `ecTrans` and COMPOSES; a functor is in
      -- `ecFuncs` and REWRITES the spine.  That is why the fold was a
      -- change of spelling and not of behaviour.
      case [ n | n <- ns, n `elem` ecThs ctx ] of
        (n : _) -> Left $ "`with " ++ n ++ "` names a theory: `with` "
                       ++ "applies a functor, and a theory is not one — "
                       ++ "write `in " ++ n
                       ++ "` to make this def a template"
        []      -> Right ()
      -- a TRANSPORT is named here too, and is taken OUT of the functor list:
      -- its rule is not a `Code ⇒ Code` word run over the spine but the
      -- carrier construction below, which needs the K-word table.
      -- a model WITH A CARRIER whose theory declares composition is a
      -- category, and `with` of it transports.  Nothing is keyed on the
      -- name `mode` any more: the model is an ordinary model and the
      -- shape of its theory is what decides (`transportOf`).
      -- ...except the model's own slot and law bodies (`ecSelf`), whose
      -- `with I` resolves names and applies nothing: a model does not
      -- transport itself, or every slot body would be `arrP` of itself.
      -- ...and except an INSTANTIATING scope (`Apply`): the body it
      -- wraps is already a morphism of the theory, so the model says
      -- what the slot names mean and composition stays the base's.
      -- A REPRESENTABLE model \8212 the one a `resource` generates \8212 is
      -- transported by the FUSED path below, with the whole group the
      -- clause names, so it is not one of the categories counted here.
      -- That is also why `with Log Counter` is not "two categories": a
      -- representable fibre's carriers are disjoint WIRES and commute
      -- by geometry, where two hom-object carriers would embed each
      -- other's.
      let ms  = [ tp | ap == Transporting
                     , tp <- ecTrans ctx, tpName tp `elem` ns
                     , isJust (tpCompose tp), isNothing (tpResource tp)
                     , tpName tp `notElem` ecSelf ctx ]
          mns = map tpName ms
      case ms of
        (_ : _ : _) -> Left $ "`with " ++ unwords mns ++ "`: a clause may "
                           ++ "name at most one category — the second would "
                           ++ "embed the first's carriers as if they were "
                           ++ "programs.  Nest the scopes, or declare the "
                           ++ "composite category."
        _           -> Right ()
      -- a BASE model is a renaming, not a `Code ⇒ Code` word run over
      -- the spine: it maps generators of the ambient presentation to
      -- their images, and every generator it does not name maps to
      -- itself.  Same phase as `with <model>`, because it is one.
      let bs   = [ b | n <- ns, Just b <- [lookupBase n (ecBases ctx)] ]
          fs   = [ (n, w) | n <- ns, n `notElem` mns
                          , isNothing (lookupBase n (ecBases ctx))
                          , Just w <- [lookup n (ecFuncs ctx)] ]
          rest = [ n | n <- ns
                     , isNothing (lookupBase n (ecBases ctx))
                     , n `elem` mns || isNothing (lookup n (ecFuncs ctx)) ]
          -- A RESOURCE IS ROUTED, even though it also names the model
          -- its declaration generates (stage 7b): `with Log` threads
          -- the wire.  The one exception is the generated model's own
          -- slot bodies, where `with Log` resolves slot names and
          -- applies nothing, exactly as every other model's do.
          (is, rs) = partitionEithers
                       [ if n `elem` ecRes ctx && n `notElem` ecSelf ctx
                           then Right n
                           else maybe (Right n) (\(_, sl) -> Left (n, sl))
                                      (lookup n (ecSlots ctx))
                       | n <- rest ]
          -- IMAGE MEMBERSHIP (2026-09-18).  Each model's rename is
          -- applied on its own rather than folded blind, so its
          -- receipt can be decided by whether ITS action changed the
          -- code.  `foldr` applied the last element first; `foldl`
          -- over the reverse is the same order.
          stepRename (t, ch) (i, sl) =
            let t' = renameSlotsT i sl t
            in (t', ch ++ [ i | t' /= t ])
          (b0', renamed) = foldl stepRename (b', []) (reverse is)
      -- the RESOURCES, transported into the models their declarations
      -- generated, as one group: `elabScope` is those models' fused
      -- evaluator (`runTransport`'s first clause is the k = 1 case of
      -- exactly this call).
      -- A MODEL OF `Base` REWRITES THE AMBIENT PRESENTATION, and an
      -- OBJECT-MAPPED one rewrites the types under it too: the images
      -- it names are inlined, a literal of the mapped type is composed
      -- with `via`, a word that mentions the type and has a body is
      -- UNFOLDED (cached as `M@def`), one with a retraction is
      -- conjugated, and a word that mentions it with none of the three
      -- is refused by name.  A word whose scheme never mentions the
      -- type passes through untouched: the functor is the identity off
      -- A, which is what makes `with M` twice the identity the second
      -- time.
      (b'', based) <-
        foldM (\(t, ch) i -> do
                 t' <- if null (inObjMap i)
                         then Right (renameWordsT (baseWordTable i) t)
                         else objTransportT ctx i t
                 pure (t', ch ++ [ inName i | t' /= t ]))
              (b0', []) bs
      routed0 <- case rs of
                   [] -> pure b''
                   _  -> elabScope (ecEnv ctx) rs b''
      (routed, transported) <-
        foldM (\(t, ch) tp -> do
                 t' <- runTransport ctx tp t
                 pure (t', ch ++ [ tpName tp | t' /= t ]))
              (routed0, []) ms
      -- left to right: functor composition of Code ⇒ Code words IS `;`,
      -- so `with F G` is sugar for one composed functor
      -- Code cannot encode a `with`, so a functor's output never
      -- contains one: no re-walk needed
      (expanded, walked) <-
        foldM (\(t, ch) fw -> do
                 t' <- runFunctor ctx fw t
                 pure (t', ch ++ [ fw | t' /= t ]))
              (routed, []) fs
      -- and each functor leaves its receipt on the expansion.  A label
      -- is minted here or nowhere, and since 2026-09-18 it is minted
      -- IFF THE SCOPE CHANGED THE CODE — image membership, the law the
      -- functor notes already state for an idempotent F (`F(p) = p` ⟺
      -- p is in F's image).  A receipt therefore says "this scope
      -- changed this code" rather than "this scope was applied to it",
      -- which is the stronger reading and the useful one: code a scope
      -- left alone has nothing to audit, and the label would only tell
      -- a caller to expect something that is not there.  The
      -- comparison is on the `Term`, before and after that one scope's
      -- action — structural, total, and already blind to a stage's
      -- line stamp (`instance Eq Term`), so provenance does not count
      -- as a change.  It is the Term rather than its `Code` reflection
      -- because a body may carry a binder, which `Code` does not
      -- represent.
      --
      -- The receipt says what RAN, so it carries the functor word's OWN
      -- labels beside the functor's name (2026-09-12).  Before this,
      -- `checkFunctorWord` tested `eIO` alone, so a `Recursive`-labelled word
      -- — a `fix`-built functor — ran at elaboration (fuel-bounded) and
      -- its `Recursive` escaped: the expansion said nothing about it.  `IO`
      -- cannot reach here (`checkFunctorWord` refuses it), so in
      -- practice this mints `Recursive` and any receipt the word itself wears.
      let wordLabels w =
            case parseProgramIn (rcDatas (ecRefl ctx)) (functorExtSrc w)
                   >>= inferTermIn (ecEnv ctx) of
              Right (Arrow _ _ (Eff ls _)) -> S.toList ls
              _                            -> []
          -- Every `with` that CHANGED something mints, models
          -- included: `def polyD with Duals = poly` says WHICH model
          -- read the template, which is provenance in exactly the
          -- sense a functor's receipt is.  An INSTANTIATING scope
          -- mints too — it is still a model reading a body.  A model
          -- that both renames and transports (`with Circuits`) mints
          -- if EITHER action changed the code: one scope, one receipt.
          -- The one scope that still never mints is a model's own
          -- component (`ecSelf`): the `with I` wrapping a slot body
          -- resolves names, it does not apply the model to itself, and
          -- a slot's declared arrow carries no label.  That filter
          -- stays: a slot body that names a SIBLING slot IS changed by
          -- the rename (`add` → `Fwd@add`), so image membership alone
          -- would mint there and `checkInstance` would refuse the body
          -- for carrying its own model's label.
          mine  = [ n | n <- renamed ++ based ++ transported
                      , n `notElem` ecSelf ctx ]
          -- `with Recursive` mints like every other scope: the knot it
          -- tied carries the label too, and a set unions to one.  It
          -- ties no knot when the body never names the def, and then
          -- there is nothing to mint.
          marks = nub ([ receiptName recLabel | b' /= b0 ]
                       ++ map receiptName mine
                       ++ concat [ receiptName f : map receiptName (wordLabels w)
                                 | (f, w) <- walked ])
      pure (foldr (Seq 0 . Prim) expanded marks)
    -- `in` declares what a def IS, so it is consumed where a def is
    -- recorded (`addDef`) and never reaches here except out of place.
    go (In ns _) = Left $ "`in " ++ unwords ns ++ "` may only be a def's "
                       ++ "own header clause, left of the `=`: it says "
                       ++ "what the def is a morphism of, and a def is "
                       ++ "one thing.  `with` is the clause that applies."
    go (Seq n a b)     = Seq n <$> go a <*> go b
    go (Tensor ts)     = Tensor <$> mapM go ts
    go (Quote t)       = Quote <$> go t
    go (Alts cs r)     = Alts <$> mapM go cs <*> pure r
    go (OpenAbs sl h b) = OpenAbs sl h <$> go b
    -- `@` is the compiler's character.  This walk sees the SOURCE
    -- (expansions are spliced after it and never re-walked), so
    -- rejecting the character here is what makes a minted label
    -- evidence and a slot reachable only through its scope.  One rule
    -- for both: a receipt gets the sharper message it has always had.
    go (Prim n)
      | not (isLitAtom n), Just f <- receiptLabel n =
          Left $ n ++ " is the receipt of `with " ++ f
              ++ "`, not a word: a label is minted by a scope, never "
              ++ "written by hand"
      | not (isLitAtom n), '@' `elem` n, not (ecGen ctx)
      , takeWhile (/= '@') n `elem` ecTables ctx =
          Left $ "`" ++ n ++ "` is the compiler's spelling of a table's "
              ++ "insides: a `table` generates `load" ++ takeWhile (/= '@') n
              ++ "` and `header" ++ takeWhile (/= '@') n
              ++ "`, and those are the only words it puts in scope"
      | not (isLitAtom n), '@' `elem` n, not (ecGen ctx) =
          Left $ "`" ++ n ++ "` is the compiler's spelling of a slot: "
              ++ "reach it with `with " ++ takeWhile (/= '@') n ++ "`"
    go t               = Right t

    -- a Str literal rides as a Prim whose name begins with a quote, and
    -- its TEXT is not a name: `"a@b"` is a string, and a generated
    -- word carries slot names inside literals it parses at runtime
    isLitAtom ('"' : _) = True
    isLitAtom _         = False

-- Templates, phase one of elaboration.
--
-- A def whose `in` clause names a THEORY is a body waiting for a model;
-- a `with <model>` scope it stands inside supplies one.  The expansion
-- runs BEFORE renaming, routing and functors, so an expanded body is
-- elaborated by every scope it landed in exactly as if it had been
-- written there — including a resource scope between the model and the
-- call.
--
-- The scope the expansion lands in INSTANTIATES and does not transport:
-- the body is already a morphism of the theory, so the model only says
-- what its slot names mean (see `Apply`, 2026-09-16).
--
-- `scope` is the enclosing models, innermost first, so nested
-- scopes resolve innermost-first with no extra rule.  `busy` is the
-- templates currently being expanded: expansion is inlining, so a
-- template that calls itself would not terminate, and says so.
expandTemplates :: ElabCtx -> [(String, String)] -> [String] -> Term
                -> Either String Term
expandTemplates ctx scope busy = go
  where
    go (With ap ns b) =
      let inner = [ (n, th) | n <- ns, Just (th, _) <- [lookup n (ecSlots ctx)] ]
      in With ap ns <$> expandTemplates ctx (inner ++ scope) busy b
    go (In ns b) = In ns <$> expandTemplates ctx scope busy b
    go (Prim n)
      | Just (th, body) <- lookup n (ecTmpls ctx) =
          if n `elem` busy
            then Left $ "template " ++ n ++ " calls itself: a template is "
                     ++ "expanded at the call, so it cannot recurse"
            else case [ i | (i, t) <- scope, t == th ] of
              (i : _) -> With Instantiating [i]
                           <$> expandTemplates ctx ((i, th) : scope) (n : busy) body
              []      -> Left $ n ++ " needs a model of " ++ th
                             ++ " in scope (`with <model>` before calling it)"
    go (Seq n a b)      = Seq n <$> go a <*> go b
    go (Tensor ts)      = Tensor <$> mapM go ts
    go (Quote t)        = Quote <$> go t
    go (Alts cs r)      = Alts <$> mapM go cs <*> pure r
    go (OpenAbs sl h b) = OpenAbs sl h <$> go b
    go t                = Right t

-- `in X` declares MEMBERSHIP, and there are exactly two things a def
-- can be a morphism of: a THEORY (the def is a template, waiting for a
-- model to say what its slot names mean) and a MODEL WITH A CARRIER (the
-- def is a hand-built word of that category, entered without transport).
-- Every other name is refused here, by kind, with the clause to write
-- instead — because the confusion `in` exists to end is "declare"
-- against "apply", and `with` is the clause that applies.
inTarget :: [String] -> [Transport] -> SlotTable -> [(String, String)]
         -> [BaseInstance] -> [String] -> String -> Either String Transport
inTarget thNames trans slots funcs bases resources n
  -- A RESOURCE is asked FIRST, because since stage 7b it also names the
  -- model its declaration generated, and the answer a user needs is the
  -- one about the resource they wrote.  There is nothing to inhabit
  -- either: a representable fibre's carrier is CANCELLED, so no def
  -- ever holds one.
  | n `elem` resources =
      Left $ pre ++ "names a resource, and a resource is threaded through "
          ++ "a body.  Write `with " ++ n ++ "`."
  | (m : _) <- [ m | m <- trans, tpName m == n ] = Right m
  | n `elem` thNames = Left $ internal ++ "a theory reached inTarget"
  | Just (th, _) <- lookup n slots =
      Left $ pre ++ "names a model of " ++ th ++ " in the base: it has no "
          ++ "carrier to build \8212 write `with " ++ n ++ "`, or `in " ++ th
          ++ "` for a template."
  | isJust (lookupBase n bases) =
      Left $ pre ++ "names a model of Base — a rewriting of the "
          ++ "ambient presentation, which is applied, not inhabited.  "
          ++ "Write `with " ++ n ++ "`."
  | isJust (lookup n funcs) =
      Left $ pre ++ "names a functor, and a functor is applied to a body, "
          ++ "not inhabited by one.  Write `with " ++ n ++ "`."
  | otherwise =
      Left $ pre ++ "names nothing declared at this point.  `in` takes a "
          ++ "THEORY (this def is then a template, instantiated by whatever "
          ++ "`with <model>` calls it) or a MODEL WITH A CARRIER (this def "
          ++ "is then a word of that category, built by hand)."
  where
    pre      = "`in " ++ n ++ "` "
    internal = "internal: "

-- What `in K` promises, checked against the arrow that came out.  A
-- word of a category builds one carrier out of NOTHING — `• ⇒ K(a, b)` —
-- because that is the shape the transport pass whiskers and hands to
-- `thenP`.  A WRITTEN expectation against an inferred arrow: invariant
-- five's carve-out, the same one an exit's declared type gets.
--
-- Note what is NOT here: a label.  A hand-built word displays as the
-- carrier it is (`• ⇒ Circuit(Int, Int)`), unfolded, because the fold
-- says "this went through K" and this one did not.  Membership is the
-- carrier in the type plus the entry in the K-word table.
isKWordShape :: Transport -> Arrow -> Bool
isKWordShape tp (Arrow i o _) = case (i, o) of
  (SEnd, SCons (TData c [_, _]) SEnd) -> c == tpCarrier tp
  _                                   -> False

-- ...and when it is neither that nor a use of one of M's words, the
-- header did nothing at all, which is worth saying.
checkKWordShape :: Transport -> String -> Bool -> Arrow -> Either String ()
checkKWordShape tp nm usedWord arr
  | isKWordShape tp arr || usedWord = Right ()
  | otherwise = Left $
      "`in " ++ tpName tp ++ "`: " ++ nm ++ " neither builds one of "
        ++ tpName tp ++ "'s carriers — `• ⇒ " ++ tpCarrier tp
        ++ "(a, b)`, which is what a morphism of the category is — nor "
        ++ "uses any of " ++ tpName tp ++ "'s words, so the header did "
        ++ "nothing: " ++ nm ++ " is " ++ show (normalizeArrow arr)
        ++ ".  Take the inputs inside the carrier ("
        ++ fromMaybe "the embedding" (tpEmbed tp)
        ++ " embeds a program), or drop the header and let `with "
        ++ tpName tp ++ "` transport the def."

-- the Term-level twin of renameSlots: within a `with Inst` scope every
-- occurrence of one of the theory's operations means THIS model's
partitionEithers :: [Either a b] -> ([a], [b])
partitionEithers xs = ([ a | Left a <- xs ], [ b | Right b <- xs ])

renameSlotsT :: String -> [String] -> Term -> Term
renameSlotsT inst slots = renameWordsT [ (n, slotDefName inst n) | n <- slots ]

-- The renaming itself, over an arbitrary word table: `with Inst` sends a
-- slot name to that model's def, and `with Opt` (a model of
-- `Base`) sends a generator to its image.  ONE walk for both, so both
-- enter quotations and rows — and a row's RESIDUAL flag rides across
-- untouched, since renaming a word cannot change which alternatives are
-- covered.
renameWordsT :: [(String, String)] -> Term -> Term
renameWordsT tbl = go
  where
    go (Prim n) | Just n' <- lookup n tbl = Prim n'
    go (Seq n a b)      = Seq n (go a) (go b)
    go (Tensor ts)      = Tensor (map go ts)
    go (Quote t)        = Quote (go t)
    go (Alts cs r)      = Alts (map go cs) r
    go (With ap ns b)   = With ap ns (go b)
    go (In ns b)        = In ns (go b)
    go (OpenAbs sl h b) = OpenAbs sl h (go b)
    go t                = t

-- OBJECT-MAPPED TRANSPORT (stage 7c, 2026-09-17).
--
-- `with Mod` for `model Mod in Base(Int ↦ Mod7 via reduce)` is the
-- action of a functor whose object map is not the identity, so it is
-- not a renaming: every atom is asked what the functor does to it, and
-- there are exactly five answers.
--
--   1. THE TABLE.  A generator the model names goes to its image, and
--      the image is a PROGRAM, inlined here and re-inferred where it
--      lands (so each use gets its own principal type, exactly as a
--      template's expansion does).
--   2. A LITERAL of the mapped type goes to `lit ; c`.  The literal
--      family is the one class of generator a table cannot name —
--      there are infinitely many and none of them is a word — which is
--      why `via` is part of the head and not a row of the table.
--   3. A WORD WHOSE SCHEME NEVER MENTIONS A passes through untouched.
--      The functor is the identity off A; this is the type-directed
--      part, and it is what makes `with M` twice the identity the
--      second time (there is no A left to map) and `with M` then
--      `with N` compose.
--   4. A WORD THAT MENTIONS A AND HAS A BODY is UNFOLDED: F(def) =
--      F(body), cached once per def per model as `M@def`.  This is the
--      piece of machinery beyond a table check, and it is why this is
--      a stage: a def called under the scope is transported too, and
--      so is everything it calls.  `fix` transports as structure —
--      the normalizer already enters quotations — so a `Recursive` def
--      comes along with no case of its own.
--   5. A WORD THAT MENTIONS A WITH NEITHER, under a declared
--      RETRACTION, is DERIVED BY CONJUGATION: one `r` per A input
--      wire, one `c` per A output wire.  With no retraction it is
--      REFUSED BY NAME, with the fix.
objTransportT :: ElabCtx -> Instance -> Term -> Either String Term
objTransportT ctx inst = go []
  where
    om    = head (inObjMap inst)
    nm    = inName inst
    datas = rcDatas (ecRefl ctx)
    -- a `data` declaration's artifacts are GENERATORS, not defs: their
    -- bodies are the compiler's own wiring and unfolding them would
    -- transport the representation rather than the word.  They take an
    -- image, a conjugation or a refusal like any other generator.
    arts  = concatMap (map fst . fst . dataDeclArtifacts) datas
    here  = baseHere nm

    go bound (Prim n)
      | n `elem` bound                          = Right (Prim n)
      | Just img <- lookup n (inBindings inst)   = imageTerm here datas img
      | isLitOfA n                               =
          Right (Seq 0 (Prim n) (Prim (omVia om)))
      | otherwise = case M.lookup n (ecEnv ctx) of
          Nothing -> Right (Prim n)      -- a binder, an injection, a receipt
          Just sc ->
            let arr = runInfer0 (instantiate sc) in
            if not (mentionsTy (omFrom om) arr) then Right (Prim n)
            else if n `notElem` arts && M.member n (ecRun ctx)
              then Right (Prim (slotDefName nm n))
              else case omBack om of
                Just r  -> conjugate n r arr
                Nothing -> Left (noImage n arr)
    go bound (Seq k a b)      = Seq k <$> go bound a <*> go bound b
    go bound (Tensor ts)      = Tensor <$> mapM (go bound) ts
    go bound (Quote t)        = Quote <$> go bound t
    go bound (Alts cs r)      = Alts <$> mapM (go bound) cs <*> pure r
    go bound (With ap ns b)   = With ap ns <$> go bound b
    go bound (In ns b)        = In ns <$> go bound b
    go bound (OpenAbs sl h b) =
      OpenAbs sl h <$> go ([ x | Just x <- sl ] ++ bound) b

    isLitOfA n = case omFrom om of
      TInt   -> isIntLiteral n
      TFloat -> isFloatLiteral n
      TStr   -> isStrLiteral n
      TSym   -> isSymLiteral n
      _      -> False        -- a NOMINAL A has no literals at all

    -- `r … r ; g ; c … c`: the functor's value on a generator it was
    -- not given, read off the generator's own arrow.  Note what it is
    -- NOT: `r ; c` is only an idempotent unless `c` is an iso, so a
    -- conjugated word sees B only through `c`'s image.
    conjugate n r (Arrow i o _) = do
      ins  <- maybe (Left (openErr n)) Right (closedWires i)
      outs <- maybe (Left (openErr n)) Right (closedWires o)
      let pre  = stage [ if t == omFrom om then r        else "_" | t <- ins ]
          post = stage [ if t == omFrom om then omVia om else "_" | t <- outs ]
      Right (foldr1 (Seq 0) (pre ++ [Prim n] ++ post))

    stage ws
      | all (== "_") ws = []
      | [w] <- ws       = [Prim w]
      | otherwise       = [Tensor (map Prim ws)]

    mapLine = show (omFrom om) ++ " " ++ mapsTo ++ " " ++ show (omTo om)

    openErr n = here ++ "`" ++ n ++ "` cannot be derived by conjugation: "
             ++ "its arrow is open, and there is no way to write one `"
             ++ fromMaybe "r" (omBack om) ++ "` per " ++ show (omFrom om)
             ++ " wire under a stack nobody has counted.  Give `" ++ n
             ++ "` an image."

    noImage n arr = "`" ++ n ++ "` has no image under model " ++ nm ++ ": "
                 ++ nm ++ " maps " ++ mapLine ++ ", and `" ++ n ++ " : "
                 ++ show (normalizeArrow arr) ++ "` mentions "
                 ++ show (omFrom om) ++ " — so the functor has nothing to "
                 ++ "send it to.  Add `" ++ n ++ " = …` to `model " ++ nm
                 ++ "`, declare a retraction (`via " ++ omVia om
                 ++ ", r` with `r : " ++ show (omTo om) ++ " ⇒ "
                 ++ show (omFrom om)
                 ++ "`) so it is derived by conjugation, or do not call it "
                 ++ "here."

-- THE UNFOLDINGS A TRANSPORTED TERM ASKED FOR, deepest first.
--
-- `M@def` is a generated WORD, minted once per def per model and
-- installed beside the def whose scope asked for it — which is what
-- makes the unfolding a CACHE rather than an inlining: `M@poly` is one
-- word in `:defs`, with one type, however many times it is called.
-- The closure terminates because a def is not in scope in its own body
-- (5a½), so the call graph a body reaches is a DAG.
objGenDefs :: ElabCtx -> Term -> Either String [(String, Term)]
objGenDefs ctx t0 = snd <$> foldM want ([], []) (calls t0)
  where
    objs  = [ b | b <- ecBases ctx, not (null (inObjMap b)) ]
    calls t = [ (b, f) | n <- nub (primsIn t), b <- objs
                       , Just f <- [stripPrefix (inName b ++ "@") n] ]
    want acc@(seen, made) (b, f)
      | g `elem` seen || M.member g (ecEnv ctx) = Right acc
      | otherwise = do
          e <- maybe (Left (baseHere (inName b) ++ "`" ++ f
                         ++ "` has a scheme but no body to unfold"))
                     Right (M.lookup f (ecRun ctx))
          body <- objTransportT ctx b (deBody e)
          (seen', made') <- foldM want (g : seen, made) (calls body)
          Right (seen', made' ++ [(g, body)])
      where g = slotDefName (inName b) f

-- ...and each of them checked and entered exactly as a def is: its
-- own principal type, its own runtime entry, its own `:doc` line.
objGenEntries :: Env -> RunDefs -> Map String String -> [(String, Term)]
              -> Either String ( Env, RunDefs, Map String String
                               , [(String, Scheme, Term)] )
objGenEntries env0 run0 docs0 = foldM step (env0, run0, docs0, [])
  where
    step (e, r, d, acc) (gname, gterm) = do
      (garr, gsubs) <- inferTermSubAt 0 e gterm
      let gsc     = generalizeWith e gsubs garr
          (mn, f) = break (== '@') gname
      Right ( M.insert gname gsc e
            , extendRunDefs r [(gname, arityOf gsc, openOf gsc, gterm)]
            , M.insert gname ("the image of `" ++ drop 1 f
                               ++ "` under model " ++ mn
                               ++ " \8212 F(def) = F(body), unfolded once") d
            , acc ++ [(gname, gsc, gterm)] )

-- INFERRED ROUTING (stage 7b, 2026-09-17).
--
-- A def is ROUTED for a resource when the scheme of an atom in its
-- body -- read from the PREFIX SCOPE, fixed before this def is touched
-- -- carries that resource as its deepest wire on BOTH sides.  The
-- wire is then padded under every other stage exactly as if `with E`
-- had been written, the def's arrow becomes `E \931 \8658 E \931\8242`, and its
-- CALLERS are routed the same way, transitively, until the wire meets
-- an INSTALL SITE (a written seed) or a HANDLER (a discharge).  A
-- resource word originates its label at the leaf, exactly as the four
-- io prims do, and the label propagates by row unification as every
-- label does.
--
-- INVARIANT FIVE is untouched.  This reads the schemes of CALLEES in
-- the prefix scope -- as good as written, the same licence `typeOfCode`
-- and the 5c\189 strength routing already have -- and never the manifest
-- of the def being elaborated.
--
-- Two guards, both about not routing a wire that is already placed:
--
--   * THE CONSTRUCTOR EXCEPTION (syntactic, two atoms).  A body that
--     names `E` or `unE` is handling the wire itself -- an install site
--     or a handler -- so padding would add a second wire beside the one
--     it holds.  This is what keeps the handler idiom working
--     unchanged: `collectLog` seeds, `note` rolls, and neither is
--     routed.
--   * ALONE IN ITS STAGE.  The atom must BE the stage, which is the
--     one shape the routing pass can place (`elabScope`'s
--     one-resource-operation rule).  A stage that writes its own `_`
--     and `...` around the atom is threading BY HAND and says so --
--     `examples/resources.braid`'s `scoreByHand` and `_ bump ...` are
--     exactly that, and they keep the types they have.  (This guard is
--     not in design-7b.md \167 4i as written; it is what makes "routed
--     exactly as if `with E` were written" true of the cases where
--     `with E` would have worked, and leaves hand-threading alone.)
--
-- `with E` stays legal, is exactly what this does -- routing is
-- idempotent -- and is the explicit OVERRIDE for the one rare edge: a
-- def that receives the carrier as a VALUE through a binder, without
-- naming the constructors, and also calls a resource word.  Inference
-- would route it and it would fail loudly with two `E` wires; the
-- header says what is meant.  Never silent: the carrier is nominal, a
-- `Str` is never a `Log`, and a missing install stays *you forgot to
-- install*.
inferRouting :: Env -> [String] -> Term -> Maybe (String, [String])
inferRouting env resources body =
  case sortOn (negate . length . snd) candidates of
    (c : _) -> Just c
    []      -> Nothing
  where
    named = primsIn body
    candidates =
      [ (n, run)
      | (_, [Prim n]) <- spineLines body
      , Just (Forall _ _ _ _ _ _ (Arrow i o _)) <- [M.lookup n env]
      , let run = leadingRes resources i
      , not (null run)
      , run == leadingRes resources o
      , and [ c `notElem` named | r <- run, c <- [r, "un" ++ r] ] ]

-- THE RESOURCE MODEL'S FUSED EVALUATOR (stage 7b restates this).
--
-- `with Log Counter` is transport into the models `resource Log` and
-- `resource Counter` generate, and this is what their `embed` and
-- `compose` come to once the `R@k` wrapper is cancelled: `embed [s]`
-- is `_^k s ...` and `compose` is nothing at all, because composition
-- in a representable fibre IS base composition of representatives.
-- Everything here that transport does not do \8212 the claim assertion,
-- the one-resource-op stage, the whole-scope word, the two refusals \8212
-- is the part of the scope that is about the SEGMENT rather than about
-- the functor, and the segment is an ordered object the grade cannot
-- hold.  See design-7b.md §3.2 and `runTransport`'s first clause.
elabScope :: Env -> [String] -> Term -> Either String Term
elabScope env rs body = do
  stages <- mapM routeStage (spineLines body)
  -- `with Log Counter` is a CLAIM about the incoming wires, so make it
  -- one: `unLog >> Log` is the identity on a Log and typechecks on
  -- nothing else.  Without this a body that never touches a resource
  -- would leave its wires unconstrained, and the scope would be padding
  -- rather than a statement.
  -- THE MINT, ON THE CLAIM (stage 7b commit 6).  `with R` puts `R` on
  -- the manifest of everything it elaborated, exactly as every other
  -- `with` does — but the receipt must NOT be a stage of its own.
  -- `elabHeaders` prepends `with@F` as a STAGE for a functor, and a
  -- resource scope already emits one: this claim.  A second stage
  -- would make `examples/metered.braid` burn eight units instead of
  -- seven, because that file counts stages by burning fuel.  So the
  -- receipt is composed INTO the claim's own atom: one stage, one
  -- unit, and the label is on it.
  let assert = [ (0, [ Seq 0 (Prim (receiptName r))
                             (Seq 0 (Prim ("un" ++ r)) (Prim r))
                     | r <- rs ]
                      ++ [Prim "pass"]) | not (null rs) ]
  pure (chainLines (assert ++ concat stages))
  where
    k = length rs
    pad n = replicate n (Prim "_")
    swapStage d = pad d ++ [Prim "swap", Prim "pass"]

    schemeOf (Prim n) = M.lookup n env
    schemeOf _        = Nothing

    resUse a = case schemeOf a of
      Just (Forall _ _ _ _ _ _ (Arrow i _ _)) -> leadingRes rs i
      _                                     -> []

    -- an open-arity word must stay final, so it takes the remainder
    -- itself instead of us appending one (§13 rule 1)
    isOpen a = case schemeOf a of
      Just (Forall _ _ _ _ _ _ (Arrow i o _)) -> openTailedS i || openTailedS o
      _                                     -> False

    -- the stage's line rides through the rewrite: every stage this
    -- one becomes reports the line this one was written on
    routeStage (ln, atoms0) = map ((,) ln) <$> routeAtoms atoms0

    routeAtoms atoms0 =
      let atoms = [ a | a <- atoms0, a /= Prim "pass" ]
          tailPass = [ Prim "pass" | not (null atoms), not (isOpen (last atoms)) ]
          touching = [ (a, u) | a <- atoms, let u = resUse a, not (null u) ]
      in case touching of
        -- a pure stage: step over the resources, act, thread the rest
        [] -> Right [ pad k ++ atoms ++ tailPass ]
        -- a word that already threads exactly this scope's resources,
        -- in this order, is shaped like the stack: apply it with no
        -- routing at all.  This is what lets `with` scopes COMPOSE — a
        -- word written under `with Log Count` is callable under `with Log
        -- Count`, which is the difference between the scope being a
        -- notation and it being an abstraction.
        [(a, u)] | [a] == atoms, u == rs ->
          Right [ atoms ++ tailPass ]
        -- one resource operation, alone in its stage: bring its wire up
        -- beside the working wires, apply, put it back
        [(a, [r])] | [a] == atoms, Just j <- elemIndex r rs ->
          Right ( [ swapStage i | i <- [j .. k - 2] ]
               ++ [ pad (k - 1) ++ [a] ++ tailPass ]
               ++ [ swapStage i | i <- reverse [j .. k - 2] ] )
        [(a, u)] | [a] == atoms ->
          Left $ "`with`: " ++ renderTerm a ++ " threads " ++ unwords u
              ++ ", but this scope is over " ++ unwords rs
              ++ "; the elaborator routes one resource per stage, or a \
                 \word threading the whole scope unchanged"
        _ -> Left $ "`with`: a stage may contain at most one resource \
                    \operation, and it must be alone — put "
                 ++ renderTerm (fst (head touching)) ++ " on its own line"

-- A law is a program that must be runnable on nothing and answer yes:
-- `• ⇒ Bool`.  Checked here so a malformed law is a declaration error
-- rather than a mystery at module start.
checkTestType :: Env -> String -> Either String ()
checkTestType env n = do
  sc <- maybe (Left $ "internal: missing test def " ++ n) Right (M.lookup n env)
  let Arrow i o _ = runInfer0 (instantiate sc)
      boolTy = TSum (RCons SEnd (RCons SEnd RNil))
  case solve [CEqStack i SEnd, CEqStack o (SCons boolTy SEnd)] of
    Right _ -> Right ()
    Left _  ->
      Left $ "test '" ++ fromMaybe n (testParts n) ++ "' must be a program "
          ++ "with type `\8226 \8658 Bool`, but is "
          ++ show (normalizeArrow (runInfer0 (instantiate sc)))

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

-- A model becomes ordinary defs: one per slot, one per law.  The
-- slot bodies are the user's programs with the model's own slots in
-- scope (so a law may call `op` and mean this model's `op`), which
-- is the same renaming `with` performs — resolution once, not per call.
instanceDefs :: [Theory] -> Instance
             -> Either String [(String, DefHdr, String, Maybe String)]
instanceDefs theories inst = do
  th <- theoryOf theories (inTheory inst)
  ext <- case thIn th of
           Just d  -> Just <$> theoryOf theories d
           Nothing -> Right Nothing
  let slotNames = map fst (thSlots th)
      given     = map fst (inBindings inst)
  case [ n | n <- slotNames, n `notElem` given ] of
    (n : _) -> Left $ "model " ++ inName inst ++ ": no binding for '"
                   ++ n ++ "' (declared by theory " ++ thName th ++ ")"
    [] -> Right ()
  case [ n | n <- given, n `notElem` slotNames ] of
    (n : _) -> Left $ "model " ++ inName inst ++ ": '" ++ n
                   ++ "' is not an operation of theory " ++ thName th
    [] -> Right ()
  -- Each generated def is wrapped in its OWN model's scope, so the
  -- Term-level renaming does the work.  Renaming the source text
  -- instead would have to re-implement tokenization — `op)` is not the
  -- word `op` — and would get it subtly wrong.
  -- ...and a FAMILY INSTANCE's slot bodies are wrapped in the
  -- PARAMETER's scope instead (2026-09-15): `model Fwd(R : Smooth(a,
  -- g))`'s bodies are templates over R's theory, so every slot name in
  -- them is R's — `add` inside `add` included, which is what makes the
  -- body unambiguous without a self-reference rule.  The LAWS still run
  -- in the instance's own scope: they are the theory's, they are checked
  -- AT EACH INSTANTIATION, and they must name this model's slots.
  let rename    = DefHdr Nothing [inName inst]
      hdr' = case inScope inst of
        []  -> rename
        sc  -> DefHdr Nothing sc
      slots  = [ ( slotDefName (inName inst) n, hdr', body
                 , Just ("slot '" ++ n ++ "' of " ++ inName inst) )
               | (n, body) <- inBindings inst ]
      -- An INHERITED law runs when the model can STATE it: every slot of
      -- the extended theory that the law names is one this theory
      -- declares.  A theory that takes the doctrine's composition and
      -- not its `first` is audited for associativity and not for
      -- naturality, which is exactly what it claimed.
      inherited = case ext of
        Nothing -> []
        Just dt -> [ l | l@(_, src) <- thLaws dt
                       , all (`elem` slotNames)
                             [ w | w <- lawWords src
                                 , isJust (lookup w (thSlots dt)) ] ]
      laws   = [ ( lawDefName (inName inst) nm, rename, body
                 , Just ("law '" ++ nm ++ "' of " ++ inName inst
                         ++ " — runs at module start") )
               | (nm, body) <- thLaws th ++ inherited ]
  pure (slots ++ laws)

-- A NATURAL TRANSFORMATION BETWEEN MODELS:
-- `transformation Len : ListMonoid \8658 IntSum = len`.
--
-- Two models of ONE theory, and a base word between their carriers.
-- The claim is naturality: for every slot `s : s \8658 j` of the theory,
-- the square
--
--   A@s ; K(j)  =  K(s) ; B@s
--
-- commutes, where K at a stack is the component ON EACH WIRE that is
-- the theory's parameter and the identity on the rest — monoidal, so
-- at `a a` the component is `len len`.  Because the base is the FREE
-- category on the theory's generators, one square per generator is
-- complete: a morphism of presentations is determined on generators.
--
-- The arrow is written `\8658` because that is the arrow of every written
-- type in Braid (`->` is only its ASCII synonym there); a transformation
-- between models is an arrow between two named things, so it is written with
-- the arrow.
data Transformation = Transformation
  { tfName  :: String
  , tfFrom  :: String
  , tfTo    :: String
  , tfWords :: [String]
      -- ONE COMPONENT PER THEORY PARAMETER (2026-09-14), in the order
      -- the theory declares them.  A natural transformation between
      -- models of `Smooth(a, g)` is a component at `a` AND a component
      -- at `g` — `gradient : a \8658 g` has one at each end of its
      -- square — and a parameter whose type is the same in both models
      -- writes `id`, which is an ordinary word and needs no case.
  } deriving (Eq, Show)

-- one slot's square: the two sides as generated defs, and the sampled
-- law that decides it when the normalizer will not
data TransformationSquare = TransformationSquare
  { tsqSlot   :: String
  , tsqLhs    :: String
  , tsqRhs    :: String
  , tsqLaw    :: Maybe String
  , tsqWhy    :: String        -- why there is no sampled law, if there is none
  , tsqPoints :: Int           -- sample points the law runs at, if it has one
  , tsqTotal  :: Int           -- ...out of how many the theory's evidence offers
  , tsqExit   :: Bool          -- ...and whether it compares through the exit
  }

-- A square's sampled law: the def it becomes, its source, how many
-- EVIDENCE POINTS it runs at, how many the theory offers, and whether
-- the comparison goes through the theory's exit (it does not when the
-- theory declares none, and then `eq?` weighs the carriers themselves).
--
-- A point is one CHOICE OF ENTRY PER INPUT WIRE (2026-09-17).  Until
-- then a square ran at ONE point — the theory's FIRST nullary entry,
-- in declaration order — so a theory that happened to declare `zero`
-- before `sample` audited its squares at zero, where a false
-- homomorphism is true.  Evidence is now the CROSS PRODUCT of every
-- nullary entry over every input wire, capped at `sampleCap`.
data SampledLaw = SampledLaw
  { slName   :: String
  , slSrc    :: String
  , slPoints :: Int
  , slTotal  :: Int
  , slExit   :: Bool
  }

-- How many evidence points one square is run at, at most.  A theory
-- with e nullary entries audits a binary slot at e\178 points, and the
-- cap is what keeps a theory with a dozen entries from turning module
-- start into a benchmark.  The cap is SAID rather than silent: over it
-- the verdict reads `sampled (64 of 169 points; —)`, so an audit
-- never reports evidence it did not take.
sampleCap :: Int
sampleCap = 64

-- What the checker decided about one square, kept so that
-- `:transformations` READS the verdict rather than deciding it again.
-- `TVProved` is `sameCode` — for every input; `TVSampled n tot why`
-- is the theory's own evidence, at n of the tot points it offers (a
-- square with no inputs runs at none), and `why` is the normalizer's
-- refusal in a few words — WHY the samples had to decide it
-- (2026-09-14).  A square the normalizer decided FALSE is not sampled
-- at all: the transformation is refused, naming the slot.
data TransformationVerdict = TVProved | TVSampled Int Int String
  deriving (Eq, Show)

-- A declared transformation and its verdicts, slot by slot, in the
-- theory's order.  A transformation whose square neither proved nor
-- sampled never gets
-- one of these: the module was refused.
data TransformationInfo = TransformationInfo
  { tiName    :: String
  , tiFrom    :: String
  , tiTo      :: String
  , tiSquares :: [(String, TransformationVerdict)]
  , tiNoExit  :: [String]   -- slots whose carriers `eq?` weighed directly
  } deriving (Eq, Show)

-- A FAMILY, as `:defs` prints it.  It is not a def and not a model: it
-- is what `with F(M)` applies, so the line says how to apply it — a
-- session that has `:import`ed a file gets the spelling with the name.
renderFamily :: Instance -> String
renderFamily i =
  "model " ++ inName i ++ "("
    ++ intercalate ", " [ mpTheory p | p <- inParams i ]
    ++ ") in " ++ inTheory i ++ "   (a FAMILY \8212 apply it: `with "
    ++ inName i ++ "("
    ++ intercalate ", " [ "<model of " ++ mpTheory p ++ ">" | p <- inParams i ]
    ++ ")`)"

-- one verdict, as `:transformations` and `:doc` print it.  A square with no
-- inputs is run at no sample points and simply reads `sampled`.
showVerdict :: TransformationVerdict -> String
showVerdict TVProved            = "proved"
showVerdict (TVSampled n tot why)
  | null parts = "sampled"
  | otherwise  = "sampled (" ++ intercalate "; " parts ++ ")"
  where
    parts = [ points | n > 0 ] ++ [ why | not (null why) ]
    -- the cap is SAID: `64 of 169 points` never claims the other 105
    points | n < tot   = show n ++ " of " ++ show tot ++ " points"
           | otherwise = show n ++ " point" ++ (if n == 1 then "" else "s")

-- WHY the theory's samples had to decide a square, in a few words, to
-- sit beside `sampled`.  Every refusal names its own case (\167 12.9);
-- this keeps the naming half and drops the explanation, which
-- `sameCode` prints in full if it is asked directly.
shortReason :: String -> String
shortReason msg = phrase (clip (dropPre "outside the structural fragment: " msg))
  where
    dropPre p m  = fromMaybe m (stripPrefix p m)
    -- the explanatory tail is parenthetical, an em dash, or a colon
    clip m       = foldr shorter m [ h | sep <- [" (", " \8212 ", ": "]
                                       , Just (h, _) <- [breakOnStr sep m] ]
    shorter a b  = if length a < length b then a else b
    phrase m
      | pre "`ev` of a value"                       = "ev of an open wire"
      | pre "a case split under an eta comparison"  = "case split under eta"
      | pre "quotations nested past"                = unwords (drop 1 (words m))
      | pre "the case tree grew past"               = "case tree past "
                                                        ++ unwords (drop 4 (words m))
      | pre "a binder abstraction elimination"      = "an open binder"
      | pre "the normalizer ran out of steps"       = "out of steps"
      | otherwise                                   = m
      where pre p = p `isPrefixOf` m

-- ...and what `sameCode` answering FALSE means for a square: the two
-- sides are different morphisms of the FREE category on the model's
-- words, which is not the same as different in the model — the model's
-- words satisfy the theory's laws, and the normalizer has none of them.
-- That is what the theory's own evidence is for.
freeDiffer :: String
freeDiffer = "differ in the free category"

-- A declared transformation and what the checker decided about each of
-- its squares, as `:transformations` prints it.  The verdicts are READ off the
-- module the declaration was checked in, never decided again here.
renderTransformation :: TransformationInfo -> String
renderTransformation mi =
  intercalate "\n"
    ( (tiName mi ++ " in " ++ tiFrom mi ++ " \8658 " ++ tiTo mi)
      : [ "  " ++ pad sl ++ showVerdict v | (sl, v) <- tiSquares mi ] )
  where
    width  = maximum (1 : map (length . fst) (tiSquares mi))
    pad sl = sl ++ replicate (width - length sl + 2) ' '

-- the same verdicts on ONE line, for `:doc`
transformationDocLine :: TransformationInfo -> String
transformationDocLine mi =
  "  squares: " ++ intercalate ", " (filter (not . null) [proved, sampled])
  where
    vs      = map snd (tiSquares mi)
    proved  = count (length [ () | TVProved <- vs ]) "proved"
    sampled = count (length [ () | TVSampled _ _ _ <- vs ]) "sampled"
    count 0 _    = ""
    count n what = show n ++ " " ++ what

transformationDefName :: String -> String -> String -> String
transformationDefName nm side slot = nm ++ "@" ++ side ++ "@" ++ slot

-- a generated side or square of a transformation's naturality square,
-- and the (transformation, slot) it came from
transformationNameParts :: String -> Maybe (String, String)
transformationNameParts n = case break (== '@') n of
  (mo, '@' : rest) -> case break (== '@') rest of
    (side, '@' : sl) | side `elem` ["lhs", "rhs", "square"] -> Just (mo, sl)
    _ -> Nothing
  _ -> Nothing

-- a generated square def, and the (transformation, slot) it came from
squareParts :: String -> Maybe (String, String)
squareParts n = case breakOnStr "@square@" n of
  Just (i, l) -> Just (i, l)
  Nothing     -> Nothing

breakOnStr :: String -> String -> Maybe (String, String)
breakOnStr pat = go ""
  where
    go _   []          = Nothing
    go acc r@(c : cs)
      | take (length pat) r == pat = Just (reverse acc, drop (length pat) r)
      | otherwise = go (c : acc) cs

-- `transformation Name in A \8658 B = word` \8212 a declaration line,
-- no block.
--
-- `in` and not `:` since 2026-09-16: the head says what the
-- transformation IS a member of \8212 the hom-set of Mod(T) from A to B
-- \8212 and `:` types a slot and nothing else.  `=` gives the body, and
-- `,` lists its components, exactly as everywhere else.
parseTransformationLine :: String -> Either String Transformation
parseTransformationLine l =
  case break (== '=') (takeWhile (/= '#') l) of
    (lhs, '=' : rhs)
      | Just ws@(_ : _) <- componentList rhs ->
          case words lhs of
            ("transformation" : nm : "in" : [a, arr, b])
              | arr `elem` ["\8658", "->", "\8594"] ->
                  Right (Transformation nm a b ws)
            ("transformation" : _ : rest) | (":" : _) <- rest -> Left colon
            _ -> case break (== ':') lhs of
              (hd, ':' : _) | ["transformation", _] <- words hd -> Left colon
              _ -> Left (malformed l)
    (_, '=' : rhs) | ';' `elem` rhs -> Left (separatorErr "components")
    _ -> Left (malformed l)
  where
    -- `= w` or `= w1, w2, …`: one word per theory parameter, in order
    componentList = mapM one . splitTopCommas
    one piece = case words piece of
      [w] -> Just w
      _   -> Nothing
    colon = "`:` types a slot and nothing else since 2026-09-16: a "
         ++ "transformation's head says which hom-set of Mod(T) it is "
         ++ "a member of \8212 write `transformation Name in ModelA "
         ++ "\8658 ModelB = word` (MANUAL \167\&8)"
    malformed t = "Malformed transformation declaration (want "
               ++ "`transformation Name in ModelA \8658 ModelB = word`, or "
               ++ "one word per theory parameter in order, `= w1, w2`): "
               ++ dropWhile isSpace t

-- Is this wire the theory's parameter \8212 the thing the component acts
-- on?  A wire parameter is the wire itself; a constructor parameter is
-- the hom-object applied to anything.
paramWire :: TyParam -> Ty -> Bool
paramWire (PWire (TV n)) (TVarTy (TV m)) = n == m
paramWire (PCon n _)     (TData m _)     = n == m
paramWire _              _               = False

-- The defs a transformation declaration contributes: the component under its
-- own name, the two sides of every square, and \8212 where the theory's
-- evidence allows it \8212 a sampled law per square.
transformationDefs :: [Theory] -> [Instance] -> Transformation
             -> Either String ( [(String, String, Maybe String)]
                              , [TransformationSquare] )
transformationDefs theories insts mo = do
  a  <- modelOf (tfFrom mo)
  b  <- modelOf (tfTo mo)
  if inTheory a == inTheory b then Right () else
    Left $ here ++ tfFrom mo ++ " models " ++ inTheory a ++ " and "
        ++ tfTo mo ++ " models " ++ inTheory b ++ ": a transformation is "
        ++ "a component between two models of ONE theory."
  th <- theoryOf theories (inTheory a)
  -- ONE COMPONENT PER PARAMETER, in the theory's order.  A theory with
  -- a parameterized exit (`gradient : a \8658 g`) has a square whose two
  -- ends live at different parameters, so a single component cannot
  -- draw it.
  ps <- components th
  built <- mapM (square th ps a b) (thSlots th)
  let word  = ( tfName mo, head (tfWords mo)
              , Just ("transformation " ++ tfName mo ++ " in " ++ tfFrom mo
                       ++ " \8658 " ++ tfTo mo ++ " \8212 the component, as "
                       ++ "an ordinary word") )
      defs  = concat [ [ (tsqLhs sq, l, note sq "the model's side")
                       , (tsqRhs sq, r, note sq "the component's side") ]
                       ++ [ (nm, src, note sq "the square, at the samples")
                          | (Just nm, Just src) <- [(tsqLaw sq, mlaw)] ]
                     | (sq, l, r, mlaw) <- built ]
  pure (word : defs, [ sq | (sq, _, _, _) <- built ])
  where
    here = "transformation " ++ tfName mo ++ ": "
    nm   = tfName mo
    note sq what = Just ("transformation " ++ nm ++ ", slot '" ++ tsqSlot sq
                          ++ "' \8212 " ++ what)
    modelOf n = case [ i | i <- insts, inName i == n ] of
      (i : _) -> Right i
      []      -> Left $ here ++ n ++ " is not a model declared at this point"
    joinSrc = intercalate " >> " . filter (not . null)

    -- the declaration's words, paired with the parameters they are
    -- components at.  One each, in order, or the refusal says so.
    components th
      | length (tfWords mo) == length (thParams th) =
          Right (zip (thParams th) (tfWords mo))
      | otherwise = Left $ here ++ "theory " ++ thName th ++ " has "
          ++ show (length (thParams th)) ++ " parameter"
          ++ (if length (thParams th) == 1 then "" else "s")
          ++ " and a natural transformation has ONE COMPONENT PER "
          ++ "PARAMETER, in order (" ++ show (length (tfWords mo))
          ++ " given).  A parameter whose type is the same in both "
          ++ "models writes `id`."

    -- the word this wire's parameter is a component at, if any
    wordFor ps w = listToMaybe [ n | (q, n) <- ps, paramWire q w ]

    -- the component at a stack: on each wire that is one of the
    -- theory's parameters, that parameter's word; on the rest, nothing.
    -- `""` is the identity.
    stageFor ps sName st = case closedWires st of
      Nothing -> Left $ here ++ "slot '" ++ sName ++ "' has an open stack, "
                     ++ "and a component is applied wire by wire.  A theory "
                     ++ "with a `...` slot needs its homomorphism written by "
                     ++ "hand."
      Just ws
        | all (isNothing . wordFor ps) ws -> Right ""
        | otherwise -> Right (unwords [ fromMaybe "_" (wordFor ps w)
                                      | w <- ws ])

    square th ps a b (sName, Arrow sIn sOut _) = do
      kIn  <- stageFor ps sName sIn
      kOut <- stageFor ps sName sOut
      let lhsS = joinSrc [slotDefName (inName a) sName, kOut]
          rhsS = joinSrc [kIn, slotDefName (inName b) sName]
          lhsN = transformationDefName nm "lhs" sName
          rhsN = transformationDefName nm "rhs" sName
      (mlaw, why) <- pure (sampledLaw th ps a b sName sIn sOut)
      pure ( TransformationSquare sName lhsN rhsN (fmap slName mlaw) why
                         (maybe 0 slPoints mlaw) (maybe 0 slTotal mlaw)
                         (maybe False slExit mlaw)
           , lhsS, rhsS, fmap slSrc mlaw )

    -- The square RUN at the theory's evidence: the standing pattern —
    -- `sample : \8226 \8658 a` supplies values, the theory's exit observes
    -- a carrier (comparing one directly is `eq?` on whatever it holds),
    -- and `eq?` decides.  `Nothing` carries the reason, which is what
    -- the refusal prints.
    --
    -- EVERY ENTRY, AND EVERY COMBINATION OF THEM (2026-09-17).  A slot
    -- with k input wires is run at the cross product of the entries
    -- that fill each one, and the law is the conjunction: one `false`
    -- anywhere refuses the square.  Reading only the first entry made
    -- the audit depend on the order the theory's slots were WRITTEN,
    -- which is not a fact about the models — a floor-halving `add`
    -- commutes at (0, 0) and nowhere else.
    sampledLaw th ps a b sName sIn sOut =
      case (closedWires sIn, closedWires sOut) of
        (Just ins, Just [out])
          | Just choices <- mapM sampleAtoms ins ->
              let obs    = observer out
                  combos = take sampleCap (sequence choices)
                  total  = product (map length choices)
                  sampled = or [ isJust (wordFor ps w) | w <- ins ]
                  at atoms =
                    let lhsRun = joinSrc [unwords atoms
                                         , slotDefName (inName a) sName
                                         , compAt sOut, obs]
                        rhsRun = joinSrc [unwords atoms, compAt sIn
                                         , slotDefName (inName b) sName, obs]
                    in "(" ++ lhsRun ++ ") (" ++ rhsRun ++ ") >> eq? >> "
                         ++ "(forget >> true | forget >> false) >> merge"
                  -- The conjunction, written the way the remainder
                  -- discipline wants it: `and : Bool Bool \8658 Bool` is
                  -- CLOSED, so each further point is grouped and
                  -- whiskered over the running verdict rather than
                  -- simply appended.  One point is written exactly as
                  -- it was before there were several.
                  src = case map at combos of
                          [p0]      -> p0
                          (p0 : ps') ->
                            joinSrc ( ("(" ++ p0 ++ ") (" ++ head ps' ++ ")")
                                      : "and"
                                      : concat [ ["_ (" ++ q ++ ")", "and"]
                                               | q <- drop 1 ps' ] )
                          []        -> "true"
              in ( Just (SampledLaw
                          (transformationDefName nm "square" sName)
                          src
                          (if sampled then length combos else 0)
                          (if sampled then total else 0)
                          (not (null obs)))
                 , "" )
          | otherwise ->
              (Nothing, "the theory declares no `sample : \8226 \8658 "
                          ++ intercalate "`/`\8226 \8658 "
                               [ pName q | (q, _) <- ps ]
                          ++ "` to supply its inputs with")
        (_, Just outs) | length outs /= 1 ->
          (Nothing, "it leaves " ++ show (length outs) ++ " wires, and a "
                      ++ "sampled square is compared with `eq?` at one")
        _ -> (Nothing, "its stacks are not closed")
      where
        compAt st = either (const "") id (stageFor ps sName st)
        -- EVERY atom that can fill this wire, in the theory's own
        -- declaration order.  `Nothing` is "the theory offers none",
        -- which is what the refusal reports.
        sampleAtoms w
          | isJust (wordFor ps w) =
              case map (slotDefName (inName a)) (sampleSlots w) of
                [] -> Nothing
                as -> Just as
          | TFn _ <- w            = Just ["[pass]"]
          | otherwise             = Nothing
        -- the ENTRIES of the source model that supply a value of THIS
        -- wire's parameter (`sample : \8226 \8658 a` feeds an `a`, and a
        -- second parameter would want an entry of its own).  ALL of
        -- them: the theory's evidence is what it declared, not what it
        -- declared first.
        sampleSlots w = nub
          [ n | (q, _) <- ps, paramWire q w
              , (n, Arrow i o _) <- thSlots th, i == SEnd
              , Just [w'] <- [closedWires o], paramWire q w' ]
        -- an EXIT of the TARGET model observes one \8212 whatever the
        -- parameter's kind.  A result that is not the carrier needs
        -- none; a carrier needs one whenever the theory declares one,
        -- because `eq?` on a carrier is `eq?` on whatever it holds, and
        -- on a quotation that is SYNTACTIC (2026-09-14: before this the
        -- exit was applied only for a constructor parameter, on the
        -- reasoning that `eq?` reaches an ordinary type \8212 it does,
        -- but `data Rev = (Float Fn\10216Float \8658 Grad\10217)` is an
        -- ordinary type holding a closure).  With no exit declared the
        -- carriers are compared directly, and a failure says so.
        observer out
          | isNothing (wordFor ps out) = ""
          | otherwise = maybe "" (slotDefName (inName b)) (exitSlot out)
        -- ...and it must FIT: `observe : k(Int, Int) \8658 Int` observes
        -- the result of `compose`, whose output is `k(a, c)`, and not
        -- the result of `first`, whose output is the hom-object at a
        -- PAIRING.  Unification is the test, at fresh variables.
        -- ...and an exit observes the carrier of the SAME parameter the
        -- result sits at: with two parameters, `observe : a \8658 Float`
        -- is not an exit for a `g`, and `fits` alone would say it was
        -- (two type variables unify with each other).
        exitSlot out = listToMaybe
          [ n | (q, _) <- ps, paramWire q out
              , (n, Arrow i o _) <- thSlots th
              , Just [w] <- [closedWires i], paramWire q w
              , Just ws <- [closedWires o], length ws == 1
              , all (isNothing . wordFor ps) ws
              , fits out w ]
        fits out w =
          let Arrow i' _ _ = runInfer0 (instantiate
                               (generalize M.empty (arrPure (SCons w SEnd) SEnd)))
          in case solve [CEqStack i' (SCons out SEnd)] of
               Right _ -> True
               Left _  -> False

-- What a component must be: the source model's carrier to the target's.
-- `k(a, b) \8658 k\8242(a, b)` for a hom-object, `A \8658 B` for a wire
-- parameter.  It is DECLARED in the sense that matters — the two model
-- heads wrote it — so a transformation's word can be forward-declared
-- at it,
-- exactly as a theory slot is.
componentArrows :: [Theory] -> [Instance] -> Transformation
                -> Either String [Arrow]
componentArrows theories insts mo = do
  a  <- modelOf (tfFrom mo)
  b  <- modelOf (tfTo mo)
  th <- theoryOf theories (inTheory a)
  if length (inArgs a) == length (thParams th)
       && length (inArgs b) == length (thParams th)
    then Right ()
    else Left $ here ++ "the two model heads do not fill theory "
             ++ thName th ++ "'s parameters"
  sequence (zipWith3 one (thParams th) (inArgs a) (inArgs b))
  where
    here = "transformation " ++ tfName mo ++ ": "
    -- A constructor parameter of arity n is applied to n fresh wires:
    -- `k(_, _)` gives `k(\945, \946) \8658 k\8242(\945, \946)`, and the
    -- arity-1 parameter a parameterized EXIT wants (`report : k(Int, b)
    -- \8658 d(b)`) gives `d(\945) \8658 d\8242(\945)`.  It used to write
    -- two, always, which refused every theory whose parameter was not a
    -- hom-object (2026-09-15).
    one (PCon _ ar) (IACon ca) (IACon cb) =
      let vs = [ SCons (TVarTy (TV v)) SEnd
               | v <- take (length ar) (map (: []) "\945\946\947\948\949\950") ]
      in Right (arrPure (SCons (TData ca vs) SEnd)
                        (SCons (TData cb vs) SEnd))
    one (PWire _) (IAStack sa) (IAStack sb) = Right (arrPure sa sb)
    one q _ _ = Left $ here ++ "theory parameter '" ++ pName q
             ++ "' and the models' arguments are not at one kind"
    modelOf n = case [ i | i <- insts, inName i == n ] of
      (i : _) -> Right i
      []      -> Left $ here ++ n ++ " is not a model declared at this point"

-- ...and the FIRST of them, which is the transformation's own type: the
-- declaration mints a word of its own name, and that word is the
-- component at the theory's first parameter (the carrier).
componentArrow :: [Theory] -> [Instance] -> Transformation -> Either String Arrow
componentArrow theories insts mo = do
  arrs <- componentArrows theories insts mo
  case arrs of
    (arr : _) -> Right arr
    []        -> Left $ "transformation " ++ tfName mo ++ ": theory "
                     ++ "declares no parameter for a component to sit at"

-- The component's own type, and the verdict on every square.  Run after
-- the module's defs are in: the squares are ordinary defs by then, so
-- the normalizer can be asked whether the two sides are the same
-- morphism, and where it cannot say, the sampled law does.
checkTransformation :: Env -> RunDefs -> [Theory] -> [Instance] -> Transformation
              -> [TransformationSquare] -> Either String TransformationInfo
checkTransformation env defs theories insts mo squares = do
  a  <- modelOf (tfFrom mo)
  b  <- modelOf (tfTo mo)
  th <- theoryOf theories (inTheory a)
  -- every component, at the parameter it sits at: the two model heads
  -- wrote its type, so it is DECLARED in the sense that matters
  wanteds <- componentArrows theories insts mo
  sequence_ [ oneComponent q w wanted
            | (q, w, wanted) <- zip3 (thParams th) (tfWords mo) wanteds ]
  vs <- mapM verdict squares
  pure (TransformationInfo (tfName mo) (tfFrom mo) (tfTo mo) vs
                  [ tsqSlot sq | sq <- squares
                              , isJust (tsqLaw sq), not (tsqExit sq) ])
  where
    here = "transformation " ++ tfName mo ++ ": "
    oneComponent q w wanted = do
      sc <- maybe (Left (here ++ "no word " ++ w)) Right (M.lookup w env)
      case subsumes sc wanted of
        Right () -> Right ()
        Left e   -> Left $ here ++ "the component " ++ w ++ " at parameter '"
                        ++ pName q ++ "' is "
                        ++ show (normalizeArrow (runInfer0 (instantiate sc)))
                        ++ " but a component from " ++ tfFrom mo ++ " to "
                        ++ tfTo mo ++ " there is "
                        ++ show (normalizeArrow wanted)
                        ++ " (" ++ e ++ ")"
    modelOf n = case [ i | i <- insts, inName i == n ] of
      (i : _) -> Right i
      []      -> Left $ here ++ n ++ " is not a model declared at this point"
    -- `false` and a REFUSAL are two different answers, and since
    -- 2026-09-14 they stay two (`fallbackFalse` used to make the second
    -- into the first).  `false` is *different as free programs*, which
    -- is a real answer about the free category and NOT an answer about
    -- the model \8212 the model's words satisfy the theory's laws, and
    -- the normalizer has none of them (`Transpose`'s squares are equal
    -- only up to the arithmetic of `fadd` and `fmul`).  So either
    -- answer sends the square to the theory's evidence, which is the
    -- only thing that knows the model; the verdict records WHICH answer
    -- it was, and a square with no evidence behind it is refused,
    -- naming the slot and saying which.
    verdict sq = case (termOf (tsqLhs sq), termOf (tsqRhs sq)) of
      (Just tl, Just tr) ->
        case sameProgram env defs defs tl tr of
          -- proved, for every input
          Right True  -> Right (tsqSlot sq, TVProved)
          -- decided FALSE as free programs.  With evidence to run, the
          -- evidence decides and the verdict says what the normalizer
          -- said; with none, there is nothing left to hope for and the
          -- square is refused as WRONG, naming the slot.
          Right False
            | isJust (tsqLaw sq) ->
                Right (tsqSlot sq, TVSampled (tsqPoints sq) (tsqTotal sq)
                                              freeDiffer)
            | otherwise -> undecided sq
                   ("' is FALSE \8212 `sameCode` decides the two sides are "
                     ++ "different programs of the free category, and there "
                     ++ "is no evidence that could say otherwise")
          -- the normalizer would not say: the samples decide it, and the
          -- verdict records what stopped the proof
          Left why
            | isJust (tsqLaw sq) ->
                Right (tsqSlot sq, TVSampled (tsqPoints sq) (tsqTotal sq)
                                              (shortReason why))
            | otherwise -> undecided sq
                   ("' does not decide \8212 `sameCode` cannot prove it ("
                     ++ shortReason why ++ ")")
      _ -> Left (here ++ "internal: missing square def for " ++ tsqSlot sq)
    -- a square with no verdict and no evidence, either way round: the
    -- refusal names the slot, says which of the two it is, and points at
    -- the evidence that would settle it
    undecided sq said =
      Left $ here ++ "the square for slot '" ++ tsqSlot sq ++ said
          ++ ", and it cannot be sampled: " ++ tsqWhy sq ++ ".  Add a "
          ++ "`sample` slot to theory " ++ inTheory (head
               [ i | i <- insts, inName i == tfFrom mo ])
          ++ ", or state the square as a law of the theory"
    termOf n = listToMaybe [ t | (dn, de) <- M.toList defs, dn == n
                               , let t = deBody de ]

-- The words a law's source mentions.  Tokenized, never scraped: `op)`
-- is not the word `op`, and a slot name inside a string literal is a
-- string.
lawWords :: String -> [String]
lawWords src = case tokenize src of
  Right toks -> nub [ n | TokIdent n <- toks, not (null n), head n /= '"' ]
  Left _     -> []

theoryOf :: [Theory] -> String -> Either String Theory
theoryOf ths n = case [ t | t <- ths, thName t == n ] of
  (t : _) -> Right t
  []      -> Left $ "Unknown theory: " ++ n

-- Every slot's inferred type must match what the theory declared, read
-- at this model's arguments.  This is the half of "audited model"
-- that does not need to run.
checkInstance :: Env -> [Theory] -> Instance -> Either String ()
checkInstance env theories inst = do
  th <- theoryOf theories (inTheory inst)
  if length (inArgs inst) /= length (thParams th)
    then Left $ "model " ++ inName inst ++ ": theory " ++ thName th
             ++ " expects " ++ show (length (thParams th)) ++ " argument(s)"
    else Right ()
  mapM_ (one th) (thSlots th)
  where
    one th (nm, declared) = do
      let dn = slotDefName (inName inst) nm
      sc <- maybe (Left $ "model " ++ inName inst ++ ": missing " ++ dn)
                  Right (M.lookup dn env)
      wanted <- slotArrowAt inst th declared
      -- SUBSUMPTION, not unification: the theory's variables are the
      -- CALLER's to choose, so a body that merely unifies at one choice
      -- (`drop 1 1` against `a ⇒ a a`) must be rejected.  This also
      -- compares the effect row, which the old stack-only check did not
      -- — an io body under a pure-declared slot used to pass, and
      -- `functor F = <that slot>` then broke the phase invariant.
      case subsumes sc wanted of
        Right () -> Right ()
        Left e   -> Left $ "model " ++ inName inst ++ ": slot '" ++ nm
                       ++ "' is " ++ show (normalizeArrow (runInfer0 (instantiate sc)))
                       ++ " but theory " ++ thName th ++ " declares "
                       ++ show (normalizeArrow wanted) ++ " (" ++ e ++ ")"

-- A slot's DECLARED type, with the theory's parameters replaced by this
-- model's arguments.
slotArrowAt :: Instance -> Theory -> Arrow -> Either String Arrow
slotArrowAt inst th (Arrow i o e) = do
  (tm, sm, rm, cm) <- foldM bind (M.empty, M.empty, M.empty, M.empty)
                        (zip (thParams th) (inArgs inst))
  pure (Arrow (substParamsS tm sm rm cm i) (substParamsS tm sm rm cm o) e)
  where
    bind (tm, sm, rm, cm) (PWire tv, IAStack (SCons t SEnd)) =
      Right (M.insert tv t tm, sm, rm, cm)
    bind (tm, sm, rm, cm) (PRow rv, IAStack (SCons (TSum row) SEnd)) =
      Right (tm, sm, M.insert rv row rm, cm)
    bind (tm, sm, rm, cm) (PStack sv, IAStack st) =
      Right (tm, M.insert sv st sm, rm, cm)
    -- the ML-functor move: `k` becomes the model's constructor NAME,
    -- and every `k(a, b)` in the slot is already a TData under that name
    bind (tm, sm, rm, cm) (PCon n _, IACon c) =
      Right (tm, sm, rm, M.insert n c cm)
    bind _ (q, a) =
      Left $ "model " ++ inName inst ++ ": parameter '" ++ pName q
          ++ "' is " ++ pKind q ++ ", given " ++ showArg a
    showArg (IAStack st) = show st
    showArg (IACon c)    = "the constructor " ++ c

-- A theory declaration IS a signature, so every slot can be
-- FORWARD-DECLARED at its declared type.  That is what lets a slot body
-- call the module's own defs (a model of any substance does) while a
-- def calls the slot — without it the two are ordered against each other
-- and one direction is always impossible.
declaredSlots :: [Theory] -> Instance -> Either String [(String, Scheme)]
declaredSlots theories inst = do
  th <- theoryOf theories (inTheory inst)
  sequence [ (,) (slotDefName (inName inst) nm) . generalize M.empty
               <$> slotArrowAt inst th declared
           | (nm, declared) <- thSlots th ]

-- substitute theory parameters through a stack: wires and stacks by the
-- ordinary parameter substitution, constructor parameters by renaming
-- the data name.  The rename runs FIRST, so it cannot reach inside a
-- type the model supplied.
substParamsS :: Map TVar Ty -> Map SVar SType -> Map RVar SumRow
             -> Map String String -> SType -> SType
substParamsS tm sm rm cm = go . substConNamesS cm
  where
    go SEnd          = SEnd
    go t@(STail v)   = M.findWithDefault t v sm
    go (SCons t r)   = SCons (substParams tm sm rm M.empty t) (go r)
    go (SExp b e r)  = sexp (go b) e (go r)

-- rename data-type NAMES through a stack.  Only theories use it: a
-- constructor parameter is a name, applied by substitution, so nothing
-- downstream of this ever sees a constructor variable.
substConNamesS :: Map String String -> SType -> SType
substConNamesS cm
  | M.null cm = id
  | otherwise = goS
  where
    goT (TFn (Arrow i o e)) = TFn (Arrow (goS i) (goS o) e)
    goT (TSum r)     = TSum (goR r)
    goT (TData n as) = TData (M.findWithDefault n n cm) (map goS as)
    goT t            = t
    goR RNil         = RNil
    goR t@(RTail _)  = t
    goR (RCons st r) = RCons (goS st) (goR r)
    goS SEnd         = SEnd
    goS t@(STail _)  = t
    goS (SCons t r)  = SCons (goT t) (goS r)
    goS (SExp b e r) = SExp (goS b) e (goS r)

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
freeVarsScheme (Forall tv sv rv nv ev subs arr) =
  let (ft, fs, fr, fn, fe) = freeVarsArrow arr
      se = nub [ v | (p, c) <- subs, Just v <- [eTail p, eTail c] ]
  in (ft \\ tv, fs \\ sv, fr \\ rv, fn \\ nv, nub (fe ++ se) \\ ev)

freeVarsEnv :: Env -> Vars
freeVarsEnv env =
  foldr (catVars . freeVarsScheme) noVars (M.elems env)

-- Generalize all free type, stack, row, and exponent variables not
-- fixed by the environment.  For an arrow with no surviving ⊆
-- constraints (a written type, a slot signature).
generalize :: Env -> Arrow -> Scheme
generalize env = generalizeWith env []

-- …and with them.  The constraints are CLOSED under transitivity first
-- (an inner composite is a part of the outer one, so a parameter's row
-- reaches the def's own row through a chain of intermediate rows that
-- the arrow never mentions), then garbage-collected: a constraint
-- naming a variable the arrow does not mention is discharged by its
-- LEAST solution — the part's least value is ∅, which every composite
-- contains, and an unmentioned composite is free to be as large as it
-- likes.  That is the standard effect-constraint GC, and it is what
-- keeps a scheme's constraint set the size of its parameter list
-- rather than the size of its body.
generalizeWith :: Env -> [EffSub] -> Arrow -> Scheme
generalizeWith env subs arr =
  let (ftv, fsv, frv, fnv, fev) = freeVarsArrow arr
      (etv, esv, erv, env', eev) = freeVarsEnv env
      -- existentials are CONSTANTS, not variables: never quantified
  in Forall (filter (not . isRigidT) (ftv \\ etv))
            (filter (not . isRigidS) (fsv \\ esv))
            (filter (not . isRigidR) (frv \\ erv))
            (filter (not . isRigidN) (fnv \\ env'))
            (fev \\ eev) (keepSubs subs fev) arr

-- Close over transitivity and garbage-collect in ONE walk.  For each
-- effect variable the ARROW mentions, follow the `⊆` edges out of it
-- and stop at the first row the arrow also mentions (or at a closed
-- row): the rows in between are the composites of a def's inner
-- stages, which the arrow never shows and whose least solution — as
-- large as they like — discharges them.  What comes back is the
-- scheme's constraint set: one edge per (parameter row, reachable
-- composite) pair, which for a real word is the size of its parameter
-- list.
--
-- Linear in the constraint set per source variable, and the sources
-- are the arrow's own tails: the naive "close then filter" is
-- quadratic per round and cost the whole suite an order of magnitude.
keepSubs :: [EffSub] -> [EVar] -> [EffSub]
keepSubs subs fev =
  dedup [ (Eff S.empty (Just v), c) | v <- fev, c <- walk v ]
  where
    dedup = S.toList . S.fromList
    inArrow = S.fromList fev
    edges = M.fromListWith (++) [ (t, [c]) | (p, c) <- subs, Just t <- [eTail p] ]
    walk v = go (S.singleton v) [(S.empty, v)] []
      where
        go _ [] acc = acc
        go seen ((ls, t) : rest) acc =
          let step (sn, q, a) (Eff lc mc) =
                let ls' = ls `S.union` lc
                in case mc of
                     Nothing -> (sn, q, Eff ls' Nothing : a)
                     Just w
                       | w == v               -> (sn, q, a)
                       | w `S.member` inArrow -> (sn, q, Eff ls' (Just w) : a)
                       | w `S.member` sn      -> (sn, q, a)
                       | otherwise -> (S.insert w sn, q ++ [(ls', w)], a)
              (seen', rest', acc') =
                foldl step (seen, rest, acc) (M.findWithDefault [] t edges)
          in go seen' rest' acc'

-- The ⊆ constraints that SURVIVE a solve: a part whose tail is still a
-- variable, and which the composite does not already contain.
residualSubs :: Subst -> [Constraint] -> [EffSub]
residualSubs s cs =
  S.toList (S.fromList
    [ (p, c)
    | (_, CSubEff p0 c0) <- map unAt cs
    , let p = apply s p0
    , let c = apply s c0
    , Just v <- [eTail p]
    , eTail c /= Just v ])

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
  , modFamilies  :: [Instance]         -- models PARAMETERIZED by a model:
                                       -- families, not models, so they are
                                       -- kept apart from the members
                                       -- `with F(M)` minted out of them
  , modFunctors  :: [(String, String)]  -- `functor Name = word`
  , modTemplates :: TemplateTable       -- defs over a theory, awaiting one
  , modTrans     :: [Transport]         -- models with a carrier
  , modKWords    :: [(String, String)]  -- def -> the category it is a word of
  , modBases     :: [BaseInstance]      -- `model Name in Base`
  , modTransformations :: [TransformationInfo]  -- `transformation Name`,
                                                -- with its verdicts
  , modRouted   :: [(String, String)]   -- defs INFERRED routing routed
                                        -- (stage 7b), and why: the
                                        -- resource and the atom that
                                        -- originated it, for `:t!`
  }

--------------------------------------------------------------------------------
-- BENEATH THE KEYWORDS: the declaration words (stage 8, 2026-09-17)
--
-- Direction 3 (design-macros.md, 2026-08-29): a fixed, name-first
-- surface over an OPEN TABLE of declaration words, each carrying a
-- `=Dict>` manifest.  The keyword-initial surface is kept deliberately
-- — it marks "an act on the dictionary" against "a morphism" — and
-- parsing words are ruled out permanently, because a reader macro
-- breaks uniform reading and the hygiene-by-representation story.
--
-- So a keyword LINE is parsed, whole, into a CALL of an ordinary word:
--
--     def f = body                 ≡   [body] "f" defW
--     type Pair = Int Int          ≡   ⌜Int Int⌝ "Pair" typeW
--     import "util.braid"          ≡   "util.braid" importW
--
-- and the pipeline runs the calls, in file order, against the `Dict`.
-- The surface does not change by one character; what changes is that
-- there is now one table saying what a keyword IS, and a library may
-- add a row to it.
--
-- WHAT SHAPES AN ARGUMENT MAY TAKE.  Three, and the list is closed:
--
--   Code     an already-parsed program — a quotation, what `[body]` is
--   Str      a name, a header, a path — text the word reads, never parses
--   TypeRep  an already-parsed type — what `typeOfWord` answers with
--
-- All three are POST-PARSE.  A keyword word never receives text to
-- parse, which is exactly the line direction 3 draws: post-parse Code
-- functors only, parsing words never.  A word that wanted a fourth
-- shape would be asking for a reader macro under another name.
--
-- HOW A LINE IS PARSED INTO THEM.  Every declaration line has the form
-- `KEYWORD <head> = <body>`, with `<body>` running to the end of the
-- line or into the indented block beneath it.  The head is the Str; the
-- body is read at the word's declared shape; the arguments are pushed
-- in that order and the word is called postfix.  A keyword whose line
-- has no `=` (`import "f.braid"`) takes the head alone.
--------------------------------------------------------------------------------

-- The shape of an argument a declaration word takes.
data DeclArgShape = ShCode | ShStr | ShTy
  deriving (Eq, Show)

-- ...and an argument, carrying the source the parser read it from.
data DeclArg = DACode String | DAStr String | DATy String
  deriving (Eq, Show)

-- How a keyword line collects its body.
data DeclSpan
  = SpanLine    -- the line, and nothing under it (`type`, `import`, `table`)
  | SpanBlock   -- an indented block under the head (`theory`, `model`)
  | SpanDef     -- either, the way a `def` has both
  deriving (Eq, Show)

-- ONE ROW OF THE TABLE.  The keyword whose lines call this word, the
-- word's own name, how its line is collected, the shape of its body
-- argument (`Nothing`: the line takes no body), and its arrow — written
-- out, because the arrow is the manifest and a declaration word that
-- did not say `=Dict>` would be claiming to be a morphism.
data DeclWord = DeclWord
  { dwKeyword :: String
  , dwWord    :: String
  , dwSpan    :: DeclSpan
  , dwBody    :: Maybe DeclArgShape
  , dwIO      :: Bool            -- ...and whether it reads the world
  }

-- the shapes this word's arguments have, deepest first: the body (when
-- it has one) under the head, which is the order `[body] "head" defW`
-- pushes them in
dwShapes :: DeclWord -> [DeclArgShape]
dwShapes w = maybe [] (: []) (dwBody w) ++ [ShStr]

-- ...and the arrow it wears, which is the manifest.  Written from the
-- row rather than beside it, so a word cannot claim a grade it has not
-- got.
dwArrow :: DeclWord -> String
dwArrow w = unwords (map shapeTy (dwShapes w)) ++ " ="
              ++ unwords (dictLabel : [ ioLabel | dwIO w ]) ++ "> \8226"
  where
    shapeTy ShCode = "Code"
    shapeTy ShStr  = "Str"
    shapeTy ShTy   = "TypeRep"

-- THE TABLE.  Eleven rows \8212 one per keyword, and one word with no
-- keyword \8212 and it is open: `keyword` adds a row (stage 8, commit
-- 4).  `resource` left it on 2026-09-18: a resource is a MODEL of the
-- Doctrine, so `modelW` is the word its lines call.
declWordTable :: [DeclWord]
declWordTable =
  [ DeclWord "def"            "defW"            SpanDef   (Just ShCode) False
  , DeclWord "type"           "typeW"           SpanLine  (Just ShTy)   False
  , DeclWord "data"           "dataW"           SpanLine  (Just ShTy)   False
  , DeclWord "theory"         "theoryW"         SpanBlock (Just ShStr)  False
  , DeclWord "model"          "modelW"          SpanBlock (Just ShStr)  False
  , DeclWord "transformation" "transformationW" SpanLine  (Just ShStr)  False
  , DeclWord "functor"        "functorW"        SpanLine  (Just ShStr)  False
    -- THE TWO THAT READ THE WORLD, and they say so in the grade.  This
    -- is the one place IO happens before anything is checked: the
    -- loader resolves a path and reads a file, and `=Dict IO>` is the
    -- manifest of exactly that (design-macros.md, 2026-09-15 \8212 "a
    -- declaration word of type `Str =Dict IO> Code`").  Nine of the
    -- eleven are `=Dict>`, so which two touch the world is readable off
    -- the table rather than off the implementation.
  , DeclWord "import"         "importW"         SpanLine  Nothing       True
  , DeclWord "table"          "tableW"          SpanLine  (Just ShStr)  True
    -- THE ROW THAT OPENS THE TABLE.  `keyword test = testW` binds a
    -- keyword name to a declaration word, and from that line on `test
    -- \8230 = \8230` is a declaration.  It is itself a declaration line,
    -- so it is a row like the others.
  , DeclWord "keyword"        "keywordW"        SpanLine  (Just ShStr)  False
    -- ...and one word with NO keyword of its own until a module binds
    -- one, which is what makes the binding worth having.  `testW`
    -- registers a runnable check; it is the kernel's only because
    -- running one at module start is the kernel's, and a word a module
    -- WRITES (`def benchW = \8230 ; defW`, at `Code Str =Dict> \8226`)
    -- binds to a keyword exactly the same way.
  , DeclWord ""               "testW"           SpanDef   (Just ShCode) False
  ]

-- what a keyword a module BOUND collects and takes: a `def`'s own
-- shape, `<keyword> <name> = <body>`, with the body as Code.  One
-- shape, because a second would be a second surface.
boundWordRow :: String -> String -> DeclWord
boundWordRow kw w = case declWordNamed w of
  Just row -> row { dwKeyword = kw }
  Nothing  -> DeclWord kw w SpanDef (Just ShCode) False

-- the keywords the table claims, for the scanner
declKeywords :: [String]
declKeywords = filter (not . null) (map dwKeyword declWordTable)

declWordFor :: String -> Maybe DeclWord
declWordFor kw =
  listToMaybe [ w | not (null kw), w <- declWordTable, dwKeyword w == kw ]

-- ...and by the word's own name, for `:doc defW` and for a program
-- that calls one
declWordNamed :: String -> Maybe DeclWord
declWordNamed n = listToMaybe [ w | w <- declWordTable, dwWord w == n ]

-- The scheme a declaration word wears in the environment, read off the
-- table: `defW : Code Str =Dict> \8226`.  There is no second spelling
-- of it \8212 `dwArrow` renders this same thing for the eye.
declWordScheme :: DeclWord -> Scheme
declWordScheme w =
  Forall [] [] [] [] [] []
    (Arrow (foldr (SCons . shapeTy) SEnd (dwShapes w)) SEnd
           (Eff (S.fromList (dictLabel : [ ioLabel | dwIO w ])) Nothing))
  where
    shapeTy ShCode = codeTy
    shapeTy ShStr  = TStr
    shapeTy ShTy   = typeRepTy

-- THE CHANNEL A DECLARATION WORD WRITES ON.  `print` does not do IO in
-- `runBuiltin` either: it appends to the log the evaluator carries, and
-- the driver does the world's half.  The dictionary is the same
-- arrangement with a different host \8212 the word appends a record, and
-- the LOADER does the dictionary's half.  The marker is a NUL, which no
-- source string can carry, so a record is the checker's and not a
-- program's.
declLogMark :: Char
declLogMark = '\0'

declLog :: String -> [String] -> String
declLog word parts = [declLogMark] ++ intercalate [declLogMark] (word : parts)

-- ...and back.  `Nothing` is an ordinary log line, which is what a
-- declaration program's `print` leaves.
declLogParts :: String -> Maybe (String, [String])
declLogParts (c : rest)
  | c == declLogMark = case splitOnChar declLogMark rest of
      (w : ps) -> Just (w, ps)
      []       -> Nothing
declLogParts _ = Nothing

-- ONE CALL: which word, its arguments, and the text it was read from.
-- The raw line rides along because every refusal below re-reads it —
-- which is how `file:line` survives the change: the call carries the
-- line it was written on, and the message it raises is the message that
-- line raised before.
data DeclCall = DeclCall
  { dcWord  :: String
  , dcArgs  :: [DeclArg]     -- in the order the word takes them
  , dcRaw   :: String        -- the head line, verbatim
  , dcBlock :: [String]      -- its indented block, verbatim
  , dcDoc   :: Maybe String
  , dcLine  :: Int           -- the line the BODY starts on
  }

-- Split a declaration line at its own `=`: the head is the Str, the
-- rest is the body.  The FIRST `=`, which is the rule every keyword
-- already used — a head has none of its own, and a body's may be its
-- second (`model Ints in Ring(Int) = add = +` is a head and a body
-- whose text contains one).
declSplit :: String -> (String, Maybe String)
declSplit l = case break (== '=') l of
  (hd, '=' : body) -> (drop 1 (dropWhile (not . isSpace) hd), Just body)
  _                -> (drop 1 (dropWhile (not . isSpace) l), Nothing)

-- The arguments of one call, read off its line at the word's shapes.
declArgsOf :: DeclWord -> String -> String -> [DeclArg]
declArgsOf w hd body = case dwBody w of
  Nothing      -> [DAStr (trimS hd)]
  Just ShCode  -> [DACode body, DAStr (trimS hd)]
  Just ShTy    -> [DATy body,   DAStr (trimS hd)]
  Just ShStr   -> [DAStr body,  DAStr (trimS hd)]
  where trimS = trimSpace

-- RUN ONE DECLARATION WORD against the dictionary.  Each row does
-- exactly what its keyword's branch of the scanner did before there was
-- a table, which is what makes the change invisible: the buckets it
-- writes, the strings it puts in them and the order they end up in are
-- the same.
applyDecl :: DeclCall -> Dict -> Either String Dict
applyDecl c dk = case dcWord c of
  "importW"         -> Right dk { dkImports = dcRaw c : dkImports dk }
  "tableW"          -> Right dk { dkTables  = dcRaw c : dkTables dk }
  w | w == "modelW", isJust (doctrineCarrierName (dcRaw c)) ->
        -- `model R in Doctrine = Ty` is a RESOURCE: the same bucket
        -- `resource` wrote to until 2026-09-18, reached by a shape test
        -- on the body rather than by a keyword of its own.
        Right dk { dkTypes = (dcRaw c, dcDoc c) : dkTypes dk }
    | w `elem` ["typeW", "dataW"] ->
        Right dk { dkTypes = (dcRaw c, dcDoc c) : dkTypes dk }
    | w `elem` ["functorW", "transformationW"] ->
        Right dk { dkBlocks = (dcRaw c, [], dcDoc c) : dkBlocks dk }
    | w `elem` ["theoryW", "modelW"] ->
        Right dk { dkBlocks = (dcRaw c, dcBlock c, dcDoc c) : dkBlocks dk }
  -- THE OPEN HALF.  `keyword test = testW` names a declaration word,
  -- and the scanner reads the table it just changed.
  "keywordW" -> case dcArgs c of
    [DAStr body, DAStr kwRaw]
      | [kw] <- words kwRaw, [w] <- words body ->
          if kw `elem` declKeywords
            then Left $ "`keyword " ++ kw ++ "` is refused: " ++ kw
                     ++ " is already a keyword of the language, and a "
                     ++ "keyword names one declaration word.  Pick another "
                     ++ "name."
            else Right dk { dkKeywords = (kw, w) : dkKeywords dk }
    _ -> Left kwMalformed
  "defW" -> do
    (name, hdr) <- defHeadOf (dcRaw c)
    body <- case dcArgs c of
              (DACode b : _) -> Right b
              _              -> Left ("internal: defW without a body: "
                                        ++ dcRaw c)
    Right dk { dkDefs = (name, hdr, body, dcDoc c, dcLine c) : dkDefs dk }
  -- A WORD A KEYWORD WAS BOUND TO.  It cannot run here \8212 it may be
  -- a word this module writes \8212 so the line becomes a CALL, kept in
  -- file order and run with the module's declaration program.
  w -> case dcArgs c of
    [DACode body, DAStr nm] ->
      Right dk { dkCalls = (dcLine c, callSrc body nm w) : dkCalls dk }
    _ -> Left ("a keyword's line is `<keyword> <name> = <body>`: "
                 ++ trimSpace (dcRaw c))
  where
    kwMalformed = "Malformed keyword declaration (want `keyword <name> = "
                    ++ "<a declaration word>`): " ++ trimSpace (dcRaw c)
    -- `[body] "name" word`, as the program it is
    callSrc body nm w =
      "([" ++ body ++ "] ; getCode) " ++ show nm ++ " ; " ++ w

-- a `def` line's own head: the name and the clauses, re-read from the
-- line so that the refusal is the line's refusal
defHeadOf :: String -> Either String (String, DefHdr)
defHeadOf l =
  case break (== '=') l of
    (lhs, '=' : _) ->
      case words lhs of
        ("def" : name : hdrWs)
          | not (isIntLiteral name), not (isFloatLiteral name) -> do
              hdr <- parseDefHdr l (unwords hdrWs)
              Right (name, hdr)
        _ -> Left ("Malformed definition: " ++ l)
    _ -> Left ("Malformed definition (missing '='): " ++ l)


-- What the def fold carries: the environment, the runtime scope, the
-- names a def may shadow, the defs so far, the docs, the templates, the
-- K-words and the routing notes.  Named because the declaration program
-- threads the same thing (stage 8).
type DefFold = ( Env, RunDefs, [String], [(String, Scheme, Term)]
               , Map String String, TemplateTable
               , [(String, String)], [(String, String)] )

-- ONE GROUP OF A MODULE'S DECLARATION PROGRAM (stage 8, 2026-09-17).
--
-- The keyword lines are calls of the declaration words and the loader
-- runs them; this is the same thing written the other way round, by a
-- program, and it is the same words.  A top-level group is a
-- DECLARATION LINE when its GRADE SAYS SO \8212 when what it does
-- carries `Dict`.  Not when it happens to name `defW`: a loop that
-- declares three words names it inside a def, and the grade is the only
-- thing that knows.  That is what the manifest is for, and it is the
-- same mark the keyword-initial surface makes, read off the arrow
-- rather than off the first token.
--
-- A declaration line is inferred at `\8226 =Dict> \8226` \8212 it must
-- take nothing and leave nothing, or lifting it out of main would
-- change what main does \8212 and RUN, purely and fuel-bounded, exactly
-- as a `functor` is run.  Every `defW` it called comes back on the log
-- and becomes a def through the same `addDef` every written one goes
-- through, so a programmatic def is checked, routed, labelled and
-- refused exactly where a written one is.
--
-- `Nothing` means "this is not a declaration line", and the group goes
-- back to main untouched \8212 including a group that does not infer at
-- all, whose refusal is main's to report, at main's own location.
declProgramStep
  :: (DefFold -> (String, DefHdr, String, Maybe String) -> Either String DefFold)
  -> [DataDecl] -> [Alias] -> [Theory] -> SlotTable -> [(String, String)]
  -> [String] -> [Transport] -> [BaseInstance] -> [String] -> [String]
  -> (DefFold, [[(Int, String)]]) -> [(Int, String)]
  -> Either String (DefFold, [[(Int, String)]])
declProgramStep addD datas aliases theories slots funcs thNames trans bases
                tbls resNames (st, mains) grp =
  case decided of
    Nothing  -> Right (st, grp : mains)
    Just act -> (\st' -> (st', mains)) <$> act
  where
    (env, run, _, _, _, tmpls, kwords, _) = st
    lineNo = case grp of ((k, _) : _) -> k; [] -> 0
    txt    = intercalate "\n" (map snd grp)
    rctx   = RCtx env datas aliases theories
    ctx    = ElabCtx env run slots funcs tmpls thNames trans kwords bases []
                     False Nothing tbls resNames rctx
    -- the grade decides, and a group that does not even infer is main's
    decided = case parseProgramFrom (const lineNo) datas txt
                     >>= \(t0, _) -> elabHeaders ctx t0
                     >>= \t1 -> (,) t1 <$> inferTermInAt lineNo env t1 of
      Right (t1, Arrow i o eff) | S.member dictLabel (eLabels eff) ->
        Just (run1 t1 i o eff)
      _ -> Nothing
    run1 t1 i o eff = do
      case solve [CEqStack i SEnd, CEqStack o SEnd] of
        Right _ -> Right ()
        Left _  -> Left $ "a DECLARATION LINE is run at check time, above "
                       ++ "main, so it must take nothing and leave nothing "
                       ++ "(`\8226 =" ++ dictLabel ++ "> \8226`): "
                       ++ trimSpace txt
      if S.member ioLabel (eLabels eff)
        then Left $ "a DECLARATION LINE runs at check time, before main, "
                 ++ "so it may not touch the world: this one is `="
                 ++ dictLabel ++ " " ++ ioLabel ++ ">`.  Reading a file "
                 ++ "before anything is checked is the LOADER's, and "
                 ++ "`import` and `table` are its words (MANUAL \167 8): "
                 ++ trimSpace txt
        else Right ()
      (_, logs) <- runPureEval (evalTerm rctx run emptyVarEnv t1 [])
      foldM install st [ r | Just r <- map declLogParts logs ]
    install s ("testW", [nm, body]) =
      addD s ( testDefName nm, noHdr, body
             , Just ("a `test` registered by this module \8212 it runs at "
                      ++ "module start, beside the laws, and must answer "
                      ++ "`true`") )
    install s ("defW", [nm, body]) =
      addD s ( nm, noHdr, body
             , Just ("declared by this module's declaration program: "
                      ++ "`[\8230] \"" ++ nm ++ "\" defW`, line "
                      ++ show lineNo) )
    install _ (w, ps) =
      Left ("internal: declaration record " ++ w ++ " " ++ show ps)

-- Two streams of logical lines, merged by the line they start on.
mergeByLine :: [[(Int, String)]] -> [[(Int, String)]] -> [[(Int, String)]]
mergeByLine [] bs = bs
mergeByLine as [] = as
mergeByLine as@(a : as') bs@(b : bs')
  | lineOf a <= lineOf b = a : mergeByLine as' bs
  | otherwise            = b : mergeByLine as bs'
  where lineOf g = case g of ((k, _) : _) -> k; [] -> 0

-- A module's program lines, grouped into LOGICAL lines: a line plus
-- whatever it left open.  The declaration program is decided per
-- logical line, because half an atom is not a line.
logicalLines :: [(Int, String)] -> [[(Int, String)]]
logicalLines = go 0 []
  where
    go _ acc [] = [ reverse acc | not (null acc) ]
    go d acc (pr@(_, l) : ls)
      | d' <= 0 && not (lineContinues l) = reverse (pr : acc) : go 0 [] ls
      | otherwise                        = go d' (pr : acc) ls
      where d' = d + lineDepth l

-- THE DICTIONARY, as a carrier (stage 8, 2026-09-17).  What a module's
-- declarations amount to, in the order they were written: the record
-- every declaration word acts on, and the thing the `Dict` wire stands
-- for.  `splitDefsIx` reads the source into one of these and the
-- checker reads it back out; a declaration word is a function on it.
--
-- It is the DECLARATIONS, not the finished module (see `dictLabel`):
-- what is here is what was written, and what the checker makes of it
-- is the `Module` at the other end.
data Dict = Dict
  { dkDefs     :: [(String, DefHdr, String, Maybe String, Int)]
    -- ^ `def`: name, header clauses, body source, doc, first body line
  , dkTypes    :: [(String, Maybe String)]
    -- ^ `type` / `data` / `resource`: the line, and its doc
  , dkBlocks   :: [(String, [String], Maybe String)]
    -- ^ `theory` / `model` / `functor` / `transformation`: head, block, doc
  , dkImports  :: [String]        -- ^ `import` lines, raw for the loader
  , dkTables   :: [String]        -- ^ `table` lines, raw for the loader
  , dkProgram  :: [(Int, String)] -- ^ every line the declarations left
  , dkKeywords :: [(String, String)]
    -- ^ THE OPEN HALF (stage 8): keyword -> the declaration word it
    -- names, as `keyword test = testW` bound it.  A line whose first
    -- word is one of these is a declaration from there on.
  , dkCalls    :: [(Int, String)]
    -- ^ ...and the calls those lines make, as programs, to be run with
    -- the module's declaration program: `[body] "name" testW`.  They
    -- wait because a word a module WROTE cannot run until the module's
    -- defs are checked.
  }

emptyDict :: Dict
emptyDict = Dict [] [] [] [] [] [] [] []

-- Every name this dictionary declares, for the checks that are about
-- names and not about kinds.  A type line's name may carry parameters
-- (`data Box(a) = a`), so it is cut at the paren.
dictNames :: Dict -> [String]
dictNames dk =
  [ n | (n, _, _, _, _) <- dkDefs dk ]
    ++ [ headName l | (l, _) <- dkTypes dk ]
    ++ [ headName h | (h, _, _) <- dkBlocks dk ]
  where
    headName l = case drop 1 (words l) of
      (n : _) -> takeWhile (`notElem` "(:=") n
      []      -> ""

-- `Dict` is the dictionary's own wire, and a module may not declare
-- it: that is what makes discharge structural rather than a check.
dictReserved :: Dict -> Either String ()
dictReserved dk = do
  -- ...and the declaration words are the compiler's: a keyword line is
  -- parsed into a call of one, so a module that could shadow one could
  -- change what `def` means halfway down a file.
  case [ n | n <- dictNames dk, Just w <- [declWordNamed n] ] of
    (n : _) -> Left $ "`" ++ n ++ "` is a declaration word: the keyword `"
                   ++ maybe "?" dwKeyword (declWordNamed n)
                   ++ "` is parsed into a call of it (`" ++ n ++ " : "
                   ++ maybe "" dwArrow (declWordNamed n)
                   ++ "`), so a module may not take the name.  Rename it.  "
                   ++ "MANUAL \167 8."
    []      -> Right ()
  case [ n | n <- dictNames dk
           , n `elem` [dictLabel, "un" ++ dictLabel] ] of
   (n : _) -> Left $ "`" ++ n ++ "` is the dictionary's own wire and may "
                 ++ "not be declared: `Dict` is the carrier every "
                 ++ "declaration word acts on (`defW : Code Str =Dict> "
                 ++ "\8226`), it is threaded by the loader, and there is "
                 ++ "no `Dict` to seed one with and no `unDict` to open "
                 ++ "one with \8212 which is what keeps a program from "
                 ++ "discharging it.  Rename it.  MANUAL \167 8."
   []      -> Right ()

-- Split source into `def name = body` lines, `type \8230` declaration
-- lines, and the main program (all remaining lines, in order, joined
-- by newline-sequencing).  A `## text` line is a doc comment: it binds
-- to the next def or type line (consecutive doc lines join); doc text
-- preceding a plain program line is dropped.
-- Returns (defs, type/data/resource lines, BLOCK declarations, IMPORT
-- lines, TABLE lines, main).  A block declaration is `theory`/`model`:
-- a header line plus the indented lines under it, kept raw for the
-- declaration parser.  Import and table lines come back RAW so the
-- loader can act on exactly the lines it consumed (see `stripLines`
-- and `spliceTables`); every other keyword branch is checked before
-- the fall-through, so a line inside a block or a continuation is
-- never mistaken for one.
splitDefs :: String
          -> Either String ( [(String, DefHdr, String, Maybe String)]
                           , [(String, Maybe String)]
                           , [(String, [String], Maybe String)]
                           , [String]
                           , [String]
                           , String )
splitDefs src = do
  (defs, tys, decls, imps, tbls, progLines) <- splitDefsIx src
  pure ( [ (n, h, b, d) | (n, h, b, d, _) <- defs ]
       , tys, decls, imps, tbls, intercalate "\n" (map snd progLines) )

-- ...and the same split with the FILE LINES it came off: each def body
-- knows the line its first line sits on (a body is a run of consecutive
-- lines, so one number places all of it), and the main program — which
-- is every line the declarations did not take, so not a run at all —
-- comes back line by line (2026-09-15).  This is the only place that
-- knows both, which is why it is the only place that has to say so.
splitDefsIx :: String
            -> Either String ( [(String, DefHdr, String, Maybe String, Int)]
                             , [(String, Maybe String)]
                             , [(String, [String], Maybe String)]
                             , [String]
                             , [String]
                             , [(Int, String)] )
splitDefsIx src = do
  dk <- dictFromSource src
  pure ( dkDefs dk, dkTypes dk, dkBlocks dk
       , dkImports dk, dkTables dk, dkProgram dk )

-- THE SCANNER, AS A RUN OF DECLARATION WORDS (stage 8, 2026-09-17).
-- Every keyword line is read into a CALL of the word its keyword names
-- and the call is applied to the dictionary, in file order; every other
-- line is a line of the program.  The three collection rules — a line,
-- a line plus its indented block, and `def`'s either — are the table's
-- `dwSpan` and not a branch of the scanner, which is what makes the
-- table open: a row is a keyword, a word, a span, a body shape and an
-- arrow, and a library that adds one adds no code here.
--
-- `file:line` survives because nothing about locations moved: a call
-- carries the line its BODY starts on, exactly as the def bucket
-- carried it before, and every refusal is raised from the same place
-- against the same raw line.
dictFromSource :: String -> Either String Dict
dictFromSource src = finish <$> go emptyDict Nothing (zip [1 ..] (lines src))
  where
    finish dk = Dict (reverse (dkDefs dk))    (reverse (dkTypes dk))
                     (reverse (dkBlocks dk))  (reverse (dkImports dk))
                     (reverse (dkTables dk))  (reverse (dkProgram dk))
                     (reverse (dkKeywords dk)) (reverse (dkCalls dk))

    go dk _ [] = Right dk
    go dk doc ((lineNo, l) : rest)
      | Just d <- docLine l =
          go dk (Just (maybe d (\p -> p ++ " " ++ d) doc)) rest
      -- a LINE: `type`, `data`, `resource`, `transformation`, `functor`,
      -- `import`, `table`
      | Just w <- wordOf dk l, dwSpan w == SpanLine = do
          dk' <- applyDecl (call w lineNo l [] doc (inlineOf l)) dk
          go dk' Nothing rest
      -- `resource` was a keyword until 2026-09-18.  A resource IS the
      -- model of the Doctrine its declaration generated (stage 7b), so
      -- the keyword was a second spelling of a thing the language has
      -- one spelling for.
      | ("resource" : _) <- words l =
          Left $ "`resource` is gone since 2026-09-18: a resource IS the "
              ++ "model of the Doctrine its declaration generates (stage "
              ++ "7b) \8212 write `model "
              ++ (case words (takeWhile (/= '=') l) of
                    (_ : n : _) -> n
                    _           -> "<Name>")
              ++ " in " ++ doctrineName ++ " ="
              ++ drop 1 (dropWhile (/= '=') l)
              ++ "`.  `:doc "
              ++ (case words l of (_ : n : _) -> n; _ -> "<Name>")
              ++ "` prints the carrier, the theory and the model, exactly "
              ++ "as it did.  CONSTRUCTS.md, MANUAL \167\&8."
      -- `rules` was a keyword until 2026-09-13; it is a model now.
      | ("rules" : _) <- words l =
          Left $ "`rules` is gone: a rule set is a PARTIAL MODEL of the "
              ++ "ambient presentation, so it is written `model Name in "
              ++ "Base = p = q, …` (or one `p = q` per indented line).  "
              ++ "MANUAL §8."
      -- `morphism` was the keyword until 2026-09-14.
      | ("morphism" : _) <- words l =
          Left $ "`morphism` is spelled `transformation` since 2026-09-14: "
              ++ "a map between two models of a theory is a NATURAL "
              ++ "TRANSFORMATION between the functors they are — write `"
              ++ ("transformation " ++ unwords (drop 1 (words l)))
              ++ "`.  MANUAL §8."
      -- `instance` and `mode` were keywords until 2026-09-13.
      | ("instance" : _) <- words l =
          Left $ "`instance` is spelled `model` since 2026-09-13: write `"
              ++ ("model " ++ unwords (drop 1 (words l))) ++ "`.  MANUAL §8."
      | ("mode" : _) <- words l =
          Left $ "`mode` is gone: a model whose theory has a hom-object "
              ++ "`k(_, _)` transports when it is APPLIED, so the model IS "
              ++ "the declaration — write `with "
              ++ (case words l of (_ : _ : "=" : i : _) -> i; _ -> "<Model>")
              ++ "` where you wrote `mode "
              ++ (case words l of (_ : n : _) -> n; _ -> "<Mode>")
              ++ "`, and `in "
              ++ (case words l of (_ : _ : "=" : i : _) -> i; _ -> "<Model>")
              ++ "` to build one of its morphisms by hand.  MANUAL §8."
      -- a HEAD PLUS ITS BLOCK: `theory`, `model`.  `model Opt in Base =
      -- p = q, r = s` writes its bindings inline instead, and
      -- `spanBlock` returns nothing for that form, so one branch serves.
      | Just w <- wordOf dk l, dwSpan w == SpanBlock = do
          let (block, rest') = spanBlock 0 rest
              kw            = head (words l)
          if null block && all isSpace (declInline l)
               && isNothing (baseInstanceName l)
            then Left $ "Empty " ++ kw ++ " body: " ++ l
            else do
              let blk = map snd block
                  bodyTxt | null blk  = inlineOf l
                          | otherwise = intercalate "\n" blk
              dk' <- applyDecl (call w lineNo l blk doc bodyTxt) dk
              go dk' Nothing rest'
      -- EITHER, the way `def` has both
      | Just w <- wordOf dk l, dwSpan w == SpanDef = do
          (name, body) <- defOrKeywordLine w l
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
                  -- a block body starts on the line after the `def`
                  dk' <- applyDecl (call w (lineNo + 1) l [] doc
                                     (intercalate "\n" (map snd block))) dk
                  go dk' Nothing rest'
            else do
              -- inline body: it may leave a bracket open, in which case
              -- the following lines belong to it, not to the module
              let (cont, rest') = spanOpen l rest
              -- an inline body starts on the `def` line itself
              dk' <- applyDecl (call w lineNo l [] doc
                                 (intercalate "\n" (body : map snd cont))) dk
              go dk' Nothing rest'
      | otherwise = do
          -- a program line may leave a bracket open; the lines that
          -- close it are part of it, so `def`/`type`/`##` inside an open
          -- bracket is code, not a declaration
          let (cont, rest') = spanOpen l rest
          go dk { dkProgram = reverse ((lineNo, l) : cont) ++ dkProgram dk }
             Nothing rest'

    -- Which declaration word this line calls, if any: the language's
    -- own table first, then the keywords THIS MODULE has bound so far.
    -- "so far" is the whole of the openness: a `keyword` line changes
    -- what the lines below it mean and nothing above it.
    wordOf dk l = case words l of
      (kw : _) -> case declWordFor kw of
        Just w  -> Just w
        Nothing -> boundWordRow kw <$> lookup kw (dkKeywords dk)
      [] -> Nothing

    -- a head line's own body text, when it has one on the line
    inlineOf l = maybe "" id (snd (declSplit l))

    -- `def`'s own head refuses a name that is a literal; a bound
    -- keyword's head is a name and nothing else
    defOrKeywordLine w l
      | dwWord w == "defW" = (\(n, _, b) -> (n, b)) <$> parseDefLine l
      | otherwise = case declSplit l of
          (hd, Just body) | [n] <- words hd -> Right (n, body)
          _ -> Left ("a keyword's line is `" ++ dwKeyword w
                       ++ " <name> = <body>`: " ++ trimSpace l)

    -- one call: the word, its arguments read at the word's shapes, and
    -- the text and the line the refusals will need
    call w bodyLine raw blk doc bodyTxt =
      DeclCall (dwWord w) (declArgsOf w (fst (declSplit raw)) bodyTxt)
               raw blk doc bodyLine

    -- what a declaration head writes after its own `=`: the INLINE body
    -- form, which every model has (a theory's slots are one per line)
    declInline = drop 1 . dropWhile (/= '=') . takeWhile (/= '#')

    indented ln = not (all isSpace ln) && isSpace (head ln)

    -- an indented block body, continuing across blank/dedented lines
    -- while a bracket opened inside it is still unclosed
    spanBlock d (p@(_, ln) : ls)
      | d > 0 || indented ln =
          let (b, r) = spanBlock (d + lineDepth ln) ls in (p : b, r)
    spanBlock _ ls = ([], ls)

    -- the lines AFTER `l` needed to close a bracket `l` left open — or
    -- to finish what `l` said it had not finished (`\`, `;`, `>>`)
    spanOpen l = walk (lineDepth l) (lineContinues l) []
      where
        walk d cont acc ls
          | d <= 0 && not cont = (reverse acc, ls)
        walk _ _ acc [] = (reverse acc, [])
        walk d _ acc (x : xs) =
          walk (d + lineDepth (snd x)) (lineContinues (snd x)) (x : acc) xs

    docLine l =
      case dropWhile isSpace l of
        '#' : '#' : txt -> Just (dropWhile isSpace txt)
        _               -> Nothing

    parseDefLine l =
      case break (== '=') l of
        (lhs, '=' : body) ->
          case words lhs of
            ("def" : name : hdrWs)
              | not (isIntLiteral name), not (isFloatLiteral name) -> do
                  hdr <- parseDefHdr l (unwords hdrWs)
                  Right (name, hdr, body)
            _ -> Left $ "Malformed definition: " ++ l
        _ -> Left $ "Malformed definition (missing '='): " ++ l

-- `Code = List(Stage)`, `Stage = List(Atom)` — the reified spine.
codeTy :: Ty
codeTy = TData "List"
           [SCons (TData "List" [SCons (TData "Atom" []) SEnd]) SEnd]

-- the two nominal types the reflection prims name; the prelude declares
-- both, exactly as it declares `Atom` for `codeTy` (2026-09-16)
typeRepTy :: Ty
typeRepTy = TData "TypeRep" []

declReprTy :: Ty
declReprTy = TData "Decl" []

--------------------------------------------------------------------------------
-- 10.3b Instances of `Base`: a declared, named, once-checked rewrite
--
-- `model Opt : Base = dupInt = dup, sumViaFold = sumN` is a PARTIAL
-- model of the ambient presentation.  `Base` is the reserved theory
-- whose generators are every word in scope, each with its own scheme as
-- the slot's declared type; a binding gives a generator its image, and
-- every generator not named maps to itself.  `with Opt` is then the
-- renaming `with Inst` already performs, and it mints `=Opt>` like any
-- other scope.  The declaration also generates a WORD `Opt : Code ⇒
-- Code` (the table, handed to the `rewrite` engine) so `[Opt]` and
-- `lift2 [Opt]` can apply the same reinterpretation at runtime.
--
-- There is no separate machinery, and no separate keyword: a rewriting
-- of the base IS a model, a by-generators functor whose action on a
-- generator is a rename.  The distinction worth keeping is semantic,
-- not syntactic — a model of `Base` whose images are PROVABLY EQUAL
-- to the generators (`sameCode`) is an optimizer; one whose images
-- merely satisfy the laws is a reinterpretation, a dialect.  Both are
-- models of `Base`.
--
-- Why a declaration and not a type.  `replace : Fn⟨a ⇒ b⟩ Fn⟨a ⇒ b⟩
-- Code ⇒ Code` types, but the shared variables are UNIFICATION — "p
-- and q have a common instance" — and that is symmetric, while "q may
-- stand wherever p stands" is not.  The property that IS sufficient is
-- `scheme(q) ≥ scheme(p)`, a rank-2 statement no rank-1 `Fn` can hold.
-- The routine that states it already exists: `subsumes`.  So the rule
-- is checked ONCE, where it is written, and is free at every use.
--
--   *Unification blesses a call; subsumption blesses a rule.*
--
-- v1 bindings are single WORDS on both sides, because Code carries
-- names and `Fn` values do not.  Multi-atom patterns wait for a use.
--------------------------------------------------------------------------------

-- Is this declaration head `model Nm in Base`?  `Base` is reserved, so
-- the test is exact and needs no theory table.
baseInstanceName :: String -> Maybe String
baseInstanceName header =
  case words (takeWhile (/= '=') (takeWhile (/= '#') header)) of
    ("model" : nm : "in" : t : _)
      | takeWhile (/= '(') t == baseTheoryName -> Just nm
    _ -> Nothing

-- The ambient presentation.  Reserved: a user may not declare it,
-- because its generators are not written down — they are every word in
-- scope, each with its own scheme as the slot's declared type.
baseTheoryName :: String
baseTheoryName = "Base"

-- `model Nm in Base = p = q, …` plus any indented `p = q` lines —
-- BOTH forms, exactly as every other model body has both.
parseBaseInstance :: [Alias] -> [(String, [TyParam])] -> [Theory] -> String
                  -> [String] -> Either String Instance
parseBaseInstance aliases dataSigs theories header body = do
  () <- maybe (Left $ "Malformed model head (want `model Name in Base "
                   ++ "= p = q, …`): " ++ dropWhile isSpace header)
              (const (Right ())) (baseInstanceName header)
  (nm, ps, _, _, om) <- parseModelHead aliases dataSigs theories header
  case ps of
    (_ : _) -> Left $ baseHere nm ++ "a model of `Base` takes no model "
                   ++ "PARAMETER: `Base`'s generators are every word in "
                   ++ "scope, so there is no theory for an argument to "
                   ++ "model"
    []      -> Right ()
  let inline = [ r | r <- splitTopCommas (drop 1 (dropWhile (/= '=')
                                                  (uncomment header)))
                   , not (all isSpace r) ]
      pieces = inline ++ [ r | r <- map uncomment body, not (all isSpace r) ]
  -- A RETRACTION MAKES THE EMPTY TABLE TOTAL (stage 7c): with `via c, r`
  -- every generator the table does not name is DERIVED by conjugation,
  -- so a model with no bindings at all is a complete one and says
  -- something.  Without a retraction there is nothing to derive from,
  -- and a table that names no generator reinterprets nothing.
  case (pieces, [ () | o <- om, isJust (omBack o) ]) of
    ([], []) -> Left $ baseHere nm ++ "no bindings: write `model " ++ nm
              ++ " in Base = p = q`, or one `p = q` per indented line (a "
              ++ "partial model names only the generators it "
              ++ "reinterprets — but it must name one)"
    _        -> Right ()
  -- THE TWO SHAPES OF AN IMAGE, and the reason there are two.  A model
  -- of `Base` with the identity object map also declares a `Code ⇒ Code`
  -- WORD (`[Opt]`, `lift2 [Opt]`), and Code carries names: so its
  -- bindings are one WORD to one word.  An object-mapped model declares
  -- no such word — its action on a literal is not a rename and its
  -- action on a def is an unfolding, neither of which a rewrite table
  -- can hold — so its images are ordinary PROGRAMS, inlined at each use
  -- and blessed once at the declaration.
  rs <- mapM (if null om then parseOneBinding nm else parseOneImage nm) pieces
  case [ p | (p, _) <- rs, length [ () | (p', _) <- rs, p' == p ] > 1 ] of
    (p : _) -> Left $ baseHere nm ++ "two bindings give `" ++ p
                   ++ "` an image, and a model sends each generator to "
                   ++ "one thing"
    []      -> Right ()
  pure (Instance nm baseTheoryName [] rs [] om [])
  where
    uncomment = takeWhile (/= '#')

-- An object-mapped model's image is a PROGRAM; only the generator on
-- the left has to be one word, because that is the name being sent.
parseOneImage :: String -> String -> Either String (String, String)
parseOneImage nm piece
  | (_, '=' : r) <- break (== '=') piece, secondBinding r =
      Left (baseHere nm ++ separatorErr "bindings")
parseOneImage nm piece =
  case break (== '=') piece of
    (l, '=' : r)
      | [p] <- words l, not (all isSpace r) -> Right (p, r)
      | [_] <- words l -> Left $ baseHere nm ++ "`" ++ trimSpace piece
                              ++ "` has no image: a binding reads `g = <program>`"
      | otherwise -> Left $ baseHere nm ++ "`" ++ trimSpace piece
                         ++ "` — a binding names ONE generator on the left "
                         ++ "(the image on the right is a program)"
    _ -> Left $ baseHere nm ++ "`" ++ trimSpace piece
             ++ "` is missing `=` (a binding reads `p = q`)"

-- The one-word table a model of `Base` with the identity object map
-- keeps: it is what the generated `Code ⇒ Code` word rewrites with, and
-- what `with Opt` renames through.
baseWordTable :: Instance -> [(String, String)]
baseWordTable i = [ (p, w) | (p, q) <- inBindings i, w <- take 1 (words q) ]

baseHere :: String -> String
baseHere nm = "model " ++ nm ++ " in Base: "

parseOneBinding :: String -> String -> Either String (String, String)
parseOneBinding nm piece
  | (_, '=' : r) <- break (== '=') piece, secondBinding r =
      Left (baseHere nm ++ separatorErr "bindings")
parseOneBinding nm piece =
  case break (== '=') piece of
    (l, '=' : r) ->
      case (words l, words r) of
        ([p], [q]) -> Right (p, q)
        _ -> Left $ baseHere nm ++ "`" ++ trimSpace piece
                 ++ "` — a v1 binding sends one WORD to one word "
                 ++ "(multi-atom patterns are not shipped)"
    _ -> Left $ baseHere nm ++ "`" ++ trimSpace piece
             ++ "` is missing `=` (a binding reads `p = q`)"

-- ONE RULE for every declaration body (2026-09-16): `;` COMPOSES, so it
-- never separates two bindings.  A comma separates them on one line, a
-- newline in a block.  The test is a second top-level `=`: a binding's
-- image is a program, and a program has no `=` in it, so a second one
-- at depth zero is two bindings run together.  Balanced brackets make
-- this exact — `mul = dup ; *` is ONE binding whose body composes.
secondBinding :: String -> Bool
secondBinding src = case tokenize src of
  Left _   -> False
  Right ts -> go (0 :: Int) ts
  where
    go _ [] = False
    go d (t : r)
      | t `elem` [TokLParen, TokLBrack, TokLAngle] = go (d + 1) r
      | t `elem` [TokRParen, TokRBrack, TokRAngle] = go (d - 1) r
      | d == 0, TokIdent "=" <- t                  = True
      | otherwise                                  = go d r

-- what to say when one is found
separatorErr :: String -> String
separatorErr what =
  "`;` composes; separate " ++ what ++ " with `,` or a newline"

trimSpace :: String -> String
trimSpace = dropWhile isSpace . reverse . dropWhile isSpace . reverse

splitOnChar :: Char -> String -> [String]
splitOnChar c str = case break (== c) str of
  (pre, _ : rest) -> pre : splitOnChar c rest
  (pre, [])       -> [pre]

-- `split`'s engine: n+1 pieces for n occurrences of the separator, so
-- the pieces and the separators rebuild the original exactly.  An empty
-- separator cuts nothing.
splitOnStr :: String -> String -> [String]
splitOnStr [] src = [src]
splitOnStr sep src = go "" src
  where
    go acc [] = [reverse acc]
    go acc r@(c : cs)
      | Just rest <- stripPrefix sep r = reverse acc : go "" rest
      | otherwise                      = go (c : acc) cs

-- The generated word: the table, then the engine.  A model of `Base`
-- is ordinary user code from here on, which is what lets `lift2 [Opt]`
-- apply it at RUNTIME with the program as its own fallback.
baseInstDefSrc :: [(String, String)] -> String
baseInstDefSrc rs =
  "(c -> (" ++ unwords [ '.' : p | (p, _) <- rs ] ++ " >> pack) ("
            ++ unwords [ '.' : q | (_, q) <- rs ] ++ " >> pack) c >> rewrite)"

-- The blessing, once, at the declaration.  `q` may stand wherever `p`
-- stands iff `scheme(q) ≥ arrow(p)`: instantiate p, skolemize it (which
-- `subsumes` does), and require q's scheme to cover it.  Grades ride
-- along by the semilattice order — a pure `q` under an io `p` passes
-- because ∅ is the bottom — so no separate effect rule is needed.
checkBaseInstance :: Env -> [DataDecl] -> TemplateTable -> [String]
                  -> [(String, [String])] -> Instance -> Either String ()
checkBaseInstance env datas tmpls thNames slotsOf inst = do
    mapM_ viaWord (inObjMap inst)
    mapM_ one (inBindings inst)
  where
    setNm = inName inst
    om0   = listToMaybe (inObjMap inst)
    -- THE IMAGE OF THE LITERAL FAMILY, and the retraction beside it.
    -- `c : A ⇒ B` is checked as a written expectation, like any image;
    -- `r : B ⇒ A` the other way.  They are checked HERE and not at a
    -- use, because there is no use — a literal has no name to refuse.
    viaWord om = do
      scC <- wordScheme (omVia om)
      let wantC = arrPure (one1 (omFrom om)) (one1 (omTo om))
      case subsumes scC wantC of
        Right () -> Right ()
        Left e -> Left $ here ++ "`via " ++ omVia om ++ "` is refused: "
              ++ omVia om ++ " is "
              ++ show (normalizeArrow (runInfer0 (instantiate scC)))
              ++ " but the image of the literal family at "
              ++ show (omFrom om) ++ " " ++ mapsTo ++ " " ++ show (omTo om)
              ++ " is " ++ show wantC ++ " (" ++ e ++ ")"
      case omBack om of
        Nothing -> Right ()
        Just r -> do
          scR <- wordScheme r
          let wantR = arrPure (one1 (omTo om)) (one1 (omFrom om))
          case subsumes scR wantR of
            Right () -> Right ()
            Left e -> Left $ here ++ "`via " ++ omVia om ++ ", " ++ r
                  ++ "` is refused: " ++ r ++ " is "
                  ++ show (normalizeArrow (runInfer0 (instantiate scR)))
                  ++ " but a RETRACTION of " ++ omVia om ++ " is "
                  ++ show wantR ++ " (" ++ e ++ ")"
    one1 t = SCons t SEnd

    -- ONE BLESSING, TWO SHAPES.  With the identity object map the image
    -- is a word and its own scheme is compared; with an object map the
    -- image is a program, inferred here, and the generator's arrow is
    -- compared AFTER the substitution — `+ : Int Int ⇒ Int` under
    -- `Int ↦ Mod7` is `Mod7 Mod7 ⇒ Mod7`, and nothing about the check
    -- changes but the arrow it is made against.
    one (p, q) = do
      scP <- wordScheme p
      let arrP0 = runInfer0 (instantiate scP)
          arrP  = maybe arrP0 (`objArrow` arrP0) om0
      (scQ, arrQ) <- imageScheme q
      case subsumes scQ arrP of
        Right () -> Right ()
        Left e   ->
          Left $ here ++ "`" ++ p ++ " = " ++ trimSpace q
              ++ "` is refused: " ++ p
              ++ " is used at " ++ show (normalizeArrow arrP) ++ " but "
              ++ trimSpace q ++ " is " ++ show (normalizeArrow arrQ)
              ++ " (" ++ e ++ ").  A binding may only GENERALIZE — the "
              ++ "image's scheme must be at least as general as the "
              ++ "generator's type, or a program that typed before the "
              ++ "reinterpretation would not type after it."

    -- the image, as something with a scheme: a WORD's own, or a
    -- program's, inferred once here and re-inferred at each use (which
    -- is what gives every use its own principal type, exactly as a
    -- template's expansion does)
    imageScheme q
      | Nothing <- om0, [w] <- words q = do
          sc <- wordScheme w
          Right (sc, runInfer0 (instantiate sc))
      | otherwise = do
          t <- imageTerm here datas q
          (arr, subs) <- inferTermInScope t
          Right (generalizeWith env subs arr, arr)

    inferTermInScope t = do
      (arr, subs) <- inferTermSubAt 0 env t
      Right (arr, subs)

    here = baseHere setNm
    wordScheme n
      | '@' `elem` n =
          Left $ here ++ "`" ++ n ++ "` is the compiler's spelling of a "
              ++ "slot: a slot is not a word outside `with`, so it can be "
              ++ "neither side of a binding"
      | n `elem` concatMap snd slotsOf =
          Left $ here ++ n ++ " is a slot of theory "
              ++ head ([ t | (t, ns) <- slotsOf, n `elem` ns ] ++ ["?"])
              ++ ", and a slot is not a word outside `with`: name the "
              ++ "model's word instead"
      | n `elem` thNames =
          Left $ here ++ n ++ " is a theory, not a word"
      | isJust (lookup n tmpls) =
          Left $ here ++ n ++ " is a template over theory "
              ++ maybe "?" fst (lookup n tmpls)
              ++ ", and a template has no type until a model "
              ++ "supplies one: a binding is checked once, so it needs a "
              ++ "word with a scheme"
      | otherwise =
          maybe (Left $ here ++ n ++ " is not defined at this point (a "
                     ++ "binding names two words, and both must already "
                     ++ "be in scope)")
                Right (M.lookup n env)

-- WHAT AN OBJECT-MAPPED MODEL SAYS ABOUT ITSELF (stage 7c).
--
-- The head, the table, and a VERDICT on each law the declaration
-- states.  Two laws can be stated here and neither has a theory behind
-- it, because `Base` has no samples: the retraction (`c ; r = id_A`)
-- and, for an image given to a word that HAS a body, `image =
-- F(body)`.  `sameCode` decides both where it reaches — a free-category
-- proof, for every input — and where it does not, the binding is
-- accepted and the model is recorded as a DIALECT.  That is the same
-- line `examples/optimizer.braid` §2 draws between an optimizer and a
-- reinterpretation, and the only honest one available: refusing would
-- rule out every image whose truth is arithmetic, which is all of them.
objModelDoc :: ElabCtx -> Instance -> Either String (String, String)
objModelDoc ctx inst = do
    laws <- mapM imageLaw (inBindings inst)
    pure (nm, headLine ++ retr ++ concat laws ++ coda)
  where
    om    = head (inObjMap inst)
    nm    = inName inst
    env   = ecEnv ctx
    run   = ecRun ctx
    datas = rcDatas (ecRefl ctx)
    arts  = concatMap (map fst . fst . dataDeclArtifacts) datas
    headLine = "model " ++ nm ++ " in Base(" ++ showObjMap om ++ ") — "
            ++ (case inBindings inst of
                  [] -> "no bindings: every generator is derived"
                  bs -> intercalate ", " [ p ++ " = " ++ trimSpace q
                                         | (p, q) <- bs ])
            ++ ".  "
    decides a b = case sameProgram env run run a b of
                    Right True -> True
                    _          -> False
    retr = case omBack om of
      Nothing -> "No retraction, so every generator that mentions "
              ++ show (omFrom om) ++ " needs an image of its own.  "
      Just r
        | decides (Seq 0 (Prim (omVia om)) (Prim r)) (Prim "id") ->
            "The retraction law `" ++ omVia om ++ " ; " ++ r
            ++ " = id` is PROVED (`sameCode`), so every generator the "
            ++ "table does not name is derived by conjugation.  "
        | otherwise ->
            "The retraction law `" ++ omVia om ++ " ; " ++ r
            ++ " = id` is UNCHECKED — `sameCode` does not decide it — "
            ++ "so " ++ nm ++ " is a DIALECT: the conjugated words are what "
            ++ "the declaration says they are, on the author’s word.  "
    imageLaw (g, q)
      | g `elem` arts = Right ""
      | otherwise = case M.lookup g run of
          Nothing -> Right ""     -- a prim: no body, so no law to state
          Just e  -> do
            img <- imageTerm (baseHere nm) datas q
            Right $ case objTransportT ctx inst (deBody e) of
              Right fb | decides img fb ->
                "The image of `" ++ g ++ "` is PROVED equal to F(its body) "
                ++ "(`sameCode`).  "
              _ ->
                "The image of `" ++ g ++ "` is a DIALECT: `sameCode` does "
                ++ "not decide `image = F(its body)`, so the binding stands "
                ++ "unchecked.  "
    coda = "An object-mapped model declares no `Code ⇒ Code` word: its "
        ++ "action on a literal is not a rename and its action on a def is "
        ++ "an unfolding, and a rewrite table holds neither."

-- An image PROGRAM, parsed.  It is base code: the vocabulary it is
-- written in is the one the model is reinterpreting, not the model's
-- own, so it applies nothing and declares nothing.
imageTerm :: String -> [DataDecl] -> String -> Either String Term
imageTerm here datas q = do
  (t, _) <- first (\e -> here ++ e) (parseProgramFrom (const 0) datas q)
  scan t
  pure t
  where
    scan (With _ ns _) = Left $ here ++ "`with " ++ unwords ns
                             ++ "` inside an image: an image is base code, "
                             ++ "written in the vocabulary the model "
                             ++ "reinterprets.  Name a def that carries the "
                             ++ "clause instead."
    scan (In ns _)     = Left $ here ++ "`in " ++ unwords ns
                             ++ "` inside an image: an image is a program, "
                             ++ "and only a def says what it is a morphism of"
    scan (Seq _ a b)   = scan a >> scan b
    scan (Tensor ts)   = mapM_ scan ts
    scan (Quote t)     = scan t
    scan (Alts cs _)   = mapM_ scan cs
    scan (OpenAbs _ _ b) = scan b
    scan _             = Right ()

-- `functor Name = <graph morphism>` — a declaration line, no block.
-- The right-hand side is a PROGRAM, because a graph morphism is
-- ordinarily built rather than named (`tick ... ; interpose`); what it
-- has to be is checked by `checkFunctorWord`, which is the type.
parseFunctorLine :: String -> Either String (String, String)
parseFunctorLine l =
  case break (== '=') (takeWhile (/= '#') l) of
    (lhs, '=' : rhs)
      | ["functor", nm] <- words lhs
      , not (all isSpace rhs) -> Right (nm, trimSpace rhs)
    _ -> Left $ "Malformed functor declaration (want `functor Name = "
             ++ "<a graph morphism, Fn\10216Stage \8658 Code\10217>`): "
             ++ dropWhile isSpace l

-- THE DOCTRINE.  `theory Doctrine(k(..., ...))` is declared in the
-- prelude, so every module sees it, and a theory that says `in
-- Doctrine` declares — in writing — that its `compose` and `embed` are
-- the doctrine's:
--
--   compose   k(ρ, σ) k(σ, τ) ⇒ k(ρ, τ)
--   embed     Fn⟨ρ ⇒ σ⟩ ⇒ k(ρ, σ)
--
-- The hom-object's arguments are STACKS.  That is the whole of stage
-- 7a: products in Braid are flat — the stack IS the product — so a
-- hom-object that named one WIRE per side was the one place they
-- nested, and it cost three things.  A pairing parameter `p` whose only
-- job was to name the packing; a `data Pair` declared once per file to
-- be that packing; and a routing pass that wrapped every wide stage in
-- `unP … ; stage ; P …` and whiskered it with `first`.  Over stacks,
-- a stage of any width embeds as itself and the base's own `...` IS
-- the strength, so all three are gone.
--
-- A model of such a theory transports (`with M`), at the LEVEL its
-- theory declared: composition alone composes carriers by hand,
-- + embedding transports ANY stage.  Two levels, where there were
-- three.  Exits (a carrier in, none out) and entries (nothing in, one
-- carrier out) are read off the remaining slots' declared arrows, as 5c
-- did.
--
-- Until 2026-09-13 this was DETECTED: three arrow shapes matched
-- against every slot, names never read.  Detection answered "does this
-- theory happen to look like a category"; the declaration answers "does
-- this theory claim to be one", which is the question, and it is the
-- same move `in` makes for a def.
doctrineName :: String
doctrineName = "Doctrine"

-- the two structure slots, in the order the level table reads them
doctrineCompose, doctrineEmbed :: String
doctrineCompose = "compose"
doctrineEmbed   = "embed"

-- and its one constructor parameter: the hom-object, whose two
-- arguments are STACKS (2026-09-16 — the pairing parameter `p` and the
-- strength `first` went with the packing they existed for)
doctrineK :: String
doctrineK = "k"

-- What a theory's `in D` clause CHECKED: for each of D's slots this
-- theory also declares, its arrow is D's arrow with D's constructor
-- parameters instantiated — consistently across every such slot.  The
-- map is from D's parameter names to the names this theory gave them
-- (its own parameter, or a data type it named outright).
type ConMap = Map String String

-- One-way match of a slot's declared arrow against the doctrine's.  The
-- pattern variables are the doctrine's slot-local wires (matched
-- against whatever the theory wrote, alpha) and its constructor
-- parameters (matched against a NAME, and the same name every time).
-- The effect is not compared: a grade is what a MODEL may do, and the
-- doctrine does not bound it — `Arrow`'s slots are `=Recursive>` because
-- circuits are built with `fix`, and that is the theory's business.
matchArrow :: [String] -> Arrow -> Arrow -> Maybe ConMap
matchArrow cons (Arrow i1 o1 _) (Arrow i2 o2 _) =
  matchStack cons (M.empty, M.empty, M.empty) i1 i2 >>= \st ->
    fst3 <$> matchStack cons st o1 o2
  where fst3 (cm, _, _) = cm

-- The match state: the constructor map, the alpha-renaming of the
-- pattern's WIRE variables, and — since the doctrine's hom-object
-- ranges over stacks (2026-09-16) — of its STACK variables.  Every
-- pattern variable is nonlinear (`k(a, b) k(b, c)`), so each must agree
-- with itself everywhere it appears.
type MatchSt = (ConMap, Map String Ty, Map String SType)

matchStack :: [String] -> MatchSt -> SType -> SType -> Maybe MatchSt
matchStack cons st0@(cm, tm, sm) s1 s2 = case (s1, s2) of
  -- a pattern TAIL swallows whatever is left, which is how `k(a, b)`
  -- with `a` a stack matches a theory's `k(ρ, σ)` at any width
  (STail (SV v), _) -> case M.lookup v sm of
    Just s' | s' /= s2 -> Nothing
    _                  -> Just (cm, tm, M.insert v s2 sm)
  (SEnd, SEnd)               -> Just st0
  (SCons t1 r1, SCons t2 r2) -> one st0 (t1, t2) >>= \st1 ->
                                  matchStack cons st1 r1 r2
  _ | s1 == s2 -> Just st0
    | otherwise -> Nothing
  where
    args acc as as'
      | length as /= length as' = Nothing
      | otherwise = foldM (\c (a, b) -> matchStack cons c a b) acc
                          (zip as as')
    one (c, tm', sm') (TVarTy (TV v), t) = case M.lookup v tm' of
      Just t' | t' /= t -> Nothing
      _                 -> Just (c, M.insert v t tm', sm')
    one st@(c, tm', sm') (TData n as, TData n' as')
      | n `elem` cons = case M.lookup n c of
          Just m | m /= n' -> Nothing
          _                -> args (M.insert n n' c, tm', sm') as as'
      | n == n'          = args st as as'
    one st (TFn (Arrow a b _), TFn (Arrow a' b' _)) = do
      st1 <- matchStack cons st a a'
      matchStack cons st1 b b'
    one st (t, t') | t == t' = Just st
    one _ _ = Nothing

-- `theory T(…) in D` — the claim, checked.  Every slot T declares
-- that D also declares must be D's slot at D's shape; the constructor
-- parameters D names are instantiated once for the whole theory.
checkExtends :: [Theory] -> Theory -> Either String ConMap
checkExtends theories th = case thIn th of
  Nothing -> Right M.empty
  Just d  -> do
    dt <- either (const (Left (here ++ "`in " ++ d ++ "` names no theory "
                            ++ "declared at this point")))
                 Right (theoryOf theories d)
    case thIn dt of
      Just d' -> Left $ here ++ "`in " ++ d ++ "` extends a theory that "
                     ++ "itself extends " ++ d' ++ ", and extension is one "
                     ++ "level deep: declare " ++ thName th ++ " over "
                     ++ d' ++ ", or flatten " ++ d ++ "."
      Nothing -> Right ()
    let cons   = [ n | PCon n _ <- thParams dt ]
        shared = [ (n, a, b) | (n, a) <- thSlots dt
                             , Just b <- [lookup n (thSlots th)] ]
    case shared of
      [] -> Left $ here ++ "`in " ++ d ++ "` declares nothing: " ++ d
                ++ " presents " ++ intercalate ", " (map fst (thSlots dt))
                ++ ", and this theory declares none of them.  A theory "
                ++ "extends another by declaring its operations, at its "
                ++ "signatures."
      _  -> Right ()
    foldM (one d cons) M.empty shared
  where
    here = "theory " ++ thName th ++ ": "
    one d cons cm (nm, declared, given) =
      case matchArrow cons declared given of
        Nothing -> Left $ here ++ "slot '" ++ nm ++ "' is "
                       ++ show (normalizeArrow given) ++ ", but " ++ d
                       ++ " declares it " ++ show (normalizeArrow declared)
                       ++ " — a theory that extends " ++ d ++ " declares "
                       ++ d ++ "'s operations at " ++ d ++ "'s signatures."
        Just cm' -> case [ (n, x, y) | (n, x) <- M.toList cm'
                                     , Just y <- [M.lookup n cm], y /= x ] of
          ((n, x, y) : _) ->
            Left $ here ++ "slot '" ++ nm ++ "' reads " ++ d
                ++ "'s parameter '" ++ n ++ "' as " ++ x
                ++ ", but another slot reads it as " ++ y
                ++ " — one theory instantiates it once."
          [] -> Right (M.union cm' cm)

-- A THEORY'S BASE SPELLINGS, audited where they are written (stage 9,
-- 2026-09-21) — once per theory, whether or not anything models it,
-- exactly as `in D` is.
--
-- The table carves a WIDE SUBCATEGORY out of the base and `embed` is
-- the functor out of it (`readTransport`), so what may carry a spelling
-- is a GENERATOR: a slot that builds a carrier out of nothing, or one
-- that whiskers a carrier.  A slot that takes something from the BASE
-- is one generator per VALUE and no one word spells it — which is where
-- the AFFINE TRAP is pinned, because `scale : Float ⇒ k(Float, Float)`
-- is exactly such a slot, and refusing it here is what keeps every
-- literal out of the table.
checkBaseSpellings :: Theory -> ConMap -> Either String ()
checkBaseSpellings th cm
  | null (thReads th) = Right ()
  | thIn th /= Just doctrineName = Left $ here
      ++ "a base spelling says which base atoms `" ++ doctrineEmbed
      ++ "` is defined on, so it needs a hom-object to embed INTO: "
      ++ "declare this theory `in " ++ doctrineName ++ "`, or drop the "
      ++ "spellings."
  | otherwise = do
      case (lookup doctrineEmbed (thSlots th), thReads th) of
        (Just _, ((n, _) : _)) -> Left $ here ++ "slot '" ++ n
          ++ "' declares a base spelling, and this theory also declares `"
          ++ doctrineEmbed ++ "`.  A base spelling says which base atoms "
          ++ "the embedding is DEFINED ON \8212 it carves out a subcategory "
          ++ "\8212 and `" ++ doctrineEmbed ++ "` says it is defined on all "
          ++ "of them.  Declare one or the other."
        _ -> Right ()
      case [ (n, ar) | (n, _) <- thReads th, Just ar <- [lookup n (thSlots th)]
                     , not (builds ar), not (whiskers ar) ] of
        ((n, ar) : _) -> Left $ here ++ "slot '" ++ n
          ++ "' declares a base spelling, and only a GENERATOR may \8212 one "
          ++ "that builds a carrier out of nothing (`\8226 \8658 k(\961, \963)`) or "
          ++ "whiskers one (`k(\961, \963) \8658 k(\964 \961, \964 \963)`).  `" ++ n
          ++ "` is " ++ show (normalizeArrow ar) ++ ", which takes "
          ++ "something from the base, so it is one generator per VALUE "
          ++ "and no one word spells it.  Drop the spelling: the "
          ++ "subcategory is generated by the atoms that ARE words."
        [] -> Right ()
      case [ n | (n, _) <- thReads th, isNothing (lookup n (thSlots th)) ] of
        (n : _) -> Left $ here ++ "'" ++ n ++ "' is not a slot of this "
                       ++ "theory"
        []      -> Right ()
  where
    here   = "theory " ++ thName th ++ ": "
    kParam = M.lookup doctrineK cm
    isCar (TData n [_, _]) = Just n == kParam
    isCar _                = False
    carriers st = length (filter isCar (fromMaybe [] (closedWires st)))
    builds   (Arrow i o _) = i == SEnd && carriers o == 1
    whiskers (Arrow i o _) = carriers i == 1 && carriers o == 1

-- the closed leading wires of a stack, and whether a tail rides above
-- them
stackPrefix :: SType -> Maybe (Int, Bool)
stackPrefix = go (0 :: Int)
  where
    go n SEnd        = Just (n, False)
    go n (STail _)   = Just (n, True)
    go n (SCons _ r) = go (n + 1) r
    go _ _           = Nothing

-- What `with M` and `in M` need from a model, checked once, here.
-- `Nothing` means "this model has no carrier": its theory has no
-- constructor parameter, so `with M` is the renaming it has always been
-- and `in M` is refused.
transportOf :: [DataDecl] -> [Theory] -> Instance
            -> Either String (Maybe Transport)
transportOf datas theories inst = do
  th <- either (const (Left ("Unknown theory: " ++ inTheory inst)))
               Right (theoryOf theories (inTheory inst))
  cm <- checkExtends theories th
  if thIn th == Just doctrineName
    then do
      kNm <- conArg th cm doctrineK
                    ("the hom-object `" ++ doctrineK ++ "(..., ...)`")
      Just <$> build th (M.lookup doctrineK cm) kNm
    else Right Nothing
  where
    here = "model " ++ inName inst ++ ": "
    -- What this model gave the doctrine's constructor parameter: the
    -- theory said which of ITS names stands for it (`checkExtends`), and
    -- a name that is one of the theory's own parameters is then read at
    -- this model's argument.
    conArg th cm n what = case M.lookup n cm of
      Nothing
        | n == doctrineK -> Left $ here ++ "theory " ++ thName th
            ++ " is declared `in " ++ doctrineName ++ "` but no slot of "
            ++ "it names " ++ what ++ ": declare `" ++ doctrineCompose
            ++ "`, and the hom-object is the one it composes."
        | otherwise -> Right Nothing
      Just nm -> case [ ar | PCon p ar <- thParams th, p == nm ] of
        (ar : _)
          | ar /= [True, True] -> Left $ here ++ "theory " ++ thName th
              ++ "'s constructor parameter `" ++ nm ++ "` is " ++ nm ++ "("
              ++ intercalate ", " [ if k then "..." else "_" | k <- ar ]
              ++ "), and " ++ doctrineName ++ " declares " ++ what
          | otherwise ->
              case [ c | (PCon p _, IACon c) <- zip (thParams th) (inArgs inst)
                       , p == nm ] of
                (c : _) -> Right (Just c)
                []      -> Left $ here ++ "no argument for theory "
                             ++ thName th ++ "'s parameter `" ++ nm ++ "`"
        [] | n == doctrineK -> Left $ here ++ "theory " ++ thName th
               ++ " declares " ++ what ++ " as " ++ nm ++ ", which is not "
               ++ "one of its parameters: a category's hom-object is the "
               ++ "parameter a MODEL chooses (`theory " ++ thName th
               ++ "(" ++ nm ++ "(_, _)) over " ++ doctrineName ++ "`)."
           | otherwise -> Right (Just nm)    -- a data type named outright
    build th kParam kNm = do
      carrier <- maybe (Left (here ++ "internal: no carrier")) Right kNm
      -- a slot's DECLARED arrow still says `k(_, _)`: the theory's own
      -- name for the hom-object, not the model's argument for it
      let slots   = thSlots th
          has n   = if isJust (lookup n slots) then Just n else Nothing
          isCar (TData n [_, _]) = Just n == kParam
          isCar _                = False
          carriers st = length (filter isCar (fromMaybe [] (closedWires st)))
          spoken  = catMaybes [has doctrineCompose, has doctrineEmbed]
          -- an EXIT consumes a carrier and hands back base; an ENTRY is
          -- the mirror, building a carrier out of nothing.  Both are read
          -- off the DECLARED arrow, so a model cannot hide one.
          exits  = [ n | (n, Arrow i o _) <- slots, n `notElem` spoken
                       , carriers i >= 1, carriers o == 0 ]
          enters = [ n | (n, Arrow i o _) <- slots, n `notElem` spoken
                       , i == SEnd, carriers o == 1 ]
          -- THE READER, inverted (stage 9).  A base spelling names the
          -- generator, and what the transport does with it is read off
          -- the slot's DECLARED arrow exactly as everything else here
          -- is: an ENTRY builds a carrier out of nothing, anything else
          -- takes one and gives one back (a whiskering).  Slots that do
          -- neither are refused where the spelling is written, below.
          -- `• ⇒ k(ρ, σ)` READ AS A BASE ARROW is `ρ ⇒ σ`: what the
          -- atom that spells this generator must actually be.
          baseArr n = case lookup n slots of
            Just (Arrow SEnd (SCons (TData _ [x, y]) SEnd) _)
              | n `elem` enters -> Just (Arrow x y effPure)
            _                   -> Nothing
          reader = [ (w, n, baseArr n) | (n, w) <- thReads th ]
      -- A BASE SPELLING IS FOR A GENERATOR, and a generator either makes
      -- a carrier or whiskers one.  `scale : Float ⇒ k(Float, Float)` is
      -- neither — it takes a base wire, so it is one generator PER
      -- SCALAR and no single word names it — and refusing it here is
      -- where the affine trap is pinned: a Float literal never enters
      -- the table, so `x ; 1.0 ; fadd` cannot be read as linear, which
      -- it is not.
      pure (Transport (inName inst) (thName th) carrier
                      (has doctrineCompose) (has doctrineEmbed)
                      exits enters
                      (representableAt datas (inName inst) carrier)
                      reader)

-- WHEN A MODEL'S FIBRE IS REPRESENTABLE AT A RESOURCE WIRE (stage 7b).
--
-- `K_E(\931, \920) = C(E \8855 \931, E \8855 \920)` is Power & Robinson's state
-- construction, and it is representable: the hom-object is a genuine
-- object of the base, `Fn\10216E \961 \8658 E \963\10217`.  So fibre composition IS
-- base composition of representatives, `embed` IS the `_`-padding the
-- routing pass writes, and `with E` fuses to exactly what
-- `elabScope` emits.  This is the test, and it is deliberately narrow:
--
--   * the carrier's body is an `Fn` whose arrow is PURE (a carrier
--     with a grade of its own \8212 `examples/prob.braid`'s
--     `Fn\10216Rng a =Recursive> Rng b\10217` \8212 composes by the
--     written-meets-written rule and must not be fused away), and
--   * the threaded wire is the same declared `resource` on both
--     sides, and
--   * that resource is the MODEL'S OWN NAME.
--
-- The last clause is what keeps a hand-written resource-shaped model
-- out: `Sampler` threads `Rng`, and `Rng` is not `Sampler`, so
-- `prob.braid` keeps the unfused path it was written for.
representableAt :: [DataDecl] -> String -> String -> Maybe String
representableAt datas modelNm carrier =
  case [ d | d <- datas, dName d == carrier ] of
    (d : _)
      | TFn (Arrow i o g) <- dBody d
      , g == effPure
      , [e] <- leadingRes resNames i
      , [e] == leadingRes resNames o
      , e == modelNm
      -> Just e
    _ -> Nothing
  where resNames = [ dName r | r <- datas, dResource r ]

--------------------------------------------------------------------------------
-- What `model R in Doctrine = Ty` GENERATES (stage 7b, 2026-09-17)
--
-- Beside the roll and the unroll the `data` machinery already writes,
-- a resource IS a MODEL OF THE DOCTRINE, and writes: the carrier, the theory
-- it models, and the model itself.  Not a compiler secret \8212 an
-- ordinary model, in the compiler's namespace (`@`, unwritable in
-- source) and visible through `:doc R`, because sugar you cannot read
-- is a feature rather than a desugaring.
--
-- The theory declares `compose` and `embed` ONLY, and that is forced
-- rather than lazy.  `observe : k(Int, Int) \8658 Int` would have to RUN a
-- resource program, which needs a SEED, and seeds live at the install
-- site with no declared defaults \8212 a generated `observe` would be
-- `mempty`-conjuring by another name.  The happy consequence is that
-- no inherited law runs: `instanceDefs`' `inherited` filter keeps a
-- doctrine law only when every doctrine slot it names is one this
-- theory declares, and all five Doctrine laws name `observe` or
-- `sample`.  The category laws hold by construction (`embed` is
-- padding, `compose` is `;`).
--
-- The two images are, verbatim, the shapes `examples/prob.braid`
-- writes by hand for `Samp` (`sEmbed`, `sCompose`), which is the
-- verification that this is the resource shape and not a guess.
--------------------------------------------------------------------------------

-- THE FOLD (2026-09-18).  `resource R = Ty` is spelled
-- `model R in Doctrine = Ty`, and it always was one: since 7b the
-- declaration generates a carrier, a theory and a MODEL of the
-- Doctrine, and everything downstream already treated it as that.  The
-- head is told from every other `model` head by its BODY — a STACK,
-- with no `=` in it — which is the same content-directed rule the
-- object map uses.  A body of `p = q` lines is a table; a body with no
-- `=` is a carrier.
--
-- `in Doctrine` here names a SUB-PRESENTATION: `compose` and `embed`,
-- and not `observe`/`sample`, for 7b's reason.  A plain `model M in T`
-- is total over T's slots and this one is not, which is said out loud
-- in MANUAL w\&8.
doctrineCarrierName :: String -> Maybe String
doctrineCarrierName header =
  case break (== '=') (takeWhile (/= '#') header) of
    (lhs, '=' : body)
      | ["model", nm, "in", d] <- words lhs
      , d == doctrineName
      , '=' `notElem` body
      , not (all isSpace body) -> Just nm
    _ -> Nothing

-- The internal name of the shape `model R in Doctrine = Ty` declares.
-- The KEYWORD is gone; the NOUN is not, and this is the noun: a
-- resource is a wire the elaborator threads.
resourceKw :: String
resourceKw = "resource"

resCarrierName, resTheoryName, resEmbedName, resComposeName
  :: String -> String
resCarrierName r = r ++ "@k"
resTheoryName  r = r ++ "@t"
resEmbedName   r = r ++ "@arr"
resComposeName r = r ++ "@then"

-- every name `resource R` puts in the compiler's namespace
resGenNames :: String -> [String]
resGenNames r = [ resCarrierName r, resTheoryName r
                , resEmbedName r, resComposeName r ]

-- `data R@k(a..., b...) = Fn<R a => R b>`
resCarrierLine :: String -> String
resCarrierLine r =
  "data " ++ resCarrierName r ++ "(a..., b...) = Fn\10216"
    ++ r ++ " a \8658 " ++ r ++ " b\10217"

-- `theory R@t(k(..., ...)) in Doctrine = compose : \8230, embed : \8230`
resTheoryDecl :: String -> (String, [String])
resTheoryDecl r =
  ( "theory " ++ resTheoryName r ++ "(k(..., ...)) in " ++ doctrineName ++ " ="
  , [ "    " ++ doctrineCompose ++ " : k(a, b) k(b, c) \8658 k(a, c)"
    , "    " ++ doctrineEmbed ++ "   : Fn\10216a \8658 b\10217 \8658 k(a, b)" ] )

-- `model R in R@t(R@k) = compose = R@then, embed = R@arr`
resModelDecl :: String -> (String, [String])
resModelDecl r =
  ( "model " ++ r ++ " in " ++ resTheoryName r
      ++ "(" ++ resCarrierName r ++ ") ="
  , [ "    " ++ doctrineCompose ++ " = " ++ resComposeName r
    , "    " ++ doctrineEmbed ++ "   = " ++ resEmbedName r ] )

-- the two images, as defs.  `_ f ... >> _ ev` steps over the carrier,
-- runs the stage on everything above it and comes back \8212 which is
-- `routeStage`'s pure branch at k = 1, and `sEmbed`'s body with the
-- wrapper and the `ev` in place.
resModelDefs :: String -> [(String, DefHdr, String, Maybe String)]
resModelDefs r =
  [ ( resEmbedName r, noHdr
    , "(f -> [_ f ... >> _ ev] >> " ++ k ++ ")"
    , Just ("generated by `model " ++ r ++ " in " ++ doctrineName
             ++ "`: the Doctrine's `" ++ doctrineEmbed ++ "` at " ++ r
             ++ " \8212 a base stage with the " ++ r
             ++ " wire whiskered underneath") )
  , ( resComposeName r, noHdr
    , "(c e -> [c ... >> un" ++ k ++ " ... >> ev >> e ... >> un" ++ k
        ++ " ... >> ev] >> " ++ k ++ ")"
    , Just ("generated by `model " ++ r ++ " in " ++ doctrineName
             ++ "`: the Doctrine's `" ++ doctrineCompose ++ "` at " ++ r
             ++ " \8212 base composition of representatives") ) ]
  where k = resCarrierName r

-- ...and what `:doc Dict` shows.  `Dict` is a resource like any other
-- and is declared by nobody, so the thing to print is the shape it
-- WOULD have had and the two words it deliberately has not got.
dictResourceDoc :: [String]
dictResourceDoc =
  [ dictLabel ++ " \8212 the dictionary, a resource the LOADER threads"
  , "## a declaration is an act on it: `def f = body` is "
      ++ "`[body] \"f\" defW`, and"
  , "## every declaration word says so in its own arrow "
      ++ "(`defW : Code Str =" ++ dictLabel ++ "> \8226`)."
  , "## it holds the module's declarations so far \8212 defs, types, "
      ++ "theories, models,"
  , "## transformations, tables, imports, and the keyword table."
  , "## what is DECLARED is here; what the checker made of it is read "
      ++ "back with the"
  , "## reflection words (`declOf`, `typeOfWord`, `envOf`)."
  , "## there is no `" ++ dictLabel ++ "` and no `un" ++ dictLabel
      ++ "`: a handler is `seed ; \8230 ; unwrap` and both"
  , "## ends come from the `data` machinery a `model R in "
      ++ doctrineName ++ "` line drives, so a wire"
  , "## nobody declared cannot be discharged by anything a program can "
      ++ "write."
  , "## the loader discharges it, because the loader is the host."
  ]

-- what `:doc R` shows: the sugar, spelled out
resourceModelDoc :: String -> [String]
resourceModelDoc r =
  [ "## generated by `model " ++ r ++ " in " ++ doctrineName
      ++ "` (the state construction at this carrier):"
  , resCarrierLine r ]
  ++ (th : tb) ++ (mh : mb)
  where (th, tb) = resTheoryDecl r
        (mh, mb) = resModelDecl r

-- The transport as a WORD, of the model's own name: the same functor as
-- a value, so `[Circuits]` is a quote and `lift2 [Circuits]` applies it
-- at runtime.  It differs from the scope in exactly two ways, both
-- deliberate: it has no K-word table (every stage is embedded) and it
-- seeds with an identity carrier so that `stagewise` can be uniform.
-- `leftId` is the law that says the seed is free.  It embeds one stage
-- at a time at one wire, which is all a `Code => Code` word can promise
-- without the widths the scope reads.
transportDefSrc :: Transport -> String -> String -> String
transportDefSrc _ arrW thenW =
  "(c -> (" ++ lit ("[_] >> " ++ arrW) ++ " >> parse >> " ++ orNil ++ ") "
        ++ "(c >> [(s -> " ++ lit "_ [" ++ " (s >> pack >> unparse) >> cat >> _ "
        ++ lit ("] >> _ " ++ arrW ++ " >> " ++ thenW)
        ++ " >> cat >> parse >> " ++ orNil ++ ")] ... >> stagewise)"
        ++ " >> append)"
  where
    lit t = "\"" ++ t ++ "\""
    orNil = "((q -> q) | drop >> nil) >> merge"

--------------------------------------------------------------------------------
-- 10.4 Imports: one file's declarations, in another file's scope
--
-- An import is a morphism of presentations — the INCLUSION.  Objects are
-- added, never merged (a name clash is an error, exactly as a duplicate
-- def is), and the composite presentation is checked as one module,
-- which is why a `type`, a `resource`, a `theory`, an `model` and a
-- `functor` all cross a file boundary with no machinery of their own.
--
-- Mechanically it is textual: the imported file's DECLARATIONS are
-- placed above the importing file's source, so the ordering rule (a
-- functor is runnable before its first `with`) extends across files
-- unchanged.  An imported file's main program is not included and does
-- not run — a library's demo is its own business — though it is still
-- typechecked when that file is checked, since a file must be a module
-- before it can be a dependency.
--
-- This is the LOADER's IO, at the same boundary that reads the main
-- file.  Elaboration still sees only parsed declarations and stays
-- pure: invariant two is untouched.
--------------------------------------------------------------------------------

isDocLine :: String -> Bool
isDocLine l = case dropWhile isSpace l of
  '#' : '#' : _ -> True
  _             -> False

-- The argument of a declaration that names a FILE: a quoted path, then
-- nothing but a comment.  `import` and `table` both take one, so it is
-- written once; the caller wraps the `why` in its own message.
quotedArg :: String -> Either String FilePath
quotedArg s =
  case dropWhile isSpace s of
    '"' : rest ->
      case break (== '"') rest of
        (path, '"' : after)
          | all isSpace (takeWhile (/= '#') after) ->
              if null path then Left "the path is empty" else Right path
          | otherwise -> Left "there is text after the path"
        _ -> Left "the path is not closed"
    _ -> Left "the path must be a quoted string"

-- `import "path.braid"` — the one declaration the loader handles.
parseImportLine :: String -> Either String FilePath
parseImportLine l =
  first bad (quotedArg (drop 6 (dropWhile isSpace l)))
  where
    bad why = "Malformed import (want `import \"path.braid\"`): "
           ++ trimLine l ++ " — " ++ why
    trimLine = dropWhile isSpace

-- Remove an in-order subsequence of lines, taking the doc-comment run
-- immediately above each removed line with it (a `##` above a main line
-- documents nothing, and must not drift onto the next declaration when
-- the file is included somewhere else).
stripLines :: [String] -> [String] -> [String]
stripLines ls rs = map snd (stripLinesIx (zip [1 ..] ls) rs)

-- ...on lines that remember where they came from, which is what the
-- loader keeps so that a refusal in an included file names THAT file
-- and THAT line (2026-09-15).
stripLinesIx :: [(Int, String)] -> [String] -> [(Int, String)]
stripLinesIx = go []
  where
    go acc ls [] = reverse acc ++ ls
    go acc [] _  = reverse acc
    go acc (p@(_, l) : ls) rs@(r : rs')
      | l == r    = go (dropWhile (isDocLine . snd) acc) ls rs'
      | otherwise = go (p : acc) ls rs

-- A module's declarations as source: everything but its main program
-- and its own import lines.  This is what an import includes.
moduleDecls :: String -> Either String String
moduleDecls = fmap (unlines . map snd) . moduleLinesIx False

-- The root file, with its import lines resolved away and its main
-- program kept.
moduleSansImports :: String -> Either String String
moduleSansImports = fmap (unlines . map snd) . moduleLinesIx True

-- What a file contributes to the assembled source, line by line, each
-- line paired with the number it has in ITS OWN file.  `True` keeps the
-- main program (the root), `False` drops it (an import).
moduleLinesIx :: Bool -> String -> Either String [(Int, String)]
moduleLinesIx keepMain src = do
  (_, _, _, imps, _, mainSrc) <- splitDefs src
  let sansImports = stripLinesIx (zip [1 ..] (lines src)) imps
  pure (if keepMain then sansImports
                    else stripLinesIx sansImports (lines mainSrc))

--------------------------------------------------------------------------------
-- 10.4b Tables: a CSV header is a PRESENTATION
--
-- `table Trades = "examples/data/trades.csv"` is a declaration line, and
-- the LOADER resolves it — at the same IO boundary `import` already
-- uses, and nowhere else.  The path resolves exactly as an import's
-- does, the WHOLE file is read at check time, and what comes back is
-- BRAID TEXT spliced in under the declaration, included exactly as an
-- imported file's declarations are:
--
--   data Trades = (sym: Str, px: Float, qty: Int)
--   headerTrades : • ⇒ List(Str)
--   loadTrades   : Str =IO Recursive> (List(Trades) | Str)
--
-- Nothing about the feature runs.  The generated text is the only thing
-- that does, and it is the same text `examples/frame.braid` wrote by
-- hand before 2026-09-15 — only the row reader and its arity vary with
-- the header.
--
-- The helpers are named `Trades@…`, the compiler's spelling, which
-- source may not write (the `'@' `elem` n` refusal in `elabHeaders`),
-- so a table's insides are reachable only through its two words.
--
-- COLUMN TYPES ARE READ FROM THE DATA: `Int` if every cell is an Int
-- literal, else `Float` if every cell is a Float or an Int literal,
-- else `Str`.  The whole file is read, so nothing is guessed about a
-- row that was not looked at; a blank cell is refused, naming line and
-- column, because a column has ONE type and a blank is not a value of
-- it.  The schema form `table Trades(sym: Str, price: Float, qty: Int)
-- = "…"` writes the names and the types instead, and every cell must
-- then read at the type that was written.
--------------------------------------------------------------------------------

-- A `table` declaration, as parsed off its line.
data TableDecl = TableDecl
  { tbName   :: String                     -- the row type, and the suffix
                                           -- of `load…` and `header…`
  , tbSchema :: Maybe [(String, String)]   -- the written names and types
  , tbPath   :: FilePath
  } deriving (Show, Eq)

-- The three types a column may have.  A table is scalars; a column of
-- anything else is a join, and a join is a program.
tableTypes :: [String]
tableTypes = ["Str", "Int", "Float"]

-- Is this string an ordinary word — a letter, then letters, digits and
-- `_`?  The words a table generates are plain identifiers, so that a
-- column name composes, quotes and reflects like any other word.
tableWord :: String -> Bool
tableWord w = not (null w) && isAlpha (head w)
           && all (\c -> isAlphaNum c || c == '_') w

-- THE SANITIZING RULE, stated once: each space, tab or `-` in a header
-- cell becomes `_`, and the first letter is lowercased.  Whatever that
-- leaves must be a word; a header that is not one after sanitizing is
-- an error naming the schema form, which writes the name by hand.
sanitizeHeader :: String -> String
sanitizeHeader h =
  case map sub (dropWhile isSpace (dropWhileEnd isSpace h)) of
    (c : cs) -> toLower c : cs
    []       -> []
  where
    sub c | isSpace c || c == '-' = '_'
          | otherwise             = c

-- `table Name = "path.csv"`, or `table Name(a: Str, b: Float) = "path.csv"`.
parseTableLine :: String -> Either String TableDecl
parseTableLine l =
  case stripPrefix "table" (dropWhile isSpace l) of
    Just r0 | null r0 || isSpace (head r0) -> do
      let (headTxt, eqRest) = break (== '=') (dropWhile isSpace r0)
      after <- case eqRest of
        '=' : p -> Right p
        _       -> Left (bad "there is no `=`")
      path       <- first bad (quotedArg after)
      (nm, cols) <- parseHead (dropWhileEnd isSpace headTxt)
      pure (TableDecl nm cols path)
    _ -> Left (bad "the line does not begin with `table`")
  where
    bad why = "Malformed table (want `table Name = \"path.csv\"`, or "
           ++ "`table Name(col: Type, …) = \"path.csv\"`): "
           ++ dropWhile isSpace l ++ " — " ++ why
    parseHead h = do
      let (nm, rest) = span (\c -> not (isSpace c) && c /= '(') h
      if null nm then Left (bad "the table has no name") else Right ()
      if isUpper (head nm) && all (\c -> isAlphaNum c || c == '_') nm
        then Right ()
        else Left (bad ("`" ++ nm ++ "` is not a type name: a table "
                     ++ "declares a row type, so its name begins with a "
                     ++ "capital letter"))
      case dropWhile isSpace rest of
        ""          -> Right (nm, Nothing)
        '(' : inner -> case break (== ')') inner of
          (b, ')' : tl)
            | all isSpace tl -> do
                cols <- mapM col (splitOnStr "," b)
                pure (nm, Just cols)
          _ -> Left (bad "the schema is not closed")
        _ -> Left (bad "there is text after the name")
    col c = case break (== ':') c of
      (f, ':' : t)
        | [fw] <- words f, [tw] <- words t ->
            if not (tableWord fw)
              then Left (bad ("`" ++ fw ++ "` is not a word: a column "
                           ++ "name is a letter, then letters, digits "
                           ++ "or `_`"))
            else if tw `elem` tableTypes
              then Right (fw, tw)
              else Left (bad ("a table column is Str, Int or Float, not "
                           ++ tw))
      _ -> Left (bad ("a schema column is `name: Type`, and this one is `"
                   ++ dropWhile isSpace c ++ "`"))

-- The Braid text a `table` line stands for.  `path` is the RESOLVED
-- path (the error messages name it, since that is the file that was
-- read); `body` is the whole file.
tableSource :: TableDecl -> FilePath -> String -> Either String String
tableSource tb path body = do
  (hdr, rows) <- case map (dropWhileEnd (== '\r')) (lines body) of
    []         -> Left (bad "the file is empty: a table's first line is \
                            \its header")
    (h : rest) -> Right (h, [ (i, ln) | (i, ln) <- zip [2 :: Int ..] rest
                            , not (blank ln) ])
  let hcells  = splitOnStr "," hdr
      width   = length hcells
      cells   = [ (i, splitOnStr "," ln) | (i, ln) <- rows ]
      columns = [ [ cs !! j | (_, cs) <- cells ] | j <- [0 .. width - 1] ]
  if null rows
    then Left (bad "the file has a header and no rows: a column's type \
                   \is read from the data, and there is none")
    else Right ()
  mapM_ (\(i, cs) ->
           if length cs == width then Right ()
           else Left (atLine i ("this row has " ++ plural (length cs) "cell"
                             ++ ", but the header has " ++ show width
                             ++ " — a table is rectangular"))) cells
  names <- case tbSchema tb of
    Just sc
      | length sc /= width ->
          Left (bad ("the schema writes " ++ plural (length sc) "column"
                  ++ " but the header has " ++ show width ++ ": "
                  ++ intercalate ", " hcells))
      | otherwise -> Right (map fst sc)
    Nothing -> mapM sanitized (zip [1 :: Int ..] hcells)
  case [ w | (w, k) <- zip names [0 :: Int ..], w `elem` take k names ] of
    (w : _) -> Left (bad ("two columns are named `" ++ w ++ "`: a column "
                       ++ "name is a WORD, and one word names one thing — "
                       ++ schemaFix))
    []      -> Right ()
  mapM_ (\(i, cs) ->
           case [ (j, nm) | (j, c, nm) <- zip3 [1 :: Int ..] cs names
                          , blank c ] of
             ((j, nm) : _) ->
               Left (atCell i j nm "the cell is blank.  v1 refuses a blank \
                                   \cell: a column has ONE type and a blank \
                                   \is not a value of it — fill the cell in, \
                                   \or delete the row")
             [] -> Right ()) cells
  tys <- case tbSchema tb of
    Nothing -> Right (map sniff columns)
    Just sc -> do
      let written = zip names (map snd sc)
      mapM_ (\(i, cs) ->
               case [ (j, nm, t, c)
                    | (j, c, (nm, t)) <- zip3 [1 :: Int ..] cs written
                    , not (readsAt t c) ] of
                 ((j, nm, t, c) : _) ->
                   Left (atCell i j nm (show c ++ " does not read as " ++ t
                                     ++ " — the schema writes `" ++ nm ++ ": "
                                     ++ t ++ "`, so write the type the column "
                                     ++ "has, or fix the cell"))
                 [] -> Right ()) cells
      Right (map snd sc)
  pure (tableText (tbName tb) (zip names tys) hcells)
  where
    blank = all isSpace
    plural k w = show k ++ " " ++ w ++ (if k == 1 then "" else "s")
    sniff cs
      | all isIntLiteral cs                               = "Int"
      | all (\c -> isFloatLiteral c || isIntLiteral c) cs = "Float"
      | otherwise                                         = "Str"
    readsAt "Int"   c = isIntLiteral c
    readsAt "Float" c = isFloatLiteral c || isIntLiteral c
    readsAt _       _ = True
    sanitized (j, h)
      | blank h = Left (bad ("column " ++ show j ++ " of the header is "
                          ++ "blank: a column's name is a word, so it must "
                          ++ "be written — " ++ schemaFix))
      | tableWord w = Right w
      | otherwise = Left (bad ("column " ++ show j ++ "'s header " ++ show h
                            ++ " is not a word after sanitizing (" ++ show w
                            ++ "): a space, a tab and a `-` become `_` and "
                            ++ "the first letter is lowercased, and what is "
                            ++ "left must be a letter followed by letters, "
                            ++ "digits or `_` — " ++ schemaFix))
      where w = sanitizeHeader h
    schemaFix = "name every column yourself with the schema form, `table "
             ++ tbName tb ++ "(col: Type, …) = \"" ++ tbPath tb ++ "\"`"
    bad why = "table " ++ tbName tb ++ " (" ++ path ++ "): " ++ why
    atLine i why = "table " ++ tbName tb ++ " (" ++ path ++ " line "
                ++ show i ++ "): " ++ why
    atCell i j nm why = "table " ++ tbName tb ++ " (" ++ path ++ " line "
                     ++ show i ++ ", column " ++ show j ++ " `" ++ nm
                     ++ "`): " ++ why

-- The text itself.  Every def but the two public words is named with
-- the compiler's `@`, so no source can reach it; `load…` is the ONE
-- generated word that names one of them, and `checkModuleWith` lets it
-- (see `tableGenNames`).
tableText :: String -> [(String, String)] -> [String] -> String
tableText nm cols hcells = unlines $
  [ "data " ++ nm ++ " = ("
      ++ intercalate ", " [ f ++ ": " ++ t | (f, t) <- cols ] ++ ")"
  , "## the CSV's header line, verbatim — runtime data, for a printer"
  , "def header" ++ nm ++ " = " ++ unwords (map show hcells) ++ " ; pack"
  , "def " ++ q "badRow" ++ " = (n -> \"bad row on line \" (n ; toStr) ; cat)"
  , "def " ++ q "cellAt" ++ " = (i cells -> i cells ; nth ; (pass | \"\") ; merge)"
  ]
  ++ [ "def " ++ q "float" ++ " = (s -> s ; asFloat? ; ((f -> f ; ok) | (t -> t ; asInt? ; ((i -> i ; toFloat ; ok) | (e -> e ; miss)) ; merge)) ; merge ; (pass | pass))"
     | "Float" `elem` map snd cols ]
  ++
  [ "def " ++ q "readRow" ++ " = (n " ++ unwords vars ++ " -> " ++ readBody ++ ")"
  , "def " ++ q "parseRow" ++ " = (n line -> (line \",\" ; split) ; (cells -> "
      ++ "(cells ; len) " ++ show width ++ " ; equals ["
      ++ unwords ("n" : [ "(" ++ show j ++ " cells ; " ++ q "cellAt" ++ ")"
                        | j <- [0 .. width - 1] ])
      ++ " ; " ++ q "readRow" ++ "] [n ; " ++ q "badRow" ++ " ; miss] ... ; cond))"
  , "def " ++ q "keepRow?" ++ " = (e -> e ; unBox ; (n line -> (line \"\" ; equals) ; not) ; (e | e))"
  , "def " ++ q "parseRows" ++ " = (src -> (src \"\\n\" ; split) ; (ls -> (ls ; len ; range ; [(i -> i 1 ; +)] ... ; map) ls ; zip) ; (numbered -> 1 numbered ; skip) ; ["
      ++ q "keepRow?" ++ "] ... ; filter ; [(e -> e ; unBox ; " ++ q "parseRow"
      ++ ")] ... ; map ; sequence ; (pass | pass))"
  , "## read " ++ nm ++ "'s CSV: the rows, or the first bad row's line"
  , "def load" ++ nm ++ " = (path -> path ; readFile ; ((body -> body ; "
      ++ q "parseRows" ++ ") | (e -> e ; miss)) ; merge ; (pass | pass))"
  ]
  where
    q s     = nm ++ "@" ++ s
    width   = length cols
    vars    = [ "c" ++ show j | j <- [0 .. width - 1] ]
    spec    = zip3 [0 :: Int ..] (map snd cols) vars
    valOf (j, t, v) = if t == "Str" then v else "v" ++ show j
    readBody = go spec
    go [] = unwords (map valOf spec) ++ " ; " ++ nm ++ " ; ok"
    go (s@(_, t, v) : rest)
      | t == "Str" = go rest
      | otherwise  =
          v ++ " ; " ++ reader t ++ " ; ((" ++ valOf s ++ " -> " ++ go rest
            ++ ") | (e -> n ; " ++ q "badRow" ++ " ; miss)) ; merge"
    reader "Int" = "asInt?"
    reader _     = q "float"

-- Splice each table's generated text in UNDER its declaration line, so
-- that the line stays where it was written and the text it stands for
-- reads as part of the file.  The blocks come in file order, exactly
-- the order `splitDefs` collected the lines in.
spliceTables :: [(String, String)] -> [(Int, String)] -> [(Int, String)]
spliceTables [] ls = ls
spliceTables _  [] = []
spliceTables bs@((raw, blk) : bs') (p@(k, l) : ls)
  -- generated text has no line of its own, so every line of it reports
  -- the DECLARATION it stands for (2026-09-15)
  | l == raw  = p : [ (k, g) | g <- lines blk ] ++ spliceTables bs' ls
  | otherwise = p : spliceTables bs ls

-- The public words a table generates.  `load…` is the only one whose
-- body names a `@` helper, so it is the only one the `@` refusal must
-- let through; source cannot claim the exemption, because a def of that
-- name would collide with the generated one.
tableGenNames :: TableDecl -> [String]
tableGenNames tb = ["load" ++ tbName tb, "header" ++ tbName tb]

-- Resolve a file's imports into one source text: depth-first, in file
-- order, each file included exactly once (a diamond includes it once,
-- which is what keeps the clash rule meaningful), a cycle reported by
-- the path that closes it.  Paths are relative to the importing file.
data Load = Load
  { lSeen :: [FilePath]           -- canonical paths already included
  , lDefs :: [(String, FilePath)] -- def names, and the file that declared them
  , lText :: String               -- the source assembled so far
  , lMap  :: LineMap              -- and where each of its lines came from
  }

emptyLoad :: Load
emptyLoad = Load [] [] "" []

-- Where the n-th line of an assembled source was written: the file, and
-- the line it has THERE.  Built by the loader, which is the only thing
-- that knows; read by `resolveLoc`, which is the only thing that needs
-- to (2026-09-15).
type LineMap = [(FilePath, Int)]

loadSource :: FilePath -> IO (Either String (String, LineMap))
loadSource = loadWith True

-- the same, as a DEPENDENCY: declarations only, main dropped.  This is
-- what an `import` line pulls in, and what the REPL's `:import` runs.
loadDecls :: FilePath -> IO (Either String (String, LineMap))
loadDecls = loadWith False

loadWith :: Bool -> FilePath -> IO (Either String (String, LineMap))
loadWith isRoot0 root =
  fmap (fmap (\a -> (lText a, lMap a))) (load [] emptyLoad root isRoot0)
  where
    -- `path` is already resolved: the root is what the user named, an
    -- import is what `resolve` found.  The root is never checked for
    -- existence — it may be /dev/stdin or another thing a program is
    -- entitled to be — so its read failure reports itself.
    load stack acc path isRoot = do
      canon <- canonicalizePath path
      if canon `elem` stack
        then pure (Left ("import cycle: "
                      ++ intercalate " → " (map takeFileName
                           (reverse (canon : stack)))))
        else if canon `elem` lSeen acc
          then pure (Right acc)
          else do
            r <- try (readFile path) :: IO (Either IOException String)
            case r of
              Left _ -> pure (Left ("cannot read " ++ path))
              Right src -> loaded stack acc path isRoot canon src

    loaded stack acc path isRoot canon src =
      case splitDefs src >>= \(defs, _, _, imps, tbls, _) ->
             (,,,) defs tbls <$> mapM parseImportLine imps
                             <*> mapM parseTableLine tbls of
        Left e -> pure (Left (inFile path e))
        Right (defs, tbls, rels, tables) -> do
          -- a TABLE is resolved here too: the same IO boundary, the
          -- same path rule, and the text it stands for is spliced in
          -- under its own declaration line
          blocks <- mapM (tableBlock (takeDirectory path)) tables
          kids <- mapM (resolve (takeDirectory path)) rels
          r <- foldM (child (canon : stack))
                     (Right acc { lSeen = canon : lSeen acc }) kids
          pure $ do
            acc' <- r
            -- objects are ADDED, never merged: the inclusion is
            -- injective on names or it is an error naming both files
            case [ (n, f) | (n, _, _, _) <- defs
                          , (m, f) <- lDefs acc', m == n ] of
              ((n, f) : _) ->
                Left $ inFile path ("`" ++ n ++ "` is already defined in "
                                 ++ f)
              [] -> Right ()
            blks <- first (inFile path) (sequence blocks)
            own  <- first (inFile path) (moduleLinesIx isRoot src)
            let spliced = spliceTables (zip tbls blks) own
                own'    = unlines (map snd spliced)
                genDefs = [ (n, path)
                          | tb <- tables, n <- tableGenNames tb ]
            pure acc' { lDefs = lDefs acc' ++ [ (n, path) | (n, _, _, _) <- defs ]
                                           ++ genDefs
                      , lMap  = lMap acc' ++ [ (path, k) | (k, _) <- spliced ]
                      , lText = lText acc' ++ own' }

    child _ acc@(Left _) _  = pure acc
    child _ (Right _) (Left e) = pure (Left e)
    child stack (Right acc) (Right p) = load stack acc p False

    -- A relative import is resolved against the importing FILE's
    -- directory, which is what lets a directory of modules move as one.
    -- Failing that, the current directory is tried, so a program read
    -- from a pipe (`braid -`, which has no directory of its own) can
    -- import too.  Found in neither: the error names both places.
    resolve dir rel = do
      found <- findRel dir rel
      pure $ case found of
        Just p  -> Right p
        Nothing -> Left ("import: no such file: " ++ rel ++ " (looked in "
                      ++ dir </> rel ++ " and in the current directory)")

    findRel dir rel
      | isAbsolute rel = pure (Just rel)
      | otherwise = do
          there <- doesFileExist (dir </> rel)
          if there then pure (Just (dir </> rel)) else do
            here <- doesFileExist rel
            pure (if here then Just rel else Nothing)

    -- A table's file is resolved by the SAME rule an import's is, read
    -- WHOLE (so nothing is guessed about a row that was not looked at),
    -- and turned into Braid text.  This is all the IO the feature has.
    tableBlock dir tb = do
      found <- findRel dir (tbPath tb)
      case found of
        Nothing -> pure (Left ("table " ++ tbName tb ++ ": no such file: "
                            ++ tbPath tb ++ " (looked in "
                            ++ dir </> tbPath tb
                            ++ " and in the current directory)"))
        Just p -> do
          r <- try (do { b <- readFile p; _ <- evaluate (length b); pure b })
                 :: IO (Either IOException String)
          pure $ case r of
            Left _  -> Left ("table " ++ tbName tb ++ ": cannot read " ++ p)
            Right b -> tableSource tb p b

    inFile path e = "in " ++ path ++ ": " ++ e

-- Which slots each of a module's models carries — the table `with`
-- consults to rename a model's operations.  A session builds it
-- from an imported module, since it cannot declare one itself.
moduleSlotTable :: Module -> Either String SlotTable
moduleSlotTable m =
  sequence [ (\th -> (inName i, (thName th, slotWords th)))
                 <$> theoryOf (modTheories m) (inTheory i)
           | i <- modInstances m ]

-- Every word `with M` renames: M's slots.  (Until 2026-09-16 it also
-- renamed the constructor words a pairing parameter gave a model; the
-- Doctrine has no pairing parameter now.)
slotWords :: Theory -> [String]
slotWords = map fst . thSlots

-- Check a module against the prelude: user defs and type aliases may
-- shadow prelude ones (once each); the prelude's defs, aliases, and
-- docs are folded into the result so the runtime and printer see them.
checkModule :: String -> Either String Module
checkModule = checkModuleAt []

checkModuleAt :: LineMap -> String -> Either String Module
checkModuleAt lm src = do
  -- the prelude's THEORIES ride in too: `Doctrine` is ambient, because
  -- `theory T(k(_, _)) over Doctrine` is a claim and a claim needs
  -- something to point at in every module.
  let base = (moduleBase (modEnv preludeModule)
                         (moduleRunDefs preludeModule) preludeShadowNames
                         (modAliases preludeModule)
                         (modDatas preludeModule))
               { mbTheories = modTheories preludeModule }
  m <- checkModuleWithAt lm base src
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
-- `run0` is the runtime scope the module is checked ON TOP OF.  It is
-- threaded through both folds so that, by the time a declaration is
-- reached, everything ABOVE it is not merely typed but RUNNABLE — which
-- is what lets a functor (a `Code ⇒ Code` word) be evaluated while the
-- module is still being checked.  Prefix visibility, deliberately: the
-- knotted mutual scope `buildRunDefs` gives the finished module does
-- not exist mid-fold, and "a functor is runnable before its first use"
-- is exactly the ordering rule (design-macros.md).
-- What a module is checked ON TOP of: the prelude, a REPL session's
-- accumulated definitions, or (for `with`) the models and functors an
-- imported file declared.  A file's own imports need none of this —
-- they are textual, so their declarations are simply part of the module
-- — but a session has no text to include into, so it carries the tables.
data ModuleBase = ModuleBase
  { mbEnv     :: Env
  , mbRun     :: RunDefs
  , mbShadow  :: [String]             -- names a def may redefine (once)
  , mbAliases :: [Alias]
  , mbDatas   :: [DataDecl]
  , mbSlots   :: SlotTable            -- model -> its theory and slots
  , mbFuncs   :: [(String, String)]   -- functor -> its word
  , mbTheories  :: [Theory]           -- theories a session `:import`ed
  , mbTemplates :: TemplateTable      -- templates it brought with them
  , mbFamilies  :: [Instance]         -- parameterized models it brought
  , mbGenerated :: [Instance]         -- ...and the members already minted
  , mbTrans     :: [Transport]        -- carrier models it brought
  , mbKWords    :: [(String, String)] -- and their K-words
  , mbBases     :: [BaseInstance]     -- and its models of `Base`
  }

moduleBase :: Env -> RunDefs -> [String] -> [Alias] -> [DataDecl] -> ModuleBase
moduleBase env run shadow aliases datas =
  ModuleBase env run shadow aliases datas [] [] [] [] [] [] [] [] []

checkModuleWith :: ModuleBase -> String -> Either String Module
checkModuleWith = checkModuleWithAt []

-- ...with the loader's line map, so that every refusal this raises is
-- printed as `file:line` rather than as the line of an assembled source
-- nobody wrote.  This is the ONE place a located refusal is turned back
-- into text; below it, a location travels inside the message.
checkModuleWithAt :: LineMap -> ModuleBase -> String -> Either String Module
checkModuleWithAt lm base src = first (locFor lm src) (checkModuleRaw base src)

checkModuleRaw :: ModuleBase -> String -> Either String Module
checkModuleRaw base src = do
  let env0     = mbEnv base
      run0     = mbRun base
      shadow0  = mbShadow base
      aliases0 = mbAliases base
      datas0   = mbDatas base
  dict <- dictFromSource src
  -- the dictionary's own wire is not a name a module may take
  dictReserved dict
  let defSrcs0   = dkDefs dict
      tyLines    = dkTypes dict
      declLines0 = dkBlocks dict
      importLines = dkImports dict
      tableLines = dkTables dict
      mainLines0 = dkProgram dict
  -- every generated def is the compiler's own text and reports the def,
  -- not a line (0); a written one reports the line its body starts on
  let defSrcs  = [ (n, h, b, d) | (n, h, b, d, _) <- defSrcs0 ]
      defLine  = \n -> maybe 0 id (lookup n [ (nm, k) | (nm, _, _, _, k) <- defSrcs0 ])
      -- the whole program, for the pass that reads `with F(M)` off the
      -- source: a family is minted before anything runs, so it must be
      -- read before the declaration program is told apart from main
      mainSrc0 = intercalate "\n" (map snd mainLines0)
  -- the loader resolves imports into the source it hands over, so one
  -- reaching here means there was no file to resolve it against
  case importLines of
    (l : _) -> Left $ "import: a module can only import when it is loaded "
                   ++ "from a file, and this one was checked without a file "
                   ++ "context: " ++ dropWhile isSpace l
    []      -> Right ()
  -- A `table` line STAYS where it was written and the text it stands
  -- for is spliced in under it, so reaching here with no generated
  -- loader means the loader never ran — there was no file to resolve
  -- the CSV against.
  tables <- mapM parseTableLine tableLines
  case [ tb | tb <- tables
            , ("load" ++ tbName tb) `notElem` [ n | (n, _, _, _) <- defSrcs ] ] of
    (tb : _) -> Left $ "table: a table can only be declared when the module "
                    ++ "is loaded from a file, and this one was checked "
                    ++ "without a file context: table " ++ tbName tb
    []       -> Right ()
  let tblTypes = map tbName tables
      -- `load…` is the one generated word whose body names a `@`
      -- helper; source cannot claim the exemption, because a def of
      -- that name would collide with the generated one
      tblGen   = concatMap tableGenNames tables
  (env1a, runTya, allAliasesA, allDatasA, ownAliasesA, ownDatasA, docs0a) <-
    foldM (addType tblTypes) (env0, run0, aliases0, datas0, [], [], M.empty) tyLines
  -- STAGE 7b: a `resource` declares a MODEL OF THE DOCTRINE, and the
  -- carrier is a `data` line the compiler writes \8212 exactly the way a
  -- `table` writes one.  It is appended AFTER the module's own types so
  -- that `data R@k = Fn<R a => R b>` can name `R`, and it goes through
  -- the same `addType` every written line does, so a name collision is
  -- the ordinary duplicate-declaration refusal.
  let ownRes = [ dName d | d <- ownDatasA, dResource d, null (dParams d) ]
  (env1, runTy, allAliases, allDatas, ownAliases, ownDatas, docs0) <-
    foldM (addType tblTypes)
          (env1a, runTya, allAliasesA, allDatasA, ownAliasesA, ownDatasA, docs0a)
          [ (resCarrierLine r, Nothing) | r <- ownRes ]
  -- ...and the theory it models and the model itself, in the same
  -- bucket a written `theory`/`model` block lands in
  let declLines = declLines0
                ++ concat [ [ (th, tb, Nothing), (mh, mb, Nothing) ]
                          | r <- ownRes
                          , let (th, tb) = resTheoryDecl r
                          , let (mh, mb) = resModelDecl r ]
  -- theory and model heads name types, and the type they name is
  -- routinely one of the prelude's (`Wrap(List(Int))`), so they are
  -- parsed against every alias and data type in scope — not just the
  -- module's own.
  let sigs = map dataSig allDatas
  -- theories first: a model is checked against its theory, so the
  -- theory must already be known.  Both run before any def, which is
  -- what gives them file-wide scope.
  ownTheories <- sequence [ parseTheory allAliases sigs h b
                          | (h, b, _) <- declLines, take 6 h == "theory" ]
  -- `Base` is the ambient presentation: its generators are every word in
  -- scope, which is not something a user can write down.
  case [ () | th <- ownTheories, thName th == baseTheoryName ] of
    (_ : _) -> Left $ "`" ++ baseTheoryName ++ "` is the ambient "
                   ++ "presentation and may not be declared: its "
                   ++ "generators are every word in scope, each with its "
                   ++ "own scheme.  `model X in " ++ baseTheoryName
                   ++ "` is how it is modelled."
    []      -> Right ()
  -- a session cannot declare a theory, but `:import` carries one in, and
  -- a model or a template checked here may name it
  let theories = ownTheories ++ mbTheories base
      thNames  = map thName theories
  -- `in D` in a theory head is a CLAIM, and it is checked here, once,
  -- whether or not anything models the theory
  mapM_ (\th -> checkExtends theories th >>= checkBaseSpellings th) ownTheories
  declared <- sequence [ parseInstance allAliases sigs theories h b
                       | (h, b, _) <- declLines, take 5 h == "model"
                       , isNothing (baseInstanceName h) ]
  -- A PARAMETERIZED model is not a model: it is a FAMILY, and the
  -- members the module names are minted below, once each.
  let ownFams = [ i | i <- declared, not (null (inParams i)) ]
      fams    = ownFams ++ mbFamilies base
      insts0  = [ i | i <- declared, null (inParams i) ] ++ mbGenerated base
  ownFuncs <- sequence [ parseFunctorLine h
                       | (h, _, _) <- declLines, take 7 h == "functor" ]
  ownTransformations <- sequence [ parseTransformationLine h
                        | (h, _, _) <- declLines
                        , take 14 h == "transformation" ]
  -- A model of `Base` declares a WORD of its own name (so `[Opt]`
  -- is an ordinary quote and `lift2 [Opt]` lifts it at runtime); the
  -- scope itself is the renaming every `with Inst` performs, receipt
  -- included.
  ownBases0 <- sequence [ parseBaseInstance allAliases sigs theories h b
                        | (h, b, _) <- declLines, take 5 h == "model"
                        , isJust (baseInstanceName h) ]
  -- EVERY MEMBER OF A FAMILY THE MODULE ASKS FOR.  `with Fwd(Floats)`
  -- is an application; the model it applies to is minted here, deepest
  -- first, so `with Fwd(Fwd(Floats))` finds `Fwd(Floats)` already made.
  -- The applications are read off the SOURCE — def HEADERS, def bodies,
  -- main, model bindings and the two model names a transformation
  -- declares — because `with` is elaboration and a model must exist
  -- before it.
  genInsts <- familyInstances fams insts0
                ([ a | (_, h, _, _) <- defSrcs
                     , a <- headerApps (map inName fams) (hdrNames h) ]
                 ++ [ a | (_, _, b, _) <- defSrcs
                        , a <- modelApps (map inName fams) b ]
                 ++ modelApps (map inName fams) mainSrc0
                 ++ [ a | i <- insts0, (_, b) <- inBindings i
                        , a <- modelApps (map inName fams) b ]
                 ++ [ a | mo <- ownTransformations, n <- [tfFrom mo, tfTo mo]
                        , a <- modelApps (map inName fams) n ])
  let insts    = insts0 ++ genInsts
      ownBases = ownBases0 ++ mbBases base
  -- A model whose theory has a hom-object is a CATEGORY model: its
  -- shape is read here, once, and `with` of it transports.  There is no
  -- `mode` line any more — the model is the declaration.
  ownTrans <- catMaybes <$> mapM (transportOf allDatas theories) insts
  -- every model with a carrier, REPRESENTABLE ONES INCLUDED (stage 7b
  -- commit 4).  Each consumer says for itself why it treats a
  -- representable one differently: `elabHeaders` transports it fused
  -- with the group it was named beside, `inTarget` answers about the
  -- resource, `transDefs` writes it no word (the roll constructor has
  -- the name), and a def under `with R` is not a K-word of R (it
  -- produces no carrier \8212 the carrier is cancelled).
  let trans = ownTrans ++ mbTrans base
      funcs = ownFuncs ++ mbFuncs base
      -- one namespace for every name a `with` header may carry
      useNames = map fst funcs ++ map inName ownBases
                 ++ [ inName i | i <- insts ] ++ map tfName ownTransformations
  case [ n | (n, i) <- zip useNames [0 :: Int ..]
           , n `elem` take i useNames ] of
    (n : _) | n `elem` map inName ownBases || n `elem` map inName insts ->
      Left $ "Duplicate model declaration: " ++ n ++ " (a functor and a "
          ++ "model share one namespace — each declares a name a `with` "
          ++ "clause may carry)"
    (n : _) -> Left $ "Duplicate functor declaration: " ++ n
    []      -> Right ()
  instDefs <- concat <$> mapM (instanceDefs theories) insts
  -- A TRANSFORMATION contributes its component as a word, the two sides of
  -- every square, and the sampled law for each square the theory's
  -- evidence can decide.  They are ordinary defs, named with the
  -- compiler's `@` so no source can reach them.
  transformationParts <- mapM (transformationDefs theories insts) ownTransformations
  let transformationDefSrcs = concatMap fst transformationParts
  slotTable <- (++ mbSlots base)
                 <$> sequence [ (\th -> (inName i, (thName th, slotWords th)))
                                  <$> theoryOf theories (inTheory i)
                              | i <- insts ]
  slotSigs <- concat <$> mapM (declaredSlots theories) insts
  -- a transformation's component is forward-declared at the type the two
  -- model heads wrote, so a def may name it however the declarations
  -- are ordered — the same courtesy a theory slot gets
  transformationSigs <- sequence [ (,) (tfName mo) . generalize M.empty
                            <$> componentArrow theories insts mo
                        | mo <- ownTransformations ]
  -- a functor's receipt is a word in the environment from here on: defs,
  -- model bodies and main are all inferred with it in scope
  let envSig = foldr (\(n, sc) e -> M.insert n sc e) (receiptEnv funcs env1)
                     (slotSigs ++ transformationSigs)
  -- The Base-model words are hoisted ABOVE the module's own defs:
  -- their bodies mention nothing but the prelude, and `with Opt` inside a
  -- def needs the word to be runnable by then (the ordering rule).
  --
  -- A transporting model also gets a WORD of its own name, so that the
  -- same functor is a value (`[Circuits]`, `lift2 [Circuits]`).
  let transDefs = [ ( tpName m, noHdr
                    , transportDefSrc m (slotDefName (tpName m) e)
                                        (slotDefName (tpName m) c)
                    , Just ("model " ++ tpName m ++ " in " ++ tpTheory m
                             ++ " — `;` is " ++ c ++ ", a stage is " ++ e
                             ++ ", the carrier is " ++ tpCarrier m) )
                  | m <- ownTrans, isNothing (tpResource m)
                  , Just c <- [tpCompose m], Just e <- [tpEmbed m] ]
      -- ...and a RESOURCE model gets no word of its own name, because
      -- the name is already taken by the roll constructor the `data`
      -- machinery wrote: `Log : Str \8658 Log` IS the entry to `Log`'s
      -- category, and a second def of that name would be a duplicate.
      resDefs = concatMap resModelDefs ownRes
      -- ...and ONLY a model with the identity object map gets one.  An
      -- object-mapped model's action on a literal is not a rename and
      -- its action on a def is an unfolding, so there is no rewrite
      -- table for `rewrite` to hold: it is an elaboration-time functor
      -- and says so (`:doc`).
      baseDefs = [ ( inName i, noHdr, baseInstDefSrc (baseWordTable i)
                   , Just ("model " ++ inName i ++ " in Base — "
                            ++ intercalate ", " [ p ++ " = " ++ q
                                                | (p, q) <- baseWordTable i ]) )
                 | i <- ownBases0, null (inObjMap i) ]
      resNames = [ dName d | d <- allDatas, dResource d ]
  -- model bodies come LAST, over an environment that already holds
  -- every module def and every slot's declared signature
  let addDef' = addDef defLine (tblTypes, tblGen) slotTable funcs thNames trans
                       ownBases resNames
                       [ (inName i, inScope i) | i <- insts ] allDatas
                       (RCtx M.empty allDatas allAliases theories)
  stA <-
    foldM addDef'
          (envSig, runTy, shadow0 ++ map fst slotSigs ++ map fst transformationSigs,
           [], docs0,
           mbTemplates base, mbKWords base, [])
          (baseDefs ++ transDefs ++ resDefs ++ defSrcs)
  -- EVERY FUNCTOR'S GRAPH MORPHISM, CHECKED ONCE, here — over the
  -- module's own defs, which is where a morphism that names one can be
  -- read.  A `with F` earlier in the file has already checked it
  -- (`runFunctor`, the ordering rule); this is the declaration that
  -- nothing applies, and it is still a declaration.
  let envA = (\(e, _, _, _, _, _, _, _) -> e) stA
  mapM_ (uncurry (checkFunctorWord envA allDatas)) ownFuncs
  -- ...and the EXTENSION of each is a word of the functor's own name,
  -- so that the same functor is a value: `[Traced]` is a quote and
  -- `lift2 [Traced]` applies it at runtime.  Same source as the one
  -- `with Traced` runs, so a functor's action has one spelling.
  let funcDefs = [ ( n, noHdr, functorExtSrc gm
                   , Just ("functor " ++ n ++ " \8212 the Code \8658 Code "
                            ++ "extension of the graph morphism `" ++ gm
                            ++ "`") )
                 | (n, gm) <- ownFuncs ]
  st0 <-
    foldM addDef' stA
          (funcDefs ++ instDefs
             ++ [ (n, noHdr, b, d) | (n, b, d) <- transformationDefSrcs ])
  -- STAGE 8: THE MODULE'S DECLARATION PROGRAM, run here \8212 above
  -- main, below the defs, which is the dictionary a compile-time word
  -- sees (the ordering rule).  Every top-level group whose GRADE
  -- carries `Dict` is one, is run against the dictionary, and is lifted
  -- out of main; everything else is main, in the order it was written.
  -- the calls a bound keyword's lines made ride WITH the program's own
  -- declaration lines, merged by the line they were written on, so that
  -- file order is file order whichever way a declaration was spelled
  (stD, mainGroups) <-
    foldM (declProgramStep addDef' allDatas allAliases theories slotTable
                           funcs thNames trans ownBases tblTypes resNames)
          (st0, [])
          (mergeByLine [ [c] | c <- dkCalls dict ] (logicalLines mainLines0))
  let (env', runFinal, _, defsRev, docs, tmpls, kwords, routedWhy) = stD
      mainLines = concat (reverse mainGroups)
      mainSrc   = intercalate "\n" (map snd mainLines)
      mainLine  = \k -> case drop (k - 1) mainLines of
                          ((orig, _) : _) | k >= 1 -> orig
                          _                        -> 0
  -- the generated transport word is checked like any other functor's
  -- word: if a model's slots ever stop composing, the message says so
  -- here
  mapM_ (\(n, _, _, _) -> checkCodeWord env' n) transDefs
  -- every slot's inferred type must match the theory's declaration,
  -- instantiated at this model's arguments
  mapM_ (checkInstance env' theories) insts
  -- Every binding is blessed ONCE, here, over the finished environment
  -- — so a model of `Base` may name a word declared anywhere in the
  -- module, exactly as a model slot may.
  mapM_ (checkBaseInstance env' allDatas tmpls (map thName theories)
           [ (thName th, map fst (thSlots th)) | th <- theories ])
        ownBases0
  -- a registered check is a program with type `\8226 \8658 Bool`, and a
  -- malformed one is a declaration error rather than a mystery at
  -- module start \8212 the same courtesy a law gets
  mapM_ (checkTestType env') [ n | (n, _, _) <- defsRev, isJust (testParts n) ]
  mapM_ (checkLawType env') [ n | (n, _, _, _) <- instDefs, isJust (lawParts n) ]
  mapM_ (checkLawType env')
        [ n | (n, _, _) <- transformationDefSrcs, isJust (squareParts n) ]
  -- every square decided, by the normalizer or at the samples; the
  -- verdicts are kept on the module, so nothing decides them twice
  transformationInfos <- sequence [ checkTransformation env' runFinal theories insts mo sqs
                         | (mo, (_, sqs)) <- zip ownTransformations transformationParts ]
  let topCtx = ElabCtx env' runFinal slotTable funcs tmpls
                        thNames trans kwords ownBases []
                        False Nothing tblTypes resNames
                        (RCtx M.empty allDatas allAliases theories)
  -- WHAT AN OBJECT-MAPPED MODEL SAYS ABOUT ITSELF (stage 7c): the head,
  -- the table, and the verdict on each law the declaration states — the
  -- retraction, and `image = F(body)` wherever an image was given to a
  -- word that HAS a body.  `sameCode` decides them where it reaches;
  -- where it does not the model stands as a DIALECT and the doc says
  -- so, which is the optimizer/dialect line this file already draws.
  objDocs <- mapM (objModelDoc topCtx)
                  [ i | i <- ownBases0, not (null (inObjMap i)) ]
  (mainPart, envM, defsM, docsM) <-
    if all isSpace mainSrc
      then pure (Nothing, env', reverse defsRev, docs)
      else do
        (term0, mainStart) <- parseProgramFrom mainLine allDatas mainSrc
        term1 <- elabHeaders topCtx term0
        gens  <- objGenDefs topCtx term1
        -- the RunDefs `objGenEntries` threads is the SCOPE each
        -- unfolding is checked in and nothing else: the module's own
        -- runtime scope is rebuilt from its defs (`buildRunDefs`), and
        -- the entries are on that list.
        (eG, _, dG, entries) <- objGenEntries env' runFinal docs gens
        arr <- inferTermInAt mainStart eG term1
        pure (Just (term1, arr), eG, reverse defsRev ++ entries, dG)
  -- own lists are built latest-first, which is exactly the match order
  pure (Module envM defsM ownAliases ownDatas
                (foldr (uncurry M.insert) docsM objDocs) mainPart
                theories insts ownFams funcs tmpls ownTrans kwords ownBases
                transformationInfos (reverse routedWhy))
  where
    preludeTypeNames = map aName (mbAliases base) ++ map dName (mbDatas base)

    addType tblTypes (env, run, aliasesIn, datasIn, ownAl, ownDt, docs) (line, doc) = do
      decl <- parseTypeLine aliasesIn datasIn line
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
          pure ( env, run
               , al : filter ((/= n) . aName) aliasesIn
               , datasIn, al : ownAl, ownDt, docs' )
        Right dd -> do
          -- shadowing a prelude data type replaces its constructors
          let shadowed = [ f | d0 <- datasIn, dName d0 == n, f <- dFields d0 ]
              envC
                | n `elem` preludeTypeNames =
                    foldr M.delete env
                          ([n, "un" ++ n, "merge" ++ n, "fold" ++ n]
                             ++ shadowed)
                | otherwise = env
          if M.member n envC || M.member ("un" ++ n) envC
               || M.member ("merge" ++ n) envC
            then Left $ "Type " ++ n
                     ++ ": constructor name collides with an existing definition"
            else Right ()
          -- A FIELD NAME IS A WORD, so it collides like one.  Objects
          -- are added, never merged: two declarations may not share a
          -- projection, and a projection may not quietly replace a def
          -- or a prim.
          case [ f | f <- dFields dd
                   , M.member f envC
                     || f `elem` [n, "un" ++ n, "merge" ++ n, "fold" ++ n] ] of
            (f : _) ->
              Left $ "Type " ++ n ++ ": field name '" ++ f
                  ++ "' is already a word in scope.  A field name becomes "
                  ++ "an ordinary definition of that name, and Braid adds "
                  ++ "objects rather than merging them — "
                  ++ (if n `elem` tblTypes
                        then "rename the column with the schema form, `table "
                          ++ n ++ "(col: Type, …) = \"…\"`, or rename the "
                          ++ "existing '" ++ f ++ "'."
                        else "rename " ++ n ++ "'s field, or rename the "
                          ++ "existing '" ++ f ++ "'.")
            [] -> Right ()
          -- constructors/unrollers must be CALLABLE by a functor, so the
          -- data artifacts join the elaboration-time scope too
          let (scs, runs) = dataDeclArtifacts dd
              docs'' = case dataFoldArtifact dd of
                         Just (fn, _, _, fdoc) -> M.insert fn fdoc docs'
                         Nothing               -> docs'
          pure ( foldr (uncurry M.insert) envC scs
               , extendRunDefs run [ (nm, ar, op, t)
                                   | (nm, (ar, op, t)) <- runs ]
               , filter ((/= n) . aName) aliasesIn
               , dd : filter ((/= n) . dName) datasIn
               , ownAl, dd : ownDt, docs'' )
    addDef defLine (tblTypes, tblGen) slotTable funcs thNames trans bases
           resources instScopes datas refl
           (env, run, shadow, acc, docs, tmpls, kws, routed)
           (name, hdr, bodySrc, doc) =
      -- ATTRIBUTION, ONCE (2026-09-15).  Everything a def's own check
      -- can refuse — the parse, the destructuring rewrite, the `\`
      -- continuation, `in`'s target, the `with` elaborator, the
      -- functor and transport expansions, inference, the K-word shape,
      -- and the module-level refusals about the def's NAME — is wrapped
      -- here rather than at each site, so no path can be added that
      -- forgets to say which def it is in.
      first inDef $ do
      -- where this body sits in the file: a run of consecutive lines
      -- starting at `base`, or nothing at all for text the compiler
      -- wrote (a model's slot, a transport word, a square)
      let base    = defLine name
          bodyAt k = if base == 0 then 0 else base + k - 1
      if name `elem` elimEmits && M.member name env
        then Left $ "`" ++ name ++ "` cannot be shadowed: abstraction "
                 ++ "elimination EMITS it, so a def of that name would "
                 ++ "capture reflected code that never mentioned it "
                 ++ "(MANUAL §6).  Pick another name."
        else Right ()
      if (M.member name env && name `notElem` shadow)
           || isJust (lookup name tmpls)
        then Left $ "Duplicate definition: " ++ name
        else Right ()
      (body0, bodyStart) <- parseProgramFrom bodyAt datas bodySrc
      -- THE TWO HEADER CLAUSES, read here and nowhere else (2026-09-16).
      --
      -- `in T` for a theory T makes this def a MORPHISM OF T.  With no
      -- model of T applied it is a TEMPLATE — a body waiting for one;
      -- with one applied it is INSTANTIATED right here, which is a
      -- renaming and not a transport (see `Apply`).
      let inTh    = case dhIn hdr of
                      Just t | t `elem` thNames -> Just t
                      _                         -> Nothing
          -- the model of `in`'s theory that this header applies, if any
          instOf  = [ n | t <- maybe [] pure inTh, n <- dhWith hdr
                        , Just (t', _) <- [lookup n slotTable], t' == t ]
          -- INFERRED ROUTING (stage 7b).  A def that CALLS a resource
          -- word is routed for that resource with no header at all;
          -- `with E` is the explicit, idempotent override, so a header
          -- that already names a resource wins outright and nothing is
          -- added beside it.
          routing
            | any (`elem` resources) (dhWith hdr) = Nothing
            | otherwise = inferRouting (M.delete name env) resources body0
          withNs  = dhWith hdr ++ maybe [] snd routing
          applied = case withNs of
            [] -> id
            ns -> With (if null instOf then Transporting else Instantiating) ns
      case (inTh, instOf) of
        (Just th, []) ->
          -- A TEMPLATE is recorded, not defined.  It has no body that
          -- runs without a model, so it enters neither the environment
          -- nor the runtime scope; the table is the prefix scope
          -- templates live in, exactly as defs do.
          pure ( env, run, shadow, acc
               , maybe docs (\d -> M.insert name d docs) doc
               , (name, (th, applied body0)) : tmpls, kws, routed )
        _ -> do
          -- `in M` — a HAND-BUILT morphism of the category M presents,
          -- written in M's vocabulary.  The clause APPLIES NOTHING: it
          -- puts the model's slot words in scope (the renaming `with`
          -- also does) and stops there — no embedding, no composition,
          -- no receipt.  It is consumed here, where a def is recorded.
          (asc, termH) <- case dhIn hdr of
            Just n | isNothing inTh ->
              (\m -> (Just m, applied body0))
                <$> inTarget thNames trans slotTable funcs bases
                             resources n
            _ -> Right (Nothing, applied body0)
          let env1 = M.delete name env   -- a shadowed def must not leak in
          -- `with` scopes are written out here, between parse and infer: a
          -- syntactic Term rewrite with the Env available for arities and
          -- resource signatures.
          -- a def whose own header names a category is a K-WORD: it produces
          -- a carrier, and a later `with K` leaves it alone instead of
          -- embedding it.  Syntactic knowledge, recorded before the body
          -- is elaborated, in the same prefix scope every def lives in.
          -- `with K` transports it; `in K` declares it built by hand.
          --
          -- ...unless it LEAVES the category on purpose.  An exit takes
          -- the carrier and hands back base, so a def that calls one is
          -- an observation written in M's vocabulary, not a morphism of
          -- M: it is neither shape-checked nor tabled.  Which slots are
          -- exits is read off their declared arrows, so this is a
          -- syntactic test against a written signature.
          let kws' = case asc of
                Just _  -> kws     -- decided after inference, below
                Nothing -> case termH of
                  With Transporting ns _
                    | (k : _) <- [ tpName m | m <- trans
                                            , isJust (tpCompose m)
                                            , isNothing (tpResource m)
                                            , tpName m `elem` ns ] ->
                        (name, k) : kws
                  _ -> kws
              -- a model's own slot and law defs are wrapped in `with
              -- I` to resolve slot names; that scope applies nothing and
              -- mints nothing (see `ecSelf`)
              self = case break (== '@') name of
                (i, '@' : _) | Just sc <- lookup i instScopes -> i : sc
                _                                             -> []
          -- `in` MINTS NOTHING, ever.  A receipt is provenance — "this
          -- code went through the functor" — and a hand-built morphism
          -- is by definition not the functor's image; it may be a
          -- circuit no base program denotes.  Putting `K` on it would
          -- over-claim in exactly the gap between "went through F" and
          -- "is in the image of F".  Membership is carried by the TYPE
          -- (checked below) and by the K-word table, and nothing else:
          -- only a `with` mints, and since 2026-09-18 a `with` mints
          -- exactly when it CHANGED the code — so the gap the receipt
          -- used to leave has closed from the other side too.
          let ectx = ElabCtx env1 run slotTable funcs tmpls
                              thNames trans kws bases self
                              ('@' `elem` name || name `elem` tblGen)
                              (Just name) tblTypes resources refl
          term0' <- elabHeaders ectx termH
          -- `in M` resolves M's slot names, and does it AFTER the walk
          -- above, which is the walk that keeps `@` out of source.
          let term = case asc of
                Just m | Just (_, sl) <- lookup (tpName m) slotTable ->
                  renameSlotsT (tpName m) sl term0'
                _ -> term0'
          -- self-reference is refused AFTER expansion, so a functor that
          -- splices the name in is caught too
          let mentions = primsIn term
          if name `elem` mentions
            then Left (selfReferenceError name False)
            else Right ()
          if "recurse" `elem` mentions && not (M.member "recurse" env1)
            then Left (selfReferenceError name True)
            else Right ()
          -- THE UNFOLDINGS AN OBJECT-MAPPED SCOPE ASKED FOR (stage
          -- 7c), installed BESIDE this def and before it: `M@poly` is
          -- an ordinary word from here on, with its own type and its
          -- own line in `:defs`, and every later scope that asks for
          -- the same unfolding finds it already made.
          gens <- objGenDefs ectx term
          (envG, runG, docsG, gentries) <- objGenEntries env1 run docs gens
          let accG = reverse gentries ++ acc
          (arr, dsubs) <- inferTermSubAt bodyStart envG term
          -- `in M` classifies BY SHAPE.  A def that builds one carrier
          -- out of nothing is a morphism of M and joins the K-word
          -- table; one that does not is a base word written in M's
          -- vocabulary — an observation, a composite that exits, a
          -- runner — and is left alone.  The WRITTEN header is what
          -- makes the question askable: a def with no header that
          -- happens to produce a carrier is still not a word of M, so
          -- no inferred type is ever scanned for membership.
          case asc of
            Just m -> checkKWordShape m name
                        (any (`elem` primsIn term)
                             [ slotDefName (tpName m) sl
                             | Just (_, sls) <- [lookup (tpName m) slotTable]
                             , sl <- sls ])
                        (normalizeArrow arr)
            _ -> Right ()
          -- ...and an INSTANTIATED template is classified the same way
          -- (2026-09-16): `def f in Prob with Enum = …` is a morphism
          -- of the theory read by a model, so if it builds one carrier
          -- out of nothing it is one of that model's words and a later
          -- `with Enum` must leave it alone.  Same question, same test,
          -- asked of the model the `with` named.
          let kws2 = case (asc, instOf) of
                (Just m, _) | isKWordShape m (normalizeArrow arr) ->
                  (name, tpName m) : kws'
                (Nothing, i : _)
                  | (m : _) <- [ t | t <- trans, tpName t == i
                                   , isJust (tpCompose t) ]
                  , isKWordShape m (normalizeArrow arr) ->
                      (name, tpName m) : kws'
                _ -> kws'
          let sc = generalizeWith envG dsubs arr
          pure ( M.insert name sc envG
               , extendRunDefs runG [(name, arityOf sc, openOf sc, term)]
               , filter (/= name) shadow
               , (name, sc, term) : accG
               , maybe docsG (\d -> M.insert name d docsG) doc
               , tmpls, kws2
               , case routing of
                   Just (a, run') ->
                     (name, "routed for " ++ unwords run'
                              ++ ": calls `" ++ a ++ "`") : routed
                   Nothing -> routed )
      where
        inDef e = case transformationNameParts name of
          Just (mo, sl) ->
            "transformation " ++ mo ++ ": the square for slot '" ++ sl
              ++ "' does not typecheck (" ++ e ++ ") \8212 the component "
              ++ "must be a word from the source model's carrier to the "
              ++ "target's, and every slot's square must be writable at it"
          Nothing -> "in def " ++ name ++ ": " ++ e

--------------------------------------------------------------------------------
-- 10.5 Prelude: derived definitions available in every module and REPL
-- session.  All user code — the primitive set stays minimal.  User defs
-- shadow prelude defs silently.
--------------------------------------------------------------------------------

preludeSrc :: String
preludeSrc = unlines
  [ "## the boolean object: a bare two-way decision"
  , "type Bool = (• | •)"
  , "## an optional value, PAYLOAD FIRST: one element, or empty.  The order matters here in a way it does not in Haskell — alt1 is the track `>=>` threads and `ok` builds, so a payload-second Maybe could not ride the railway at all."
  , "type Maybe(...) = (... | •)"
  , "## the list: initial algebra of (• | a X); foldList is generated"
  , "type List(a) = (• | a List(a))"
    -- a whole stack as ONE wire: what multi-wire aggregates become now
    -- that list cells hold a single wire
  , "data Box(...) = (...)"
  , "## the empty list"
  , "def nil = alt1 >> List"
  , "## prepend an element"
  , "def cons = alt2 >> List"
  , "## open one layer: the asymmetric list router"
  , "def uncons = unList"
  , "## left fold: step sees [acc, elem], list consumed left to right."
  , "## Derived from the STRUCTURAL recursor rather than written"
  , "## recursively: fold the list up into an endofunction of the"
  , "## accumulator (Church-style, as pack2 does), then ev it to the"
  , "## seed.  So `fold` — and map/filter/reverse/append/concat with it —"
  , "## terminates by construction and needs no `fix`."
  , "def fold = (f b l -> l >> [[pass]] [(g x -> [(acc -> f acc x >> ev >> g ... >> ev)])] ... >> foldList >> _ b >> ev)"
  , "## a reflected atom: prim | int | str | sym | quote | row | group"
  , "data Atom = (Sym | Int | Str | Sym | List(List(Atom)) | List(List(List(Atom))) Bool | List(List(Atom)))"
  , "## code is a chain of tensor stages of atoms (spine normal form)"
  , "type Stage = List(Atom)"
  , "type Code = List(Stage)"

  , "## ev a quoted function to every element"
  , "def map = (f l -> l >> [nil] [(r x -> f x >> ev >> _ r >> cons)] ... >> foldList)"
  , "## the identity, named.  It IS the `_` of a tensor stage -- `_` is"
  , "## the positional spelling (a wire this stage does not touch), `id`"
  , "## the word.  One morphism, so one of them is a def."
  , "##   id : a0 => a0"
  , "def id = _"
  , "## invert a router: swap the hit and miss tracks"
  , "def not = (miss | ok) >> merge"
  , "## keep only a router's decision: collapse both payloads to nothing"
  , "def verdict = (forget | forget)"
  , "## the other three Int comparators, DERIVED from `lt?`.  `gt?` is"
  , "## `lt?` with its arguments exchanged (and the payload put back);"
  , "## `gte?`/`lte?` are the track swap of the other two.  `not` opens"
  , "## the row (injections are open), so a closed 2-row re-closes it --"
  , "## which is what makes the derived schemes IDENTICAL to the prims'."
  , "##   gt? gte? lte? : Int Int => (Int Int | Int Int)"
  , "def gt? = swap >> lt? >> (swap | swap)"
  , "def gte? = lt? >> not >> (pass | pass)"
  , "def lte? = gt? >> not >> (pass | pass)"
  , "## the two Float words that are NOT implementation.  Negation is `0.0 minus`; absolute value is one comparison.  Everything else about a double is a machine fact, so it is a prim (MANUAL 9)."
  , "##   fneg fabs : Float => Float"
  , "def fneg = (x -> 0.0 x >> fsub)"
  , "def fabs = (x -> x 0.0 >> flt? >> ((v w -> v >> fneg) | (v w -> v)) >> merge)"
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
  , "def assocL = (alt1 >> alt1 | (alt2 >> alt1 | alt2) >> merge) >> merge"
  , "## re-nest a sum rightward: ((A | B) | C) => (A | (B | C))"
  , "def assocR = ((alt1 | alt1 >> alt2) >> merge | alt2 >> alt2) >> merge"
  , "## negate a quoted router, as a value"
  , "def negate = (p -> [p ... >> ev >> (miss | ok) >> merge])"
  , "## and on quoted routers: hit iff both hit; q runs only on p's hit"
  , "def both = (p q -> [p ... >> ev >> (q ... >> ev | miss) >> merge])"
  , "## or on quoted routers: hit if p hits, otherwise q decides"
  , "def either = (p q -> [p ... >> ev >> (ok | q ... >> ev) >> merge])"
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
    -- THE N-FAMILY, DERIVED.  Every one of these is `mapAccumN` at a
    -- different MOTIVE (design-exponents.md, amendment 2026-09-21):
    -- `foldExp` at the constant carrier (the output bundle is a
    -- discarded copy of the accumulator — `b := •` is unreachable,
    -- because `b` is a WIRE variable and `•` is not a wire), `mapN` at
    -- `n ↦ bⁿ` (the accumulator is the quotation itself, threaded
    -- untouched), and the two-wire twins by BOXING the element:
    -- `splitN >> zipN` re-chunks a flat `(a b)ⁿ` as `Box(a b)ⁿ`, one
    -- wire each, and then the one-wire words serve.  `dupN` joins
    -- them (2026-09-21): with `unzipN` boxed it is the diagonal
    -- `mapAccumN` writes, `[(s x -> s (x >> dup >> Box))]`, unboxed
    -- back into two lanes.
  , "## fold a bundle: aⁿ collapsed by a step, DERIVED at the constant"
  , "## motive.  The step's own output bundle is a copy of the"
  , "## accumulator, discarded by the group that forgets the segment."
  , "def foldExp = (f b ... -> [(s x -> f s x >> ev >> dup)] b ... >> mapAccumN >> (r ... -> r (... >> forget)))"
  , "## map a one-wire word across a bundle, DERIVED with the quotation"
  , "## itself as the accumulator — threaded untouched, then dropped"
  , "def mapN = (f ... -> [(s x -> s (f x >> ev))] f ... >> mapAccumN >> (acc ... -> ...))"
  , "## copy a bundle (the GLA Δ), DERIVED: box a copy of every"
  , "## element, then unbox the bundle of pairs into two lanes.  The"
  , "## accumulator is an unread Int — mapAccumN wants a wire and this"
  , "## motive has no state to carry."
  , "def dupN = [(s x -> s (x >> dup >> Box))] 0 ... >> mapAccumN >> (acc ... -> ... >> unzipN)"
  , "## the two-wire twins: box each pair (`splitN >> zipN`), then the"
  , "## one-wire words do the work.  This is the boxing discipline —"
  , "## a multi-wire element always fits in one wire (MANUAL §13)."
  , "def mapN2 = (f ... -> splitN >> zipN >> [(p -> f (p >> unBox) >> ev)] ... >> mapN)"
  , "## fold a bundle of PAIRS; the step sees [acc, a, b]"
  , "def foldExp2 = (f b ... -> splitN >> zipN >> [(s p -> f s (p >> unBox) >> ev >> dup)] b ... >> mapAccumN >> (r ... -> r (... >> forget)))"
  , "## box a bundle as a list, DERIVED from its own eliminator:"
  , "## pack : aⁿ ⇒ List(a) — the flat list constructor; groups delimit"
  , "def pack = [(l x -> x l >> cons)] nil ... >> foldExp >> reverse"
  , "## two-wire elements: (a b)ⁿ ⇒ List(a b).  reverse/append are"
  , "## single-wire words, so order is kept Church-style: fold up a"
  , "## FUNCTION, then ev it to nil"
  , "def pack2 = [(f x y -> [(l -> f ((x y >> Box) l >> cons) >> ev)])] [pass] ... >> foldExp2 >> _ nil >> ev"
  , "## top-first packs: head = TOP of the segment.  With a `...` ladder"
  , "## (each line pushes UNDER), list order = TEXT order — the vertical"
  , "## list idiom:   line1 / line2 ... / line3 ... / packR"
  , "def packR = [(l x -> x l >> cons)] nil ... >> foldExp"
  , "def pack2R = [(l x y -> (x y >> Box) l >> cons)] nil ... >> foldExp2"
  , "## first-match over a clause list: each clause is [router] [action];"
  , "## the first router that hits runs its action on x, else the default."
  , "## the always-hit router: the last lane of a guard clause list"
  , "def else? = alt1"
  , "## probe a clause list (pack2 / pack2R lanes): run the first hit;"
  , "## alt1(result) on a hit, alt2(input) if none hit"
  , "def choose = (x clauses -> clauses >> [x >> alt2] [(rest c -> c >> unBox >> (p f -> x >> p ... >> ev >> (f ... >> ev >> alt1 | drop >> rest) >> merge))] ... >> foldList)"
  , "def matchWith = (x default clauses -> x clauses >> choose >> (pass | default ... >> ev) >> merge)"
  , "## commute List over the sum monad: all hits, or the first miss"
  , "def sequence = [nil >> ok] [(r x -> x >> ((y -> r >> (y ... >> cons | ---)) | miss) >> merge)] ... >> foldList"
  , "## keep the elements a quoted router hits"
  , "def filter = (p -> [p ... >> ev >> (single | drop >> nil) >> merge]) ... >> flatMap"
  , "## splice one level of right-nesting into the parent row — ANY"
  , "## inner arity (the row variable does the counting):"
  , "##   splice : (ρ0 | (σ0)) ⇒ (ρ0 | σ0)"
  , "def splice = (alt1 | there) >> merge"
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
  , "def case2 = (f g s -> s >> (f ... >> ev | g ... >> ev) >> merge)"
  , "def case3 = (f g h s -> s >> (f ... >> ev | (g ... >> ev | h ... >> ev) >> merge) >> merge)"
  , "def case4 = (f g h i s -> s >> (f ... >> ev | (g ... >> ev | (h ... >> ev | i ... >> ev) >> merge) >> merge) >> merge)"
  , "## LAMBDA -- the exponential's other map, beside `ev`.  `curry` takes"
  , "## a program that wants one extra wire DEEPEST and returns one that"
  , "## takes that wire and hands back the rest as an Fn.  Its own body is"
  , "## the one binder-into-quote that abstraction elimination takes as a"
  , "## GENERATOR rather than eliminating: every other capture is rewritten"
  , "## into `capture`, which is `curry` then `ev` (MANUAL §6)."
  , "##   curry : Fn⟨a ρ0 ⇒ ρ1⟩ ⇒ Fn⟨a ⇒ Fn⟨ρ0 ⇒ ρ1⟩⟩"
  , "def curry = (f -> [(x -> [x ... >> f ... >> ev])])"
  , "## partial application: bind one value into the DEEPEST input of an"
  , "## Fn.  Derived -- curry, then ev -- and the word abstraction"
  , "## elimination emits once per captured parameter, shallowest first."
  , "##   capture : a Fn⟨a ρ0 ⇒ ρ1⟩ ⇒ Fn⟨ρ0 ⇒ ρ1⟩"
  , "def capture = (x f -> (f >> curry) x >> ev)"
  , "## distribute a wire over a coproduct.  Not a prim and not an axiom:"
  , "## in a cartesian CLOSED category `P x -` is a left adjoint (that is"
  , "## `curry`), left adjoints preserve coproducts, and the body below is"
  , "## that proof -- capture the wire into one handler per track, then"
  , "## case over the sum.  distN follows caseN's arity family, and like"
  , "## caseN the sums nest: polymorphism does not reach a row's width."
  , "##   dist2 : a (ρ0 | ρ1) ⇒ (a ρ0 | a ρ1 | σ0)"
  , "def dist2 = (x s -> x [(y ... -> y ... >> alt1)] >> capture >> _ x [(y ... -> y ... >> alt2)] >> _ capture >> _ _ s >> case2)"
  , "def dist3 = dist2 >> (pass | dist2)"
  , "def dist4 = dist2 >> (pass | dist3)"
  , "## the easy direction: pull a shared deepest wire out of every track."
  , "## Always available (no closed structure needed) -- it is the map any"
  , "## category with coproducts has, and `dist` is its inverse."
  , "##   undist2 : (a ρ0 | a ρ1) ⇒ a (ρ0 | ρ1 | σ0)"
  , "def undist2 = (s -> s >> (_ alt1 | _ alt2) >> merge)"
  , "def undist3 = (pass | undist2) >> undist2"
  , "def undist4 = (pass | undist3) >> undist2"
  , "def condFn = (b t e -> b >> (t | e) >> merge)"
  , "## a Bool selects a quotation; ev runs it on the rest of the stack"
  , "def cond = condFn ... >> ev"
  , "def whenFn = (b t -> b >> (t | [...]) >> merge)"
  , "## run the quotation only when the Bool hits"
  , "def when = whenFn ... >> ev"
  , "def unlessFn = (b t -> b >> ([...] | t) >> merge)"
  , "## run the quotation only when the Bool misses"
  , "def unless = unlessFn ... >> ev"
  , "## the length of a list"
  , "def len = [0] [_ drop >> 1 ... >> +] ... >> foldList"
  , "## sum and product of an Int list"
  , "def sum = [+] 0 ... >> fold"
  , "def product = [*] 1 ... >> fold"
  , "def downFrom with Recursive = (n -> n >> zero? >> (drop >> nil | (m -> (m 1 >> -) >> downFrom >> (m 1 >> -) ... >> cons)) >> merge)"
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
  , "def take with Recursive = (n l -> n >> zero? >> (drop >> nil | (m -> l >> unList >> (nil | (x r -> (m 1 >> -) r >> take >> x ... >> cons)) >> merge)) >> merge)"
  , "def skip with Recursive = (n l -> n >> zero? >> ((z -> l) | (m -> l >> unList >> (nil | (x r -> (m 1 >> -) r >> skip)) >> merge)) >> merge)"
  , "## the i-th element, counting from 0, or nothing: Int List(a) => (a | \8226)"
  , "def nth = (i l -> i l >> skip >> unList >> (alt2 | (x r -> x >> alt1)) >> merge >> (pass | pass))"
  , "## zip two lists into flat two-wire elements: List(a) List(b) => List(a b)"
  , "def zip with Recursive = (l r -> l >> unList >> (nil | (x xs -> r >> unList >> (nil | (y ys -> xs ys >> zip >> (x y >> Box) ... >> cons)) >> merge)) >> merge)"
  , "## the other half of the pair: split a list of two-wire elements"
  , "## back into two lists.  `zip >> unzip` is the identity, and"
  , "## `unzip >> zip` is too on lists of equal length -- which is the"
  , "## strength of any category whose objects are columns"
  , "##   unzip : List(Box(a b)) => List(a) List(b)"
  , "def unzip with Recursive = (l -> l >> unList >> ((nil) (nil) | (x r -> r >> unzip >> (as bs -> x >> unBox >> (u v -> (u as >> cons) (v bs >> cons))))) >> merge)"
  , "## conjunction / disjunction over a Bool list"
  , "def all = [true] [and] ... >> foldList"
  , "def any = [false] [or] ... >> foldList"
  , "## split a list of sums into two lists (hits, misses) — two wires,"
  , "## no bundling: our products are the stack itself"
  , "def partitionSum with Recursive = (l -> l >> unList >> ((nil) (nil) | (x r -> r >> partitionSum >> (as bs -> x >> ((v -> (v as >> cons) bs) | (w -> as (w bs >> cons))) >> merge))) >> merge)"
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
  , "def if   = (b f -> b [f >> alt1] [alt2] >> cond)"
  , "def elif = (acc b f -> acc >> (alt1 | (b [f >> alt1] [alt2] >> cond)) >> merge)"
  , "def else = (acc d -> acc >> (pass | d) >> merge)"
  , "## close a ladder with a quoted default: runs only if nothing hit."
  , "## (Also the total default for ifRoute/elifRoute ladders, where the"
  , "## undecided track still carries the routed value.)"
  , "def otherwise = (s a -> s >> (pass | a ... >> ev) >> merge)"
  , "## fold a product of decisions accumulated line by line with `...`:"
  , "##     (cond1) answer1 ...      <- each lane line pushes UNDER the"
  , "##     (cond2) answer2 ...         product (remainder on top), so"
  , "##     default         ...         lanes stack reversed and the"
  , "##     decide                      overwrite fold makes the FIRST-"
  , "## written true lane win.  a ((•|•) a)ⁿ ⇒ a — answers are values;"
  , "## quote them and `decide >> ev` when an answer does work."
  , "def decide = [(acc b f -> b f acc >> select)] ... >> foldExp2"
  , "## routing guards: the condition must be a router, and its hit VALUE"
  , "## flows into the action (so the action sees the routed/refined type)."
  , "def ifRoute   = (x p a -> x >> p ... >> ev >> (a ... >> ev | pass))"
  , "def elifRoute = (s p a -> s >> (alt1 | p ... >> ev >> (a ... >> ev | pass)) >> merge)"
  , "## box a Code value as a runnable Fn WITHOUT running it: the"
  , "## deferred half of reflect's round trip.  Takes the WITNESS whose"
  , "## type the code must meet, so the boxed Fn is ordinarily typed —"
  , "## Fn⟨Γ ⇒ (Δ | Str Γ)⟩ — and the check rides the railway at ev"
  , "## time.  On a miss the witness is still there to fall back to."
  , "def box = (w cd -> [(w) (cd) ... >> evalAs])"
  , "## a program's wiring as Code — nil when it has none to show (a closure)"
  , "def getCode = reflect >> ((c -> c) | drop >> nil) >> merge"
  , "## THE EXTENSION of a graph morphism to the whole of Code.  A"
  , "## `functor` declaration names one image per generator — `Fn⟨Stage"
  , "## ⇒ Code⟩` — and this is the word that carries it along every"
  , "## spine.  Functorial by the universal property (a functor out of a"
  , "## free category IS a graph morphism), so the law comes free rather"
  , "## than being a promise.  `atomwise` is the same one level down."
  , "def stagewise = flatMap"
  , "def atomwise = (f c -> c >> [[f ... >> ev] ... >> flatMap] ... >> map)"
  , "## the graph morphism that puts a stage after every generator,"
  , "## UNCHECKED; `interpose` is this one with the prim `checkedStage`"
  , "## in front, and that check is what makes it one you can trust"
  , "def interposeRaw = (h -> [(s -> (s >> pack) h >> append)])"
  , "def interpose = checkedStage >> interposeRaw"
  , "## the runtime lift of any Code ⇒ Code functor to Fn ⇒ Fn: the"
  , "## program is its own witness and its own fallback, so the result"
  , "## has the program's arrow by construction — a rewrite the witness"
  , "## refuses leaves the original running"
  , "def lift2 = (m f -> [f (m (f >> getCode) >> ev >> (c -> c)) ... >> evalAs >> (... | drop ... >> f ... >> ev) >> merge])"
  , "## sum an Int bundle: the variadic +"
  , "## run a program one wire deeper: `[f] >> lift` is f with one wire riding beneath it, untouched.  Compose it once per context wire.  This is tensorial STRENGTH — the action of (A ⊗ −) on a morphism — and it is what threads a resource past a pure stage, so it is an ordinary word rather than machinery."
  , "def lift = (f -> [_ (f ... >> ev)])"
  , "def sumN = [+] 0 ... >> foldExp"
    -- the GLA generators are DERIVED: `zipN` boxes each pair, so one
    -- `mapN` lifts any two-wire word pointwise and `+` and `*` are the
    -- only arithmetic the bundle tier needs to know about
  , "## pointwise add: the bundle monoid ∇, lifted from `+`"
  , "def addN = zipN >> [unBox >> +] ... >> mapN"
  , "## scale a bundle by a scalar, lifted from `*`"
  , "def scaleN = (k ... -> [k _ >> *] ... >> mapN)"
  , "## pointwise multiply (NOT linear — outside the GLA generators)"
  , "def mulN = zipN >> [unBox >> *] ... >> mapN"
  , "## pointwise subtract"
  , "def subN = zipN >> [unBox >> -] ... >> mapN"
  , "## guard lanes as a bare product: (Bool Fn)^n lanes, default Fn on"
  , "## top.  All conditions are pre-evaluated (probe every lane); the"
  , "## FIRST true lane's action runs, else the default — exactly one"
  , "## action ever runs (the fold selects quotes, applies once).  The"
  , "## accumulator is (decided | default): a true lane decides once;"
  , "## later lanes leave a decision alone."
  , "def firstTrue = (d -> d >> alt2) ... >> [(acc b f -> acc >> (alt1 | (g -> b [f >> alt1] [g >> alt2] >> cond)) >> merge)] ... >> foldExp2 >> merge >> ev"
  , "## OPEN RECURSION, derived.  `with Recursive` ties a def's own knot,"
  , "## so the fixpoint COMBINATOR is only needed when the body is a"
  , "## value someone hands you -- a memoizing or logging `self`.  Written"
  , "## eta-expanded, because Braid is call-by-value: the self-application"
  , "## sits under a quote and is tied only when the knot is run.  The"
  , "## `id` says the knot is ONE wire -- a grouped atom in non-final"
  , "## position is closed (MANUAL §4), and the knot's own arity is"
  , "## what closing would otherwise erase."
  , "##   fix : Fn⟨Fn⟨ρ0 =Recursive> ρ1⟩ ρ0 ⇒ ρ1⟩ =Recursive> Fn⟨ρ0 =Recursive> ρ1⟩"
  , "def fix with Recursive = (b -> [(b >> fix >> id) ... >> b ... >> ev])"
  , "## ELGOT ITERATION, derived: the Elgot dagger f† = ∇ ∘ (f† + id) ∘ f."
  , "## The body routes into (continue | done): the continue track"
  , "## re-enters through the knot, the done track falls out, and"
  , "## `merge` -- the codiagonal -- joins them.  NOTE this needs no"
  , "## `into`: the row is CLOSED and two-track, so the copairing"
  , "## [f†, id] is just `(f† | pass) >> merge`.  `into` is for the OPEN"
  , "## case (a residual, or more than one track left).  The knot is the"
  , "## def's own name, under `with Recursive`; the label is that scope's"
  , "## receipt."
  , "##   loop : Fn⟨ρ0 =Recursive> (ρ0 | ρ1)⟩ ρ0 =Recursive> ρ1"
  , "def loop with Recursive = (f ... -> f ... >> ev >> (f ... >> loop | pass) >> merge)"
  , "## assemble a loop body from a quoted predicate and step"
  , "def whileFn = (p f -> [p ... >> ev >> (f ... >> ev >> again | done) >> merge])"
  , "## run step while predicate hits; exit with the miss payload"
  , "def while = whileFn ... >> loop"
  , "## assemble a loop body that exits on the predicate's hit"
  , "def untilFn = (p f -> [p ... >> ev >> (done | f ... >> ev >> again) >> merge])"
  , "## run step until predicate hits; exit with the hit payload"
  , "def until = untilFn ... >> loop"
    -- REFLECTED TYPES (2026-09-16).  The checker's own `Ty`, `SType`,
    -- `EffRow` and `Arrow`, and a `data`/`type`/`theory` declaration,
    -- as ordinary data.  They are declared here for the same reason
    -- `Atom` is: the prims name them, and a prim's scheme has to point
    -- at something.  The vocabulary below is the small library that
    -- makes a rep readable; `cellsFor` is the first DERIVING customer
    -- (MANUAL §12, examples/typerep.braid).
  , "## a WIDTH, as data: a literal, or a variable at an offset (`n+1` is what `weaken` leaves).  A width is its own SORT -- `A\8319` is a stack SEGMENT repeated n times and `Fin(n)` is an index into one -- so it has its own rep and cannot stand where a type stands."
  , "data WidthRep = (Int | Sym Int)"
  , "## a reflected TYPE: the checker's Ty, SType, EffRow and Arrow as data.  Nine alternatives -- a base type by name; a type VARIABLE by name; a declared type at its argument STACKS; Fn around an arrow; a sum (its alternatives, and the row tail, `.\8226` when closed); a stack's OPEN END; an ARROW (in, out, the grade's labels, the effect tail); a repeated closed SEGMENT and its width (`A\8319`); and `Fin` at a width.  `tail` and `rep` are not wires: each stands in a stack and nowhere else, and `rep` stands for however many wires its width says.  Equality is `eq?` on reps the reflection words BUILT -- they normalize first, widths included (MANUAL 12); a rep assembled by hand compares variable names."
  , "data TypeRep = (Sym | Sym | Sym List(List(TypeRep)) | TypeRep | List(List(TypeRep)) Sym | Sym | List(TypeRep) List(TypeRep) List(Sym) Sym | List(TypeRep) WidthRep | WidthRep)"
  , "## a stack of wires as a type rep: front wire first, an open end last"
  , "type StackRep = List(TypeRep)"
  , "## a reflected DECLARATION: a `data` (name, parameters, body, FIELD NAMES), a `type` (name, parameters, body) or a `theory` (name, parameters, slots, law names).  A parameter is (name, kind, arity): the kind is .wire .stack .row .width or .con, and the arity counts a constructor's underscores."
  , "data Decl = (Sym List(Box(Sym Sym Int)) TypeRep List(Sym) | Sym List(Box(Sym Sym Int)) TypeRep | Sym List(Box(Sym Sym Int)) List(Box(Sym TypeRep)) List(Sym))"
  , "## the name of a BASE type rep (.Int .Float .Str .Sym), or .none"
  , "def baseOf = [(s -> s)] [(s -> .none)] [(n as -> .none)] [(a -> .none)] [(as t -> .none)] [(s -> .none)] [(i o ls t -> .none)] [(b w -> .none)] [(w -> .none)] ... >> foldTypeRep"
  , "## is this rep a WIRE, rather than a stack's open end or a repeated segment?"
  , "def wire? = [(s -> true)] [(s -> true)] [(n as -> true)] [(a -> true)] [(as t -> true)] [(s -> false)] [(i o ls t -> true)] [(b w -> false)] [(w -> true)] ... >> foldTypeRep"
  , "## the closed width of a stack rep: its wires, an open end and a repeated segment not counted (neither is a KNOWN number of wires)"
  , "def stackWidth = [(n x -> (x >> wire?) (n 1 >> +) n >> select)] 0 ... >> fold"
  , "## the WIDTH a rep carries, or .none: a repeated segment's and a Fin's are the same sort"
  , "def widthOf = [(s -> nil)] [(s -> nil)] [(n as -> nil)] [(a -> nil)] [(as t -> nil)] [(s -> nil)] [(i o ls t -> nil)] [(b w -> w >> single)] [(w -> w >> single)] ... >> foldTypeRep"
  , "## the FIRST alternative of a type rep, as a stack -- nil unless it is a sum"
  , "def firstAlt = [(s -> nil)] [(s -> nil)] [(n as -> nil)] [(a -> nil)] [(as t -> as >> unList >> (nil | (x r -> x)) >> merge)] [(s -> nil)] [(i o ls t -> nil)] [(b w -> nil)] [(w -> nil)] ... >> foldTypeRep"
  , "## does this rep stand for Str?"
  , "def strRep? = (t -> (t >> baseOf >> symStr) \"Str\" >> equals)"
  , "## one column of a row printer, as SOURCE: `(r ; name)`, with `; toStr` unless the field is already a Str"
  , "def cellSrc = (e -> e >> unBox >> (f t -> (\"(r ; \" (f >> symStr) >> cat) ((t >> strRep?) \")\" \" ; toStr)\" >> select) >> cat))"
  , "## the printer, as Code: the source it is, parsed -- nil if it will not"
  , "def cellsCode = (s -> ((\"(r -> \" s >> cat) \"; pack)\" >> cat) >> parse >> ((c -> c) | drop >> nil) >> merge)"
  , "## DERIVE a row printer from a declaration: `Decl => Code`, the Code of `(r -> (r ; f1) (r ; f2 ; toStr) ... ; pack)` for a `data` with named fields.  nil for a `type`, a `theory`, or a `data` that named none -- there are no columns to print.  The first deriving customer of reflected declarations (MANUAL 12)."
  , "## one step of the derivation: the source so far and the types left over, one field at a time.  Written as a fold over the FIELD NAMES carrying the remaining types rather than as `zip`, because the prelude's `zip` ties a knot and a derived printer must stay PURE -- an `=Recursive>` printer no longer fits `embed`'s `Fn\10216a \8658 b\10217` (examples/frame.braid)."
  , "def cellStep = (acc f -> acc >> unBox >> (src ts -> ts >> unList >> ((src nil >> Box) | (t r -> ((src ((f t >> Box) >> cellSrc) >> cat) \" \" >> cat) r >> Box)) >> merge))"
  , "def cellsFor = (d -> d >> unDecl >> ((n ps body fs -> (fs >> [cellStep] (\"\" (body >> firstAlt) >> Box) ... >> fold >> unBox >> (src rest -> src)) >> cellsCode) | (n ps body -> nil) | (n ps sl ls -> nil)) >> mergeDecl)"
    -- THE DOCTRINE, declared.  Every module sees it, because a theory
    -- that says `in Doctrine` is claiming membership in THIS one and
    -- a claim needs something to point at.  The two structure slots
    -- are the base's own structure — Hughes' `arr`/`>>>`, Atkey's
    -- categorical model of arrows — and the laws below are the category
    -- laws, written once here instead of once per theory.
    --
    -- The HOM-OBJECT RANGES OVER STACKS (2026-09-16): `k(..., ...)`,
    -- and `compose : k(a, b) k(b, c) => k(a, c)` names six stacks, not
    -- six wires.  That is what deleted `first` and the pairing
    -- parameter `p` from this theory: a stage of any width embeds as
    -- itself, so the strength a one-wire hom-object needed is the
    -- BASE'S OWN `...` and needs no slot.  `embedWide` is the law that
    -- says so — the old `firstFst`/`firstEmbed`/`firstCompose` restated
    -- where the whiskering now happens, inside the quotation.
    --
    -- `observe` and `sample` are the AUDIT'S EVIDENCE, and they are
    -- slots like the rest: a carrier is often codata, so it cannot be
    -- compared, only observed.  A theory extending the doctrine
    -- declares as many of the four as it has; the laws that name only
    -- declared slots are the ones its models are audited against, and a
    -- sealed category — one that declares no way out — is honestly
    -- unaudited.
  , "## the arrow doctrine: a category whose hom-objects range over STACKS, and the embedding of the base.  `theory T(k(..., ...)) in Doctrine` declares membership; `with M` of a model of T transports."
  , "theory Doctrine(k(..., ...)) ="
  , "    compose : k(a, b) k(b, c) \8658 k(a, c)"
  , "    embed   : Fn\10216a \8658 b\10217 \8658 k(a, b)"
  , "    observe : k(Int, Int) \8658 Int"
  , "    sample  : \8226 \8658 k(Int, Int)"
  , "    law leftId = ([_] ... >> embed ... >> _ sample >> compose >> observe) (sample >> observe) >> eq? >> (forget >> true | forget >> false) >> merge"
  , "    law rightId = (sample >> _ [_] >> _ embed >> compose >> observe) (sample >> observe) >> eq? >> (forget >> true | forget >> false) >> merge"
  , "    law assoc = (sample sample sample >> compose _ >> compose >> observe) (sample sample sample >> _ compose >> compose >> observe) >> eq? >> (forget >> true | forget >> false) >> merge"
  , "    law embedFunctor = ([_ 1 >> + >> _ 2 >> *] ... >> embed ... >> observe) ([_ 1 >> +] ... >> embed ... >> _ [_ 2 >> *] >> _ embed >> compose >> observe) >> eq? >> (forget >> true | forget >> false) >> merge"
  , "    law embedWide = ([dup] ... >> embed ... >> _ [(_ 1 >> +) _] >> _ embed >> compose >> _ [*] >> _ embed >> compose >> observe) ([dup >> (_ 1 >> +) _ >> *] ... >> embed ... >> observe) >> eq? >> (forget >> true | forget >> false) >> merge"
  ]

-- `##` docs for PRIMS.  Prims are not defs, so they have no `##` line to
-- carry one; the table rides into the prelude's doc map so `:doc` finds
-- them by the same lookup.  Only words whose name alone does not say
-- what they are need an entry.
primDocs :: Map String String
primDocs = M.fromList
  [ ("into", unlines
      [ "the OPEN coproduct eliminator: peel the FIRST alternative off a"
      , "sum and leave the rest standing.  `into : Fn⟨ρ0 ⇒ (σ0)⟩"
      , "(ρ0 | σ0) ⇒ (σ0)` — the copairing `[h, id]`, where `h` maps the"
      , "handled alternative into the REMAINING row and every other tag"
      , "shifts down one.  Not derivable: over a residual you cannot write"
      , "a handler for a track you cannot name, so `[h, id]` is the only"
      , "copairing there is, and collapsing `(h | ---)`'s `((σ0) | σ0)`"
      , "positionally is exactly the tag shift."
      , "Peel, then close the ladder with `otherwise`:"
      , "  s >> [h1 >> alt1] into >> [h2 >> alt1] into >> [d] otherwise"
      , "Each `into` handles one track and shortens the row by one; the"
      , "closed eliminators (`case2`, `merge`, `otherwise`) finish the job"
      , "once the row is closed.  `>=>` is `[q, alt2]` — a CLOSED"
      , "copairing, not an instance of this." ])
  , ("showStack", unlines
      [ "a RENDERER for a whole stack: `showStack : ρ0 ⇒ Str`, the"
      , "wires deepest-first, space separated, each one rendered exactly"
      , "as `toStr` renders it and as the REPL's `:s` prints it — one"
      , "convention, said once."
      , "It CONSUMES the segment and is open-tailed, so it takes the"
      , "whole segment as the FINAL atom of its stage and is closed to"
      , "the empty one anywhere else — `forget`'s convention exactly."
      , "To render part of a stack,"
      , "close the arity with a binder — `dup >> (b -> b >> unBox >>"
      , "showStack)` logs the contents of a box and leaves the box"
      , "standing."
      , "It is a RENDERER, NOT A CLASS: there is no way to hook a"
      , "user-defined rendering into it, and `toStr` is the per-wire"
      , "word with the same property.  A `Show` doctrine, if there is"
      , "ever one, is a theory with a model per type and not this." ])
  , ("ev", unlines
      [ "the exponential's COUNIT: evaluation.  `ev` is the only way to"
      , "consume an `Fn`, and it is not derivable — naming a value never"
      , "runs it, so `(x f -> [x >> f])` does not typecheck.  Paired with"
      , "`curry`, the other half of the adjunction: `curry` makes an Fn"
      , "out of a program that wanted one more wire, `ev` takes it back."
      , "Spelled `apply` before 2026-09-12, renamed so the exponential's"
      , "two maps carry matching names."
      , "The Fn sits BELOW its arguments, and the grade rides inside it:"
      , "`[print] : • ⇒ Fn⟨a =IO> •⟩`, and `ev` is where the io comes"
      , "back out, so one `ev` serves pure and effectful quotes alike." ])
  ]

preludeModule :: Module
preludeModule =
  case checkModuleWith (moduleBase primEnv M.empty [] [] []) preludeSrc of
    Left err -> error ("prelude failed to check: " ++ err)
    Right m  -> m { modDocs = modDocs m `M.union` primDocs }

preludeNames :: [String]
preludeNames = [ n | (n, _, _) <- modDefs preludeModule ]

-- The prelude words abstraction elimination writes INTO reflected code
-- (stage 5a¾): one `capture` per parameter a quotation closed over, one
-- `dist2` per parameter a row's tracks need.  They are ordinary defs and
-- re-splice like any other name — which is exactly why shadowing one
-- would be capture, the hygiene invariant's one loophole.  So they are
-- the two prelude names a module may not redefine.
elimEmits :: [String]
elimEmits = ["capture", "dist2"]

-- Names a user definition is allowed to shadow: every prelude def, plus
-- the structural recursors the prelude's own data declarations generate
-- (foldList and friends were ordinary prelude defs until 5a½, and
-- shadowing one has to keep working).
preludeShadowNames :: [String]
preludeShadowNames =
  preludeNames
    ++ [ fn | d <- modDatas preludeModule
            , Just (fn, _, _, _) <- [dataFoldArtifact d] ]

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

--------------------------------------------------------------------------------
-- 12.9 Deciding program equality on the structural fragment
--
-- A program built from wiring (`id`/`_`/`dup`/`drop`/`swap`/`pass`),
-- composition and juxtaposition, over words treated as UNINTERPRETED, is
-- a morphism of the free cartesian category on those words.  That
-- category's word problem is solvable, and the decision procedure is the
-- obvious one: run the program on distinct symbolic inputs and read off
-- the tuple of terms it returns.  Two programs are equal exactly when
-- they consume the same number of wires and return the same tuple.
--
-- This is a PROOF for all inputs, not a test at chosen ones — which is
-- what makes it worth having beside the sampled laws.  What it decides
-- is exactly the laws that hold for every interpretation of the words
-- involved: the naturality of copy and discard, functoriality of `first`,
-- interchange, and every rearrangement of wires.  A law needing `+` to
-- be commutative is NOT in this fragment: `+` is uninterpreted here, and
-- the fragment is honest about the difference.
--------------------------------------------------------------------------------

-- A symbolic value.  `SVar` is an input wire and `SBnd` a bundle wire
-- invented by a case split; `SApp` is the j-th output of an
-- uninterpreted word; `SInj` an injection whose tag is KNOWN, carrying
-- its bundle; `SQuo` a quotation, carrying the arguments captured into
-- it (deepest first) and the body it will run on them.
data SymV
  = SVar !Int
  | SBnd !Int
  | SApp String [SymV] !Int
  | SInj !Int [SymV]
  | SQuo [SymV] Term
  deriving (Eq, Ord)

-- The working state: a tick budget (a bound, not a proof), the
-- fresh-input counter, and the stack (deepest wire first).
data NState = NState
  { nsFuel  :: !Int
  , nsFresh :: !Int
  , nsStack :: [SymV]
  }

-- Either the program left the fragment, or an eliminator met a sum
-- whose injection is unknown and the tree has to branch.  A split
-- carries the scrutinee and the row's track stacks, which is what
-- fixes how many wires each branch's bundle has.
data NErr = NOut String | NSplit SymV [SType]

-- The shared half of a decision: the typing environment, the defs to
-- inline for a QUOTE body (the union of both sides'), the refinement
-- built by the splits taken so far, the wire types a split reads its
-- widths from, and the next free bundle-wire id.
data NCtx = NCtx
  { ncEnv   :: Env
  , ncDefs  :: RunDefs
  , ncRef   :: Map SymV SymV
  , ncTypes :: Map SymV Ty
  , ncNext  :: !Int
  }

-- One side of a decision: the term, the defs IT resolves names against,
-- and the pre-seeded input stack (plus the counter that continues it).
data NProg = NProg
  { npTerm  :: Term
  , npDefs  :: RunDefs
  , npSeed  :: [SymV]
  , npFresh :: !Int
  }

-- Bounds.  Both are reported as "outside the structural fragment",
-- never as a verdict: running out of room is not an answer.
normFuel :: Int
normFuel = 40000

normDepthCap :: Int
normDepthCap = 16

-- Count the wires of a CLOSED stack type; an open tail has no width.
closedWidth :: SType -> Maybe Int
closedWidth SEnd        = Just 0
closedWidth (SCons _ r) = (1 +) <$> closedWidth r
closedWidth _           = Nothing

-- The wires of a stack type, deepest first (an open tail contributes
-- nothing, which is why every caller pairs this with `closedWidth`).
stackWires :: SType -> [Ty]
stackWires (SCons t r) = t : stackWires r
stackWires _           = []

stackWireAt :: Int -> SType -> Maybe Ty
stackWireAt 0 (SCons t _) = Just t
stackWireAt k (SCons _ r) = stackWireAt (k - 1) r
stackWireAt _ _           = Nothing

-- Pull n wires off the front, inventing fresh inputs when the stack is
-- short: a program is normalized as a morphism on however many wires it
-- turns out to need.
takeSym :: Int -> NState -> ([SymV], NState)
takeSym 0 s = ([], s)
takeSym n s = case nsStack s of
  x : st -> let (xs, s') = takeSym (n - 1) s { nsStack = st } in (x : xs, s')
  []     -> let v = SVar (nsFresh s)
                (xs, s') = takeSym (n - 1) s { nsFresh = nsFresh s + 1 }
            in (v : xs, s')

-- Apply the refinement a case split built.  Keys are values that were
-- unresolvable when the split was taken and images are fresh
-- injections, so this cannot cycle; the depth bound is belt and braces.
resolveSym :: Map SymV SymV -> SymV -> SymV
resolveSym r = go (64 :: Int)
  where
    go 0 v = v
    go d v = case M.lookup v r of
      Just u  -> go (d - 1) u
      Nothing ->
        let v' = case v of
                   SApp n as j -> SApp n (map (go (d - 1)) as) j
                   SInj t bs   -> SInj t (map (go (d - 1)) bs)
                   SQuo cs b   -> SQuo (map (go (d - 1)) cs) b
                   _           -> v
        in if v' == v then v else go (d - 1) v'

-- The type of a symbolic value, where the program said one: an input
-- wire carries the type the seed gave it, and the j-th output of an
-- uninterpreted word carries the one its scheme declares.
symTy :: NCtx -> SymV -> Maybe Ty
symTy ctx v = unwrap (8 :: Int) =<< own
  where
    own = case v of
      -- a neutral `ev` is typed by the FUNCTION it applied, not by
      -- `ev`'s own scheme (whose output is an open stack)
      SApp "ev" (f : _) j
        | Just (TFn (Arrow _ o _)) <- symTy ctx f -> stackWireAt j o
      SApp n _ j
        | Just (Forall _ _ _ _ _ _ (Arrow _ o _)) <- M.lookup n (ncEnv ctx)
        , Just t <- stackWireAt j o -> Just t
      _ -> M.lookup v (ncTypes ctx)
    -- A single-wire nominal type is its body to the normalizer: the
    -- unroller is the identity and has already been inlined away, so
    -- the wire that is TYPED `Arr(a, b)` IS the `Fn⟨a ⇒ b⟩` inside it.
    -- The scheme of `unName` is where the body still is.
    unwrap 0 t = Just t
    unwrap d t@(TData n _)
      | Just (Forall _ _ _ _ _ _ (Arrow _ o _)) <- M.lookup ("un" ++ n)
                                                            (ncEnv ctx)
      , Just [u] <- closedWires o = unwrap (d - 1) u
      | otherwise = Just t
    unwrap _ t = Just t

-- The track stacks of a sum-typed value, when the type says so and
-- every track is closed.  `Nothing` is a refusal, never a guess: an
-- open row tail (`---`, a row variable σ) has tracks with no names and
-- therefore no widths, and there is no partition to split on.
sumTracks :: NCtx -> SymV -> Maybe [SType]
sumTracks ctx v = case v of
  SApp n _ j
    | Just (Forall _ _ _ _ _ _ (Arrow _ o _)) <- M.lookup n (ncEnv ctx)
    , Just t <- stackWireAt j o -> fromTy t
  _ -> M.lookup v (ncTypes ctx) >>= fromTy
  where
    fromTy (TSum row) = do
      sts <- closedRow row
      _   <- mapM closedWidth sts
      Just sts
    -- a declared nominal type is its body up to the `unName` wrapper,
    -- which the normalizer has already inlined away (it is the
    -- identity); the scheme of `unName` is where the row still is
    fromTy (TData n _) = do
      Forall _ _ _ _ _ _ (Arrow _ o _) <- M.lookup ("un" ++ n) (ncEnv ctx)
      t <- stackWireAt 0 o
      case t of
        TSum row -> fromTy (TSum row)
        -- a SINGLE-ALTERNATIVE declaration (`data Pair(a, b) = a b`):
        -- the unroller hands back the payload stack, so there is one
        -- track and it is that stack.  The "split" is then a partition
        -- into one branch, which is how `unPair` of a wire gets its
        -- two wires.
        _ | Just _ <- closedWidth o, Just _ <- closedWidth o -> Just [o]
        _ -> Nothing
    fromTy _ = Nothing
    closedRow RNil        = Just []
    closedRow (RTail _)   = Nothing
    closedRow (RCons s r) = (s :) <$> closedRow r

-- Does this term still carry a binder?  Abstraction elimination is not
-- free (it re-infers), so it is run only where it can do something.
hasOpenAbs :: Term -> Bool
hasOpenAbs (OpenAbs {}) = True
hasOpenAbs (Seq _ a b)  = hasOpenAbs a || hasOpenAbs b
hasOpenAbs (Tensor ts)  = any hasOpenAbs ts
hasOpenAbs (Quote t)    = hasOpenAbs t
hasOpenAbs (Alts cs _)  = any hasOpenAbs cs
hasOpenAbs (With _ _ b) = hasOpenAbs b
hasOpenAbs (In _ b)     = hasOpenAbs b
hasOpenAbs _            = False

normTerm :: NCtx -> RunDefs -> [String] -> Term -> NState -> Either NErr NState
normTerm ctx defs seen term s0 = case term of
  Seq _ a b -> normTerm ctx defs seen a s0 >>= normTerm ctx defs seen b
  Tensor ts -> goAtoms ts s0
  With _ _ _ -> outside "an unelaborated `with`"
  In _ _    -> outside "an unelaborated `in`"
  t         -> goAtoms [t] s0
  where
    env = ncEnv ctx
    outside what = Left (NOut ("outside the structural fragment: " ++ what))

    -- mirrors evalTerm's goAtoms: each atom's outputs accumulate, the
    -- leftover stack flows through the last one
    goAtoms [] s = Right s
    goAtoms (a : more) s
      | nsFuel s <= 0 = outside "the normalizer ran out of steps"
      | otherwise = do
          (out, s1) <- atom (null more) a s { nsFuel = nsFuel s - 1 }
          s2 <- goAtoms more s1
          Right s2 { nsStack = out ++ nsStack s2 }

    -- the refinement the splits so far have built
    scrut v = resolveSym (ncRef ctx) v

    splitOn v = case sumTracks ctx v of
      Just tracks -> Left (NSplit v tracks)
      Nothing     -> outside "a sum whose injection is unknown and whose \
                             \row has no closed tracks"

    wire k f s = let (args, s') = takeSym k s in (f args, s')
    -- takeSym always returns exactly what it was asked for; the second
    -- alternative is there so the match is total, not because it happens.
    one s = let (xs, s') = takeSym 1 s
            in (case xs of { x : _ -> x ; [] -> SVar (nsFresh s') }, s')
    two s = let (xs, s') = takeSym 2 s
            in case xs of
                 x : y : _ -> (x, y, s')
                 _         -> (SVar (nsFresh s'), SVar (nsFresh s'), s')

    -- a quotation is a VALUE: the body, with nothing captured yet
    atom _ (Quote b) s = Right ([SQuo [] b], s)

    -- A code row eliminates one sum wire.  Under a known injection it
    -- is β for the coproduct: follow the tag, run that track, re-tag.
    -- Under an unknown one the tree branches.
    atom _ (Alts comps residual) s =
      let (v, s1) = one s in case scrut v of
        SInj t bundle
          | t < length comps -> do
              s2 <- normTerm ctx defs seen (comps !! t) s1 { nsStack = bundle }
              Right ([SInj t (nsStack s2)], s2 { nsStack = nsStack s1 })
          | residual  -> Right ([SInj t bundle], s1)
          | otherwise -> outside "a row applied to a tag it has no track for"
        u -> splitOn u

    atom isFinal (Prim n) s
      | n == "id" || n == "_" = Right (wire 1 (\ws -> ws)          s)
      | n == "dup"            = Right (wire 1 (\ws -> ws ++ ws)    s)
      | n == "drop"           = Right (wire 1 (const [])           s)
      | n == "swap"           = Right (wire 2 reverse              s)
      -- `pass` is the open remainder: everything as the final atom, and
      -- closed to nothing by the typechecker anywhere else
      | n == "pass" || isJust (receiptLabel n) =
          Right (if isFinal then (nsStack s, s { nsStack = [] }) else ([], s))
      -- (a RECEIPT is `pass` with a label — it moves no wire, so the
      -- normalizer erases it exactly as it erases `pass`.  Without this
      -- no law could be stated about a program written under any `with`
      -- scope, transported scopes included: `with@F` has no closed arity.)
      -- the injections are open-arity in the same way: the whole
      -- remaining segment is the bundle when they end the stage
      | Just k <- injIndex n =
          Right (if isFinal
                   then ([SInj (k - 1) (nsStack s)], s { nsStack = [] })
                   else ([SInj (k - 1) []], s))
      -- the codiagonal: under a known injection, hand back the bundle
      | n == "merge", not (M.member n defs) =
          let (v, s1) = one s in case scrut v of
            SInj _ bundle -> Right (bundle, s1)
            u             -> splitOn u
      -- `into` is the copairing [h, id]: tag 0 runs the handler on its
      -- own bundle, every other tag shifts down one
      | n == "into", not (M.member n defs) =
          let (h, sm, s1) = two s in case scrut sm of
            SInj 0 bundle -> case scrut h of
              SQuo caps body -> do
                s2 <- normTerm ctx defs seen body s1 { nsStack = caps ++ bundle }
                case nsStack s2 of
                  [r] -> Right ([r], s2 { nsStack = nsStack s1 })
                  _   -> outside "`into`'s handler did not land in one wire"
              _ -> outside "`into` of a value that is not a literal quotation"
            SInj t bundle -> Right ([SInj (t - 1) bundle], s1)
            u             -> splitOn u
      -- β for the exponential: `[p] >> ev = p`, and since `capture`
      -- builds the quotation by pushing onto its captures, `capture ;
      -- ev` IS substitution — the body runs on captures ++ segment
      | n == "ev", not (M.member n defs) =
          let (v, s1) = one s in case scrut v of
            SQuo caps body -> do
              let seg = if isFinal then nsStack s1 else []
              s2 <- normTerm ctx defs seen body s1 { nsStack = caps ++ seg }
              Right ( nsStack s2
                    , s2 { nsStack = if isFinal then [] else nsStack s1 } )
            -- `ev` of a WIRE.  There is no β to do — the function is
            -- not a quotation we hold — but if its type is a CLOSED
            -- arrow the typechecker has already said how many wires it
            -- eats and leaves, so it is a neutral application like any
            -- other uninterpreted word: standard NbE's neutral case,
            -- and the widths come from a written type.  Only an OPEN
            -- stack (a `fix` body's self wire, a handler slot) is left
            -- outside, and now that is the whole of what is left.
            u | Just (TFn (Arrow i o _)) <- symTy ctx u
              , Just k <- closedWidth i
              , Just m <- closedWidth o ->
                  let (args, s2) = takeSym k s1
                  in Right ([SApp "ev" (u : args) j | j <- [0 .. m - 1]], s2)
            _ -> outside "`ev` of a value whose arrow is not closed \
                         \(there is no arity to give it)"
      -- the 1-ary re-tag: on an injection we know, shift the tag; on one
      -- we do not, `there` stays an uninterpreted word (its row is a
      -- bare tail, so there is nothing to split on)
      | n == "there", not (M.member n defs) =
          let (x, s1) = one s in case scrut x of
            SInj t b -> Right ([SInj (t + 1) b], s1)
            u        -> Right ([SApp "there" [u] 0], s1)
      -- `capture` and `dist2` are interpreted rather than inlined:
      -- their own bodies go back through the words they define
      -- (`capture` through `curry`, `dist2` through `case2`, whose
      -- elimination emits `dist2`), so inlining them would stall on the
      -- `seen` list.  They are also the two prelude names a module may
      -- not shadow, which is what makes reading them by name sound.
      | n == "capture" =
          let (x, f, s1) = two s in case scrut f of
            SQuo caps body -> Right ([SQuo (caps ++ [x]) body], s1)
            -- capture of a function that arrived as a WIRE is partial
            -- application, and partial application is the quotation
            -- that applies it: `capture x into f` = `[f x … ; ev]`.
            -- Whether THAT can be run is the `ev`-of-a-wire question,
            -- asked where it belongs rather than here.
            u -> Right ([SQuo [u, x] (Prim "ev")], s1)
      | n == "dist2" || isJust (distPrimArity n) =
          let k = fromMaybe 2 (distPrimArity n)
              (x, sm, s1) = two s
          in case scrut sm of
               SInj t bundle
                 | t < k     -> Right ([SInj t (x : bundle)], s1)
                 | otherwise -> Right ([SInj t bundle], s1)
               u -> splitOn u
      -- a def in the fragment is INLINED, which decides strictly more;
      -- one already being expanded is recursive, so treat it as opaque.
      -- Binders in the body are eliminated first — the same path
      -- `reflect` takes — so a def is no less decidable than its Code.
      --
      -- ...except a KNOT (a def written under `with Recursive`, whose
      -- spine ends in `ev` of `#fix`).  Inlining one always lands on
      -- `ev` of a wire whose arrow is the knot's — an open stack, no
      -- arity — so it can only turn a verdict into a refusal.  Held
      -- opaque it is an uninterpreted word of closed arity, which is
      -- what the prim `fix` was until 2026-09-14 and what makes
      -- `F(fix b) = fix (F b)` decide by congruence.
      | Just de <- M.lookup n defs, not (deOpen de), n `notElem` seen
      , not (isRecursorEntry de), not (isKnotEntry de)
      , Right body <- (if hasOpenAbs (deBody de)
                         then elimAbsTerm env (deBody de)
                         else Right (deBody de)) =
          let (args, s1) = takeSym (deArity de) s
          in do s2 <- normTerm ctx defs (n : seen) body s1 { nsStack = args }
                Right (nsStack s2, s2 { nsStack = nsStack s1 })
      -- literals are nullary constants, and distinct literals are
      -- distinct constants (that is what makes `[1 ...]` and `[2 ...]`
      -- decidably different rather than merely untested)
      | isIntLiteral n || isFloatLiteral n || isStrLiteral n || isSymLiteral n =
          Right ([SApp n [] 0], s)
      -- any other word is uninterpreted: it needs a closed arity so we
      -- know how many wires it eats and how many it returns
      | Just (Forall _ _ _ _ _ _ (Arrow i o _)) <- M.lookup n env
      , Just k <- closedWidth i
      , Just m <- closedWidth o =
          let (args, s') = takeSym k s
          in Right ([SApp n args j | j <- [0 .. m - 1]], s')
      | otherwise = outside ("`" ++ n ++ "` has no closed arity")
    -- A grouped compound operand (a Seq/Tensor standing as one atom),
    -- exactly as evalTerm treats it: final, it runs on the whole
    -- remaining stack; non-final, it was typed closed, so take its
    -- arity.
    atom isFinal t s
      | isFinal = do
          s2 <- normTerm ctx defs seen t s
          Right (nsStack s2, s2 { nsStack = [] })
      | otherwise = case inferTermIn env t of
          Right (Arrow i _ _) ->
            let (args, s1) = takeSym (closedArity i) s
            in do s2 <- normTerm ctx defs seen t s1 { nsStack = args }
                  Right (nsStack s2, s2 { nsStack = nsStack s1 })
          Left e -> outside ("a grouped program whose arity is unknown: "
                             ++ e)

    -- a structural recursor has no body to inline; it has a closed
    -- scheme, so it decides as an uninterpreted word instead
    isRecursorEntry de = case deBody de of
      Prim p -> isJust (foldPrimSpec p)
      _      -> False

    -- a def that ties its own knot: the same treatment, for the same
    -- reason — its closed scheme decides more than its body would
    isKnotEntry de = knotPrimName `elem` primsIn (deBody de)

-- The pre-seeded input for ONE comparison.  Lazy invention alone is
-- enough to get equality right when both sides are inferred alike, but
-- a sum arriving as an input wire needs a TYPE before it can be split
-- on, and that comes from the program's own arrow.  The two sides are
-- inferred INDEPENDENTLY (the unification the call site did is gone by
-- now), so one can come out closed and the other open; both are
-- therefore seeded with the SAME number of wires, the larger of what
-- they ask for.  Seeding both with extra wires is whiskering by an
-- identity, which preserves equality in both directions.
-- `seedPair`, with the two sides' capture lists kept apart: the shared
-- fresh segment is what a quotation is APPLIED to, and the captures are
-- already-supplied arguments that each side holds its own of.
seedSeg :: Env -> [SymV] -> [SymV] -> Int -> Term -> Term
        -> ([SymV], Int, Map SymV Ty)
seedSeg env c1 c2 base b1 b2 = (ws, base + k, tys)
  where
    inp t = case inferTermIn env t of
      Right (Arrow i _ _) | isJust (closedWidth i) -> Just i
      _                                            -> Nothing
    i1  = inp b1
    i2  = inp b2
    own c i = drop (length c) (stackWires i)
    k   = max (maybe 0 (length . own c1) i1) (maybe 0 (length . own c2) i2)
    ws  = [ SVar (base + j) | j <- [0 .. k - 1] ]
    tys = mergeTypes env (capTys c1 i1) (capTys c2 i2)
    capTys c (Just i) = M.fromList (zip c (stackWires i))
                          `M.union` M.fromList (zip ws (own c i))
    capTys _ Nothing  = M.empty

seedPair :: Env -> [SymV] -> Int -> Term -> Term -> ([SymV], Int, Map SymV Ty)
seedPair env caps base b1 b2 =
  ( caps ++ ws, base + k, mergeTypes env (tysFor i1) (tysFor i2) )
  where
    c   = length caps
    inp t = case inferTermIn env t of
      Right (Arrow i _ _) | isJust (closedWidth i) -> Just i
      _                                            -> Nothing
    own i = drop c (stackWires i)
    i1  = inp b1
    i2  = inp b2
    k   = max (maybe 0 (length . own) i1) (maybe 0 (length . own) i2)
    ws  = [ SVar (base + j) | j <- [0 .. k - 1] ]
    tysFor Nothing  = M.empty
    tysFor (Just i) = M.fromList (zip caps (stackWires i))
                        `M.union` M.fromList (zip ws (own i))

-- Two type maps merged; a wire the two sides disagree about is marked
-- with a type nothing can read a row off, so a split is refused there
-- rather than taken on one side's say-so.
--
-- "Disagree" is up to the NAMES of type variables, which is the whole
-- point: the two sides are inferred independently, so the same wire
-- comes back as `Arr(a0, a1)` on one side and `Arr(a5, a6)` on the
-- other, and marking that a clash threw away every type in every
-- comparison of two programs that were not spelled identically.  Only
-- the SHAPE is ever read off these types — a row's track widths, an
-- `Fn`'s stack widths — and a type variable is one wire whatever it is
-- called.
mergeTypes :: Env -> Map SymV Ty -> Map SymV Ty -> Map SymV Ty
mergeTypes env = M.unionWith (\x y -> fromMaybe (TVarTy (TV "#clash"))
                                                (mergeTy env x y))

-- Structural merge of what the two sides say one wire is.  A type
-- VARIABLE is "not said": the other side's answer stands, which is
-- what makes a generic quotation comparable with the specialized one
-- it is being weighed against.  A real disagreement — `Int` against
-- `Str`, two different constructors, rows of different length — is
-- `Nothing`, and the caller marks the wire so no row can be read off
-- it and no split is taken on one side's say-so.
mergeTy :: Env -> Ty -> Ty -> Maybe Ty
mergeTy env a b = case (a, b) of
  (TVarTy _, t)                -> Just t
  (t, TVarTy _)                -> Just t
  (TFn (Arrow i1 o1 e), TFn (Arrow i2 o2 _)) ->
    TFn <$> (Arrow <$> mergeS env i1 i2 <*> mergeS env o1 o2 <*> pure e)
  (TSum r1, TSum r2)           -> TSum <$> mergeR env r1 r2
  (TData n1 as1, TData n2 as2)
    | n1 == n2, length as1 == length as2 ->
        TData n1 <$> sequence (zipWith (mergeS env) as1 as2)
  -- A single-wire nominal wrapper is its body here, because the
  -- normalizer has already erased the roll: one side saying
  -- `Plain(a, b)` and the other `Fn⟨a ⇒ b⟩` are saying one thing.
  (TData _ _, _) | Just a' <- unwrapTy env a -> mergeTy env a' b
  (_, TData _ _) | Just b' <- unwrapTy env b -> mergeTy env a b'
  _ | a == b   -> Just a
    | otherwise -> Nothing

unwrapTy :: Env -> Ty -> Maybe Ty
unwrapTy env (TData n _)
  | Just (Forall _ _ _ _ _ _ (Arrow _ o _)) <- M.lookup ("un" ++ n) env
  , Just [u] <- closedWires o = Just u
unwrapTy _ _ = Nothing

mergeS :: Env -> SType -> SType -> Maybe SType
mergeS env a b = case (a, b) of
  (SEnd, SEnd)               -> Just SEnd
  (STail _, t)               -> Just t
  (t, STail _)               -> Just t
  (SCons t1 r1, SCons t2 r2) -> SCons <$> mergeTy env t1 t2 <*> mergeS env r1 r2
  _ | a == b   -> Just a
    | otherwise -> Nothing

mergeR :: Env -> SumRow -> SumRow -> Maybe SumRow
mergeR env a b = case (a, b) of
  (RNil, RNil)               -> Just RNil
  (RTail _, t)               -> Just t
  (t, RTail _)               -> Just t
  (RCons s1 r1, RCons s2 r2) -> RCons <$> mergeS env s1 s2 <*> mergeR env r1 r2
  _ | a == b   -> Just a
    | otherwise -> Nothing

allOk :: (a -> Either String Bool) -> [a] -> Either String Bool
allOk _ []       = Right True
allOk f (x : xs) = do b <- f x
                      if b then allOk f xs else Right False

maxVarIn :: [SymV] -> Int
maxVarIn = foldr (\v m -> max m (go v)) (-1)
  where
    go (SVar i)      = i
    go (SApp _ as _) = maxVarIn as
    go (SInj _ bs)   = maxVarIn bs
    go (SQuo cs _)   = maxVarIn cs
    go _             = -1

-- Decide whether two programs are the same morphism.  They are
-- normalized JOINTLY under a shared refinement: a case split requested
-- by either side is taken by BOTH, which is what lets a program that
-- branches be compared with one that does not (`dist2 >> undist2` and
-- `id` at an arbitrary sum is the case that needs it).
sameProgram :: Env -> RunDefs -> RunDefs -> Term -> Term -> Either String Bool
sameProgram env d1 d2 t1 t2 = do
  u1 <- prep t1
  u2 <- prep t2
  let (seed, fr, tys) = seedPair env [] 0 u1 u2
      ctx = NCtx { ncEnv   = env
                 , ncDefs  = M.union d1 d2
                 , ncRef   = M.empty
                 , ncTypes = tys
                 , ncNext  = 0 }
  decideProgs 0 ctx (NProg u1 d1 seed fr) (NProg u2 d2 seed fr)
  where
    prep t
      | hasOpenAbs t =
          either (Left . ("outside the structural fragment: a binder \
                          \abstraction elimination refuses — " ++))
                 Right (elimAbsTerm env t)
      | otherwise = Right t

decideProgs :: Int -> NCtx -> NProg -> NProg -> Either String Bool
decideProgs depth ctx p q =
  case runProg ctx p of
    Left (NSplit u tracks) -> branchOn depth ctx p q u tracks
    Left (NOut m)          -> Left m
    Right n1 -> case runProg ctx q of
      Left (NSplit u tracks) -> branchOn depth ctx p q u tracks
      Left (NOut m)          -> Left m
      Right n2               -> eqLeaf depth ctx n1 n2

-- One side, run to a leaf: how many input wires it consumed, and the
-- tuple it returns with the refinement applied.
runProg :: NCtx -> NProg -> Either NErr (Int, [SymV])
runProg ctx p = do
  s <- normTerm ctx (npDefs p) []  (npTerm p)
         (NState normFuel (npFresh p) (npSeed p))
  Right (nsFresh s, map (resolveSym (ncRef ctx)) (nsStack s))

-- The case split.  Splitting a coproduct into its tracks is
-- extensivity (Carboni–Lack–Walters), so the branches are a partition
-- and the conjunction over them is the verdict.
branchOn :: Int -> NCtx -> NProg -> NProg -> SymV -> [SType]
         -> Either String Bool
branchOn depth ctx p q u tracks
  | depth >= normDepthCap =
      Left ("outside the structural fragment: the case tree grew past "
            ++ show normDepthCap ++ " splits")
  | otherwise = allOk branch (zip [0 ..] tracks)
  where
    branch (i, st) =
      let ws  = stackWires st
          bs  = [ SBnd (ncNext ctx + j) | j <- [0 .. length ws - 1] ]
          ctx' = ctx { ncRef   = M.insert u (SInj i bs) (ncRef ctx)
                     , ncTypes = M.union (M.fromList (zip bs ws)) (ncTypes ctx)
                     , ncNext  = ncNext ctx + length ws }
      in decideProgs (depth + 1) ctx' p q

eqLeaf :: Int -> NCtx -> (Int, [SymV]) -> (Int, [SymV]) -> Either String Bool
eqLeaf depth ctx (k1, o1) (k2, o2)
  | k1 /= k2 || length o1 /= length o2 = Right False
  | otherwise = allOk (eqSym depth ctx) (zip o1 o2)

-- Structural, except on quotations: a quote equals a quote when their
-- captures are equal and their bodies are the same morphism, decided by
-- the same procedure one level down.  The recursion terminates because
-- a body is a proper subterm of the term that carried it.
eqSym :: Int -> NCtx -> (SymV, SymV) -> Either String Bool
eqSym depth ctx (a, b) = case (a, b) of
  (SQuo c1 b1, SQuo c2 b2) -> do
    ok <- if length c1 == length c2
            then allOk (eqSym depth ctx) (zip c1 c2)
            else Right False
    if ok then sameQuo depth ctx c1 c2 b1 b2
      -- Captures that are not pairwise equal are not a verdict: two
      -- closures can hold different things and still be the same
      -- morphism (`[capture 1 … ; +]` against `[capture 0 … ; + ; _ 1
      -- ; +]`).  So run each body on ITS OWN captures plus a shared
      -- fresh segment, which is what equality of functions means.  A
      -- refusal there is a REFUSAL (2026-09-14): it used to fall back
      -- to `false`, which made `false` mean "could not decide" in this
      -- one corner and nothing could trust it.
      else sameQuo depth ctx c1 c2 b1 b2
  -- ETA for the exponential.  A quotation against a FUNCTION THAT
  -- ARRIVED AS A WIRE: `f = [f ... ; ev]` holds in any closed
  -- category, so apply the quote to fresh wires and compare with the
  -- neutral application.  Without this, every identity law of a
  -- category whose carrier wraps an `Fn` comes out `false` — the law
  -- says `embed [pass] ; f = f`, and the left side is a quotation
  -- while the right side is the wire itself.
  (SQuo c1 b1, u) | Just (si, so) <- evArity ctx u ->
    etaEq depth ctx c1 b1 u si so
  (u, SQuo c2 b2) | Just (si, so) <- evArity ctx u ->
    etaEq depth ctx c2 b2 u si so
  (SApp n1 as1 j1, SApp n2 as2 j2)
    | n1 == n2, j1 == j2, length as1 == length as2 ->
        allOk (eqSym depth ctx) (zip as1 as2)
  (SInj t1 x1, SInj t2 x2)
    | t1 == t2, length x1 == length x2 ->
        allOk (eqSym depth ctx) (zip x1 x2)
  _ -> Right (a == b)

-- Two quotations, each run on its own captures and a SHARED fresh
-- segment: the segment is seeded once, at the wider of the two sides'
-- own arities, because seeding both with extra wires is whiskering by
-- an identity.
sameQuo :: Int -> NCtx -> [SymV] -> [SymV] -> Term -> Term
        -> Either String Bool
sameQuo depth ctx c1 c2 b1 b2
  | depth >= normDepthCap =
      Left ("outside the structural fragment: quotations nested past "
            ++ show normDepthCap ++ " levels")
  | otherwise =
      let base = 1 + maxVarIn (c1 ++ c2)
          defs = ncDefs ctx
          (ws, fr, tys) = seedSeg (ncEnv ctx) c1 c2 base b1 b2
          -- the OUTER wire types are still true inside a quotation: a
          -- captured wire is the same wire, and dropping its type is
          -- what kept `ev` of a captured function undecided
          ctx' = ctx { ncRef = M.empty, ncTypes = M.union tys (ncTypes ctx) }
      in decideProgs (depth + 1) ctx'
           (NProg b1 defs (c1 ++ ws) fr) (NProg b2 defs (c2 ++ ws) fr)

-- the widths `ev` of this value may be given: a closed arrow, read off
-- the type the program wrote (through a single-wire nominal wrapper,
-- whose roll and unroll the normalizer has already erased)
evArity :: NCtx -> SymV -> Maybe (SType, SType)
evArity ctx u = case symTy ctx u of
  Just (TFn (Arrow i o _)) | isJust (closedWidth i), isJust (closedWidth o) ->
    Just (i, o)
  _ -> Nothing

-- One side of an eta comparison: run the quotation on fresh wires and
-- ask whether it lands exactly on `ev` of the neutral at those wires.
etaEq :: Int -> NCtx -> [SymV] -> Term -> SymV -> SType -> SType
      -> Either String Bool
etaEq depth ctx caps body u si so
  | depth >= normDepthCap =
      Left ("outside the structural fragment: quotations nested past "
            ++ show normDepthCap ++ " levels")
  | otherwise =
      let k    = length (stackWires si)
          m    = length (stackWires so)
          base = 1 + maxVarIn (u : caps)
          ws   = [ SVar (base + j) | j <- [0 .. k - 1] ]
          app  = [ SApp "ev" (u : ws) j | j <- [0 .. m - 1] ]
          -- the arguments are typed by the function's own input stack
          ctx1 = ctx { ncTypes = M.union (M.fromList (zip ws (stackWires si)))
                                         (ncTypes ctx) }
      in case runProg ctx1 (NProg body (ncDefs ctx) (caps ++ ws) (base + k)) of
           Left (NOut msg)   -> Left msg
           Left (NSplit _ _) -> Left "outside the structural fragment: a \
                                     \case split under an eta comparison"
           Right (fresh, out)
             | fresh /= base + k        -> Right False   -- other arity
             | length out /= m          -> Right False
             | otherwise -> allOk (eqSym (depth + 1) ctx1) (zip out app)

data Value
  = VInt Int
  | VFloat Double
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
  -- STRUCTURAL, which at Float means IEEE `==`: `eq?` on two Floats is
  -- bit equality of the two doubles up to the one identification IEEE
  -- makes (0.0 and -0.0) and the one it refuses (NaN is equal to
  -- nothing, itself included).  It is not an epsilon comparison and
  -- never will be: `(0.1 0.2 ; fadd) 0.3 ; eq?` is false, and that is
  -- the truth about the two doubles.
  VFloat a   == VFloat b   = a == b
  VStr a     == VStr b     = a == b
  VSym a     == VSym b     = a == b
  VFn _ va a == VFn _ vb b = va == vb && a == b
  VSum i vs  == VSum j ws  = i == j && vs == ws
  _          == _          = False

-- Cons-shaped sum spines (alt2(x, alt2(y, … alt1()))) display as
-- list(x, y, …); a bare alt1() stays alt1().
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
  show (VFloat d)    = showFloatLit d
  show (VStr t)      = t
  show (VSym t)      = t
  show (VFn _ _ _)   = "[fn]"
  show (VSum i vs)   =
    "alt" ++ show (i + 1) ++ "(" ++ intercalate ", " (map show vs) ++ ")"

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
          ++ show (length out) ++ " were produced.  Splices now check "
          ++ "their own result against the type the context expected, so "
          ++ "this is a LAST-RESORT backstop rather than the evalCode "
          ++ "arity gap it was written for (see design-metaprogramming.md)."
    _ -> Nothing

-- A runtime definition: closed input arity, whether the input has an
-- open tail (segment-consuming as a final atom, like ev/loop), the
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
    -- binder values the entry closed over.  Empty for every ordinary
    -- def (a def body has no free binder names); `fix` uses it to hang
    -- its self-knot on the very machinery that early binding already
    -- provides, WITHOUT putting the knot in a VarEnv — VarEnvs are
    -- compared by `eq?`, and a self-referential one would not terminate.
  , deVars  :: VarEnv
  }

type RunDefs = Map String DefEntry

-- The name `fix` binds its knot to.  `#` cannot start an identifier, so
-- no source program and no reflected atom can name or shadow it.
selfKnotName :: String
selfKnotName = "#self"

-- Extend `base` with defs in definition order; each body snapshots
-- base + all-earlier-defs + itself.  Braid has no forward references
-- (the typechecker's left fold rejects them), so "earlier defs" is the
-- exact set a body may legally mention besides itself.
extendRunDefs :: RunDefs -> [(String, Int, Bool, Term)] -> RunDefs
extendRunDefs = foldl step
  where
    -- PREFIX scope, with no self-knot: since 5a½ a definition is not in
    -- scope in its own body, so `acc` (everything strictly earlier) is
    -- exactly what the body may mention.  Recursion is `fix`, which ties
    -- its own knot at the value.
    step acc (name, ar, op, body) =
      M.insert name (DefEntry ar op body acc emptyVarEnv) acc

moduleRunDefs :: Module -> RunDefs
moduleRunDefs = buildRunDefs M.empty

-- ...and what the reflection words read while it runs: the same four
-- tables the checker finished with (2026-09-16).
moduleRCtx :: Module -> RCtx
moduleRCtx m = RCtx (modEnv m) (modDatas m) (modAliases m) (modTheories m)

-- Fold a module's data artifacts and defs onto a base environment.
-- Data-artifact bodies are prim-only (constructors, unrollers, merge),
-- so their scope is inert.
--
-- A module's own defs are MUTUALLY visible: every one captures the
-- finished scope rather than the prefix that happened to precede it.
-- Sequential capture would make runtime resolution depend on source
-- order in a way the typechecker no longer does — a theory slot is
-- forward-declared at its declared type, so a slot body may call a
-- module def while a module def calls the slot, and only one of those
-- can come first.  `base` entries keep the scopes they were built with,
-- so a module def shadowing a prelude name cannot reach back into the
-- prelude's own calls.
buildRunDefs :: RunDefs -> Module -> RunDefs
buildRunDefs base m =
  let arts = [ (name, ar, op, term)
             | d <- modDatas m
             , (name, (ar, op, term)) <- snd (dataDeclArtifacts d) ]
      -- a checked file carries the prelude as a PREFIX of modDefs; those
      -- keep sequential capture, so a module def shadowing a prelude
      -- name cannot reach back into the prelude's own calls
      preNames = [ n | (n, _, _) <- modDefs preludeModule ]
      nameOf (n, _, _) = n
      (preDefs, ownDefs)
        | map nameOf (take (length preNames) (modDefs m)) == preNames
            = splitAt (length preNames) (modDefs m)
        | otherwise = ([], modDefs m)
      entryOf (name, sc, term) = (name, arityOf sc, openOf sc, term)
      base' = extendRunDefs base (arts ++ map entryOf preDefs)
      final = foldl step base' (map entryOf ownDefs)
      step acc (name, ar, op, body) =
        M.insert name (DefEntry ar op body final emptyVarEnv) acc
  in final
  where


-- Evaluate a term: returns the final stack and the print log.  The Env
-- is needed to compute closed arities of grouped compound operands; the
-- VarEnv holds named-abstraction parameters in scope.
type Eval = ExceptT String IO

-- The evaluator runs in TWO phases, so it is generic in its monad.
--
--   * at runtime, in `Eval` — IO edges work, no step budget;
--   * at ELABORATION, purely, so a functor (a `Code ⇒ Code` word) can
--     be run while a module is still being checked.  There, IO must be
--     unreachable — which it is, because a functor's grade is checked
--     `⇒` and not `⇒!` before it may run — and evaluation is
--     fuel-bounded, because purity is not totality: a functor can loop.
--
-- `tick` is the budget hook; the IO instance ignores it.
class MonadError String m => EvalM m where
  liftEvalIO :: IO a -> m a
  tick       :: m ()

instance EvalM (ExceptT String IO) where
  liftEvalIO = liftIO
  tick       = pure ()

-- The pure phase: a step budget in State, errors in Either.
type PureEval = StateT Int (Either String)

instance EvalM PureEval where
  liftEvalIO _ =
    throwError "internal: an IO edge was reached during elaboration \
               \(a functor must be pure — this should have been a grade error)"
  tick = do
    n <- get
    if n <= (0 :: Int)
      then throwError "elaboration step budget exhausted: a functor \
                      \did not terminate (or needs a larger budget)"
      else put (n - 1)

-- One run of the evaluator at elaboration time.
elabFuel :: Int
elabFuel = 1000000

runPureEval :: PureEval a -> Either String a
runPureEval = runPureEvalWith elabFuel

runPureEvalWith :: Int -> PureEval a -> Either String a
runPureEvalWith n m = evalStateT m n

-- no binder parameters in scope (the usual starting VarEnv)
emptyVarEnv :: VarEnv
emptyVarEnv = M.empty

{-# SPECIALIZE evalTerm :: RCtx -> RunDefs -> VarEnv -> Term -> [Value]
                        -> Eval ([Value], [String]) #-}
evalTerm :: EvalM m => RCtx -> RunDefs -> VarEnv -> Term -> [Value]
         -> m ([Value], [String])
evalTerm env defs vars term st =
  case term of
    Seq _ t u -> do
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
      tick   -- `loop` and def recursion re-enter goAtoms, so this counts
             -- every atom application, not merely every source stage
      (out, stk', logs) <- applyAtom (null more) a stk
      (outRest, logs') <- goAtoms more stk'
      pure (out ++ outRest, logs ++ logs')

    -- ev is special: its Γ is the stack segment after the code value.
    -- As the final atom that segment is the whole remaining stack; as a
    -- non-final atom it was closed to • by the typechecker.  (Parameters
    -- shadow the special forms, hence the vars guards.)
    applyAtom isFinal (Prim "ev") stk
      | not (M.member "ev" vars) = do
          (args, stk') <- takeWires "ev" 1 stk
          case args of
            [VFn scope cvars body] -> do
              let seg = if isFinal then stk' else []
              (out, logs) <- evalTerm env scope cvars body seg
              pure (out, if isFinal then [] else stk', logs)
            _ ->
              throwError "Runtime type error in ev: expected a quotation"
    -- into: the open eliminator.  Tag 0 runs the handler on its own
    -- bundle and the handler's answer (already a value of the remaining
    -- sum) IS the result; every other tag shifts down one, bundle
    -- untouched.  That shift is the whole content of `[h, id]` at a
    -- positional row — and the reason this cannot be derived.
    applyAtom _ (Prim "into") stk
      | not (M.member "into" vars), not (M.member "into" defs) = do
          (args, stk') <- takeWires "into" 2 stk
          case args of
            [VFn scope cv body, VSum tag bundle]
              | tag == 0 -> do
                  (out, logs) <- evalTerm env scope cv body bundle
                  case out of
                    [v@(VSum _ _)] -> pure ([v], stk', logs)
                    _ -> throwError "Runtime type error in into: the handler \
                                    \must land in the remaining sum"
              | otherwise -> pure ([VSum (tag - 1) bundle], stk', [])
            _ -> throwError "Runtime type error in into: expected a handler \
                            \quotation and a sum"
    -- evalAs: witness-checked splice.  Rebuild the term, infer it in
    -- process, check it SUBSUMES the witness's arrow, then run it on the
    -- segment.  Every failure rides the miss track WITH the untouched
    -- segment as evidence — so the caller can fall back to the witness,
    -- which is a real program, not just a type.
    applyAtom isFinal (Prim "evalAs") stk
      | not (M.member "evalAs" vars), not (M.member "evalAs" defs) =
          runAs isFinal stk

    -- IO edges, in print's mold: effects with honest railway types
    -- readLine: one line from stdin; EOF (or a closed stream) rides
    -- the miss track like any other IO failure
    applyAtom _ (Prim "readLine") stk
      | not (M.member "readLine" vars), not (M.member "readLine" defs) = do
          r <- liftEvalIO (try getLine)
          case r of
            Left e  -> pure ([VSum 1 [VStr (show (e :: IOException))]], stk, [])
            Right t -> pure ([VSum 0 [VStr t]], stk, [])
    applyAtom _ (Prim "readFile") stk
      | not (M.member "readFile" vars), not (M.member "readFile" defs) = do
          (args, stk') <- takeWires "readFile" 1 stk
          case args of
            [VStr path] -> do
              r <- liftEvalIO (try (do t <- readFile path
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
              r <- liftEvalIO (try (writeFile path contents))
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
    -- showStack: the segment as the REPL renders it, deepest wire
    -- first, space separated.  The same `show` per value that `toStr`
    -- uses and that `:s` prints, so one convention serves all three.
    applyAtom isFinal (Prim "showStack") stk
      | not (M.member "showStack" vars), not (M.member "showStack" defs) =
          if isFinal
            then pure ([VStr (unwords (map show stk))], [], [])
            else pure ([VStr ""], stk, [])
    -- #fix: tie the knot — the compiler's own word, emitted by `with
    -- Recursive` and by nothing else.  The quoted body is handed a self-reference
    -- DEEPEST and then its own arguments.  The knot is a DefEntry whose
    -- scope contains itself — the same lazy early-binding cycle
    -- `buildRunDefs` builds for a module — under a name (`#self`) the
    -- parser cannot produce, so nothing can capture it.  Every re-entry
    -- goes through `goAtoms`, so a fix under pure elaboration is
    -- fuel-bounded exactly like a def call or a `loop`.
    applyAtom _ (Prim nm) stk
      | nm == knotPrimName = do
          (args, stk') <- takeWires knotPrimName 1 stk
          case args of
            [VFn scope cv body] -> do
              let knotted = Seq 0 (Prim selfKnotName) body
                  scope'  = M.insert selfKnotName
                              (DefEntry 0 False (Quote knotted) scope' cv)
                              scope
              pure ([VFn scope' cv knotted], stk', [])
            _ -> throwError "Runtime type error in #fix: expected a body quotation"
    -- a generated structural recursor: dispatch on the tag, fold every
    -- recursive slot FIRST (moving it to the front), then run that
    -- alternative's case on folded-then-payload.  Terminating by
    -- construction: every recursive call is on a proper sub-value.
    applyAtom _ (Prim nm) stk
      | Just spec <- foldPrimSpec nm = do
          (args, stk') <- takeWires nm (length spec + 1) stk
          case splitAt (length spec) args of
            (fns, [v]) -> do
              (out, logs) <- foldPoints fns spec v
              pure (out, stk', logs)
            _ -> throwError (recErr "expected one case per constructor \
                                    \and a value")
    -- mapAccumN: the tier's one catamorphism.  n is erased, so the
    -- bundle is the final segment and its runtime width is the witness
    -- (the forget convention).  The accumulator is ONE WIRE, so the
    -- two wires taken here fix the boundary with no width channel.
    -- Non-final was typed at n := 0.
    applyAtom isFinal (Prim "mapAccumN") stk
      | not (M.member "mapAccumN" vars), not (M.member "mapAccumN" defs) = do
          (args, stk') <- takeWires "mapAccumN" 2 stk
          case args of
            [VFn scope cv body, acc0] -> do
              let bundle = if isFinal then stk' else []
                  go acc [] outs logs = pure (acc, reverse outs, logs)
                  go acc (x : xs) outs logs = do
                    (out, lg) <- evalTerm env scope cv body [acc, x]
                    case out of
                      [acc', y] -> go acc' xs (y : outs) (logs ++ lg)
                      _ -> throwError "Runtime type error in mapAccumN: the step must return the accumulator and one wire"
              (acc', ys, logs) <- go acc0 bundle [] []
              pure (acc' : ys, if isFinal then [] else stk', logs)
            _ -> throwError "Runtime type error in mapAccumN: expected a step quotation and an initial accumulator"
    -- The Naperian structure maps: width-polymorphic wiring, and the
    -- segment IS the witness.  `zipN` and `unzipN` are inverse (both
    -- sides box); `splitN` chunks the flat stack-native form.
    applyAtom isFinal (Prim "zipN") stk
      | not (M.member "zipN" vars), not (M.member "zipN" defs) =
          if not isFinal then pure ([], stk, [])
          else if odd (length stk)
            then throwError "zipN: odd segment (unreachable on typechecked programs)"
            else let (xs, ys) = splitAt (length stk `div` 2) stk
                 in pure (zipWith (\x y -> VSum 0 [x, y]) xs ys, [], [])
    applyAtom isFinal (Prim "unzipN") stk
      | not (M.member "unzipN" vars), not (M.member "unzipN" defs) =
          if not isFinal then pure ([], stk, [])
          else do
            let unboxPair (VSum 0 [x, y]) = pure (x, y)
                unboxPair _ = throwError
                  "unzipN: element is not a boxed pair (unreachable on \
                  \typechecked programs) \8212 to split the FLAT (a b)\8319, \
                  \use `splitN`"
            pairs <- mapM unboxPair stk
            pure (map fst pairs ++ map snd pairs, [], [])
    applyAtom isFinal (Prim "splitN") stk
      | not (M.member "splitN" vars), not (M.member "splitN" defs) =
          if not isFinal then pure ([], stk, [])
          else if odd (length stk)
            then throwError "splitN: odd segment (unreachable on typechecked programs)"
            else let pairs = chunk2 stk
                 in pure (map fst pairs ++ map snd pairs, [], [])
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
      | isFloatLiteral name = pure ([VFloat (read name)], stk, [])
      | isStrLiteral name = pure ([VStr (drop 1 name)], stk, [])
      | isSymLiteral name = pure ([VSym name], stk, [])
      | Just entry <- M.lookup name defs =
          -- jump into the def's body under ITS captured scope, not the
          -- caller's — early binding (see DefEntry)
          let k     = deArity entry
              open  = deOpen  entry
              body  = deBody  entry
              scope = deScope entry
              cvars = deVars  entry
          in if open && isFinal
            then do
              (out, logs) <- evalTerm env scope cvars body stk
              pure (out, [], logs)
            else do
              (args, stk') <- takeWires name k stk
              (out, logs) <- evalTerm env scope cvars body args
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
                Forall [dummy] [] [] [] [] [] (arrPure SEnd (SCons (TVarTy dummy) SEnd))
              arityEnv = foldr (\n -> M.insert n dummyScheme)
                               (rcEnv env) (M.keys vars)
          Arrow i _ _ <- liftEither (inferTermIn arityEnv t')
          let k = closedArity i
          (args, stk') <- takeWires "grouped program" k stk
          (out, logs) <- evalTerm env defs vars t' args
          pure (out, stk', logs)

    -- A splice: rebuild the code, typecheck it, check that it SUBSUMES
    -- the witness's arrow, and only then run it.  Every failure is a
    -- value on the miss track with the untouched input segment as
    -- evidence.  Subsumption rather than unification is the whole point:
    -- types are erased by now, so the check cannot know which
    -- instantiation of a polymorphic witness the context chose, and must
    -- demand code that handles every one.
    runAs isFinal stk = do
      (args, stk') <- takeWires "evalAs" 2 stk
      let seg  = if isFinal then stk' else []
          keep = if isFinal then [] else stk'
          missWith msg = pure ([VSum 1 (VStr msg : seg)], keep, [])
      case args of
        [VFn ws wv wt, c] ->
          case codeToTermV c of
            Left e -> missWith e
            Right term ->
              case witnessArrow wv wt >>= checkAgainst term of
                Left e -> missWith e
                Right () -> do
                  -- a spliced program's failure is a VALUE on the miss
                  -- track, not this program's failure: catch rather than
                  -- nest a second runExceptT (which would pin us to IO).
                  -- The code runs in the WITNESS's scope, not the
                  -- caller's: the witness was typed against the module
                  -- (`env`), and the scope that matches is the one it
                  -- closed over — a prelude word such as `lift2` or `box`
                  -- has only the prelude in its own early-bound snapshot.
                  r <- (Right <$> evalTerm env ws M.empty term seg)
                         `catchError` (pure . Left)
                  case r of
                    Left e -> missWith e
                    Right (out, logs) -> pure ([VSum 0 out], keep, logs)
        _ -> throwError "evalAs: expected a witness and a Code value"

    -- the witness's TYPE is what it contributes; it is never applied
    witnessArrow wv wt = groundTerm (rcEnv env) wv wt >>= inferTermIn (rcEnv env)

    checkAgainst term want = do
      (got, gsubs) <- inferTermSub (rcEnv env) term
      subsumes (generalizeWith M.empty gsubs got) want

    recErr what = "Runtime type error in a structural recursor: " ++ what

    foldPoints fns spec = go
      where
        go (VSum tag bundle)
          | tag < length spec, (fn : _) <- drop tag fns = do
              (seg, logs) <- case spec !! tag of
                Nothing -> pure (bundle, [])
                Just flags
                  | length flags == length bundle -> do
                      rs <- mapM go [ v | (True, v) <- zip flags bundle ]
                      pure ( concatMap fst rs
                               ++ [ v | (False, v) <- zip flags bundle ]
                           , concatMap snd rs )
                  | otherwise ->
                      throwError (recErr "an alternative's payload does \
                                         \not match its declared width")
              case fn of
                VFn scope cv body -> do
                  (out, lg) <- evalTerm env scope cv body seg
                  pure (out, logs ++ lg)
                _ -> throwError (recErr "a case must be a quotation")
        go _ = throwError (recErr "expected a value of the declared type")

    takeWires name k stk
      | length stk >= k = pure (take k stk, drop k stk)
      | otherwise =
          throwError $ "Runtime stack underflow in " ++ name
               ++ " (unreachable on typechecked programs)"

builtinArity :: String -> Either String Int
builtinArity name
  | isJust (receiptLabel name) = Right 0
  | isJust (distPrimArity name) = Right 2
builtinArity name =
  case M.lookup name primEnv of
    Just (Forall _ _ _ _ _ _ (Arrow i _ _)) -> Right (closedArity i)
    Nothing -> Left $ "Unknown primitive at runtime: " ++ name

runBuiltin :: RCtx -> RunDefs -> String -> [Value]
           -> Either String ([Value], [String])
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
-- the identity on •: nothing in, nothing out, nothing done
runBuiltin _ _ "one"   []               = Right ([], [])
-- a receipt is `pass` that a type can see: nothing happens here, and
-- the whole content is in the manifest (like weaken's bound)
runBuiltin _ _ name    []
  | isJust (receiptLabel name)          = Right ([], [])
runBuiltin _ _ "+"     [VInt x, VInt y] = Right ([VInt (x + y)], [])
runBuiltin _ _ "*"     [VInt x, VInt y] = Right ([VInt (x * y)], [])
runBuiltin _ _ "print" [v]              = Right ([], [show v])
-- Two programs are the same morphism when they consume the same number
-- of wires and return the same tuple of symbolic terms.  A captured
-- binder value would be a free constant we cannot see through, so a
-- quote that closed over one is reported rather than guessed at.
runBuiltin env defs "sameCode" [VFn s1 v1 t1, VFn s2 v2 t2]
  | not (M.null v1) || not (M.null v2) =
      Left "sameCode: a quotation that captured a bound name is outside \
           \the structural fragment"
  | otherwise =
      case sameProgram (rcEnv env) (M.union s1 defs) (M.union s2 defs) t1 t2 of
        Right same -> Right ([VSum (if same then 0 else 1) []], [])
        Left e     -> Left ("sameCode: " ++ e)
-- The same question asked of CODE.  Two differences from `sameCode`,
-- both in `sameCodeC`'s favour: a functor's output is Code, so this is
-- the only form in which a law about a functor can be stated at all;
-- and Code has already been through abstraction elimination, so a
-- program that `sameCode` refuses for carrying a binder is decided here
-- once it has been through `getCode`.
runBuiltin env defs "sameCodeC" [c1, c2] = do
  t1 <- inC (codeToTermV c1)
  t2 <- inC (codeToTermV c2)
  same <- inC (sameProgram (rcEnv env) defs defs t1 t2)
  Right ([VSum (if same then 0 else 1) []], [])
  where inC = either (Left . ("sameCodeC: " ++)) Right
-- The rule-set engine.  Atomwise on NAMES, because Code carries names
-- and `Fn` values do not, and structural rather than textual because
-- the synthesized generators (`#dist:K`, `#fold:…`) do not round-trip
-- through `unparse` — `#` lexes as a comment.
runBuiltin _ _ "rewrite" [froms, tos, c] = do
  fs <- decodeListV froms >>= mapM symName
  ts <- decodeListV tos   >>= mapM symName
  if length fs /= length ts
    then Left "rewrite: the two name lists have different lengths"
    else do
      c' <- rewriteCode (zip fs ts) c
      Right ([c'], [])
  where
    symName (VSym s) = Right s
    symName v        = Left $ "rewrite: a rule's two sides are symbols, "
                           ++ "but this one is " ++ show v
runBuiltin _ _ "true"  []               = Right ([VSum 0 []], [])
runBuiltin _ _ "false" []               = Right ([VSum 1 []], [])
runBuiltin _ _ "eq?"  [x, y]            = Right ([VSum (if x == y then 0 else 1) [x, y]], [])
runBuiltin _ _ "lt?"  [VInt x, VInt y]  = Right ([VSum (if x < y then 0 else 1) [VInt x, VInt y]], [])
runBuiltin _ _ "-"    [VInt x, VInt y]  = Right ([VInt (x - y)], [])
runBuiltin _ _ "div"  [VInt _, VInt 0]  = Left "division by zero"
runBuiltin _ _ "div"  [VInt x, VInt y]  = Right ([VInt (x `div` y)], [])
runBuiltin _ _ "mod"  [VInt _, VInt 0]  = Left "modulo by zero"
runBuiltin _ _ "mod"  [VInt x, VInt y]  = Right ([VInt (x `mod` y)], [])
-- Float arithmetic is IEEE, with one refusal kept for company with
-- `div`: dividing by zero has no answer worth inventing.  Everything
-- else that can leave the finite doubles (`fexp` overflowing, `fsqrt`
-- of a negative) yields the IEEE value, which prints as itself.
runBuiltin _ _ "fadd"  [VFloat x, VFloat y] = Right ([VFloat (x + y)], [])
runBuiltin _ _ "fsub"  [VFloat x, VFloat y] = Right ([VFloat (x - y)], [])
runBuiltin _ _ "fmul"  [VFloat x, VFloat y] = Right ([VFloat (x * y)], [])
runBuiltin _ _ "fdiv"  [VFloat _, VFloat 0] = Left "division by zero"
runBuiltin _ _ "fdiv"  [VFloat x, VFloat y] = Right ([VFloat (x / y)], [])
runBuiltin _ _ "flt?"  [VFloat x, VFloat y] =
  Right ([VSum (if x < y then 0 else 1) [VFloat x, VFloat y]], [])
runBuiltin _ _ "fexp"  [VFloat x]           = Right ([VFloat (exp x)], [])
runBuiltin _ _ "fsin"  [VFloat x]           = Right ([VFloat (sin x)], [])
runBuiltin _ _ "fcos"  [VFloat x]           = Right ([VFloat (cos x)], [])
runBuiltin _ _ "fsqrt" [VFloat x]           = Right ([VFloat (sqrt x)], [])
runBuiltin _ _ "toFloat" [VInt n]           = Right ([VFloat (fromIntegral n)], [])
runBuiltin _ _ "floor" [VFloat x]           = Right ([VInt (floor x)], [])
runBuiltin _ _ "cat"  [VStr x, VStr y]  = Right ([VStr (x ++ y)], [])
runBuiltin _ _ "toStr" [v]              = Right ([VStr (show v)], [])
runBuiltin _ _ "symStr" [VSym t]        = Right ([VStr (drop 1 t)], [])
runBuiltin _ _ "unparse" [c]            = do
  t <- codeToTermV c
  Right ([VStr (renderTerm t)], [])
runBuiltin env _ "parse" [VStr src]     =
  case parseProgram src >>= reflectPure (rcEnv env) of
    Right c -> Right ([VSum 0 [c]], [])
    Left e  -> Right ([VSum 1 [VStr e]], [])
runBuiltin env _ "reflect" [VFn _ cv t] =
  case reflectFn (rcEnv env) cv t of
    Right c -> Right ([VSum 0 [c]], [])
    Left e  -> Right ([VSum 1 [VStr e]], [])
-- REFLECTED TYPES (2026-09-16).  Each reads the prefix scope the
-- evaluator is running over — the same four tables the checker
-- finished with — and nothing else.
runBuiltin ctx _ "typeOfWord" [VStr w] =
  Right ([railed (typeOfWordV ctx w)], [])
runBuiltin ctx _ "declOf" [VStr n] =
  Right ([railed (declOfV ctx n)], [])
runBuiltin ctx _ "typeOfCode" [c] =
  Right ([railed (typeOfCodeV ctx c)], [])
runBuiltin ctx _ "envOf" [] = Right ([envOfV ctx], [])
runBuiltin ctx _ "showType" [r] =
  case showTypeV ctx r of
    Right t -> Right ([VStr t], [])
    Left e  -> Left ("showType: " ++ e)
runBuiltin env _ "checkedStage" [eta]    = do
  etaT <- codeToTermV eta
  checkInterposed (rcEnv env) etaT
  Right ([eta], [])
runBuiltin _ _ "asInt?" [VStr t]        =
  case reads t :: [(Int, String)] of
    [(n, "")] -> Right ([VSum 0 [VInt n]], [])
    _         -> Right ([VSum 1 [VStr t]], [])
runBuiltin _ _ "asFloat?" [VStr t]
  | isFloatLiteral t = Right ([VSum 0 [VFloat (read t)]], [])
  | otherwise        = Right ([VSum 1 [VStr t]], [])
runBuiltin _ _ "split" [VStr src, VStr sep] =
  Right ([encodeListV (map VStr (splitOnStr sep src))], [])
-- #dist:K at runtime: the wire joins the bundle of any of the first K
-- alternatives (deepest, so it heads the bundle), and a tag at or past
-- K is the residual, which passes untouched — the wire is simply gone
-- from it, which is what the type already said.
runBuiltin _ _ nm [x, VSum tag bundle]
  | Just k <- distPrimArity nm =
      Right ([if tag < k then VSum tag (x : bundle) else VSum tag bundle], [])
runBuiltin _ _ "there" [VSum t bundle]  = Right ([VSum (t + 1) bundle], [])
runBuiltin _ _ "merge" [VSum _ bundle]  = Right (bundle, [])
-- THE DECLARATION WORDS, CALLED FROM A PROGRAM (stage 8, 2026-09-17).
-- The word appends a RECORD to the evaluator's log and the loader does
-- the dictionary's half, exactly as `print` appends a line and the
-- driver does the world's half.  `defW` takes the body as Code and
-- renders it back to source, which is what `unparse` does and what the
-- def bucket has always held.
runBuiltin _ _ "defW" [c, VStr nm] = do
  t <- codeToTermV c
  Right ([], [declLog "defW" [nm, renderTerm t]])
-- ...and the one that has no keyword until a module binds it: it
-- registers a CHECK, which runs at module start beside the laws.
runBuiltin _ _ "testW" [c, VStr nm] = do
  t <- codeToTermV c
  Right ([], [declLog "testW" [nm, renderTerm t]])
-- ...and the nine that a KEYWORD LINE calls and a program does not, yet.
-- Refused by name, saying what the restriction is: a `theory` declared
-- from a program would have to be checked before the defs that read it,
-- and the dictionary the checker reads is read once, above them.
runBuiltin _ _ w _
  | Just dw <- declWordNamed w, w /= "defW" = Left $
      "`" ++ w ++ "` is a declaration word, and a program may not call "
        ++ "this one yet: `" ++ dwKeyword dw ++ "` declares something the "
        ++ "module's own defs are checked AGAINST, and they are checked "
        ++ "above the program that would declare it.  Write the keyword "
        ++ "line.  `defW` is the one a program may call, because a def is "
        ++ "checked where it lands (MANUAL \167 8)."
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
-- segment-consuming atoms (ev, injections, merge, loop, …) are
-- rejected onto the miss track with an explanation.
--------------------------------------------------------------------------------

-- The stage `interpose` inserts after every cut must be a UNIT
-- ENDOMORPHISM whiskered by the rest of the stack: `∀ρ. ρ ⇒ ρ`, or
-- `∀ρ. E ρ ⇒ E ρ` for a closed prefix E of nullary data types — in
-- practice resources, which `with` routing keeps deepest for the whole
-- scope.  Such a stage touches no wire of the program, so inserting it
-- at every cut leaves the program's type where it was.
--
-- E is read off the stage's own arrow (input and output unified), and
-- then the stage's SCHEME must be at least as general as `E ρ ⇒ E ρ`
-- with ρ rigid.  Subsumption, not unification: unifying with `ρ ⇒ ρ`
-- would bless `Int ρ' ⇒ Int ρ'` at ρ := Int ρ', a stage that needs a
-- wire and fails at any empty cut.  Only the WIRES are skolemized
-- (`subsumesShape`): a marker prints, a metered stage carries `Fuel`,
-- an instrumented one carries its functor's receipt — the manifest is
-- not what makes a stage fit at a cut.
checkInterposed :: Env -> Term -> Either String ()
checkInterposed env t = do
  (arr@(Arrow i o _), asubs) <- inferTermSub env t
  let shown = "interpose: `" ++ renderTerm t ++ "` is "
           ++ show (normalizeArrow arr)
      rule  = "a stage inserted at every cut must be ρ ⇒ ρ, or E ρ ⇒ E ρ "
           ++ "for resource wires E routed beneath the whole scope"
      whisk (SCons ty@(TData _ []) r) = (ty :) <$> whisk r
      whisk (STail _)                 = Just []
      whisk _                         = Nothing
  s <- either (const (Left (shown ++ ", not an endomorphism; " ++ rule)))
              Right (solve [CEqStack i o])
  e <- maybe (Left (shown ++ ", which reads a wire; " ++ rule))
             Right (whisk (apply s i))
  let side = foldr SCons (STail (SV "ρ")) e
      want = Arrow side side (Eff S.empty (Just (EV "ε")))
  either (\err -> Left (shown ++ "; " ++ rule ++ " (" ++ err ++ ")"))
         Right (subsumesShape (generalizeWith M.empty asubs arr) want)

-- Substitute atom names through a whole spine.  This is `with Inst`'s
-- `renameSlotsT` seen from the Code side: a rule set is a by-generators
-- functor whose action on a generator is a rename and whose action on
-- everything else is congruence.  Quotes, rows and groups recurse; a
-- row's residual flag is carried, never inspected.
rewriteCode :: [(String, String)] -> Value -> Either String Value
rewriteCode tbl = go
  where
    go code = do
      stages <- decodeListV code
      encodeListV <$> mapM stage stages
    stage sv = encodeListV <$> (decodeListV sv >>= mapM atom)
    atom a@(VSum 0 [VSym s]) = Right (maybe a (\s' -> VSum 0 [VSym s']) (lookup s tbl))
    atom (VSum 4 [c])        = (\c' -> VSum 4 [c']) <$> go c
    atom (VSum 5 [csV, bV])  = do
      cs <- decodeListV csV >>= mapM go
      Right (VSum 5 [encodeListV cs, bV])
    atom (VSum 6 [c])        = (\c' -> VSum 6 [c']) <$> go c
    atom a                   = Right a

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
spineOf = map snd . spineLines

-- ...and the same with each stage's LINE, which is what the `with`
-- elaborator keeps so that a rewritten stage still says where it was
-- written (2026-09-15).  A stage inherits the stamp of the `>>` that
-- introduced it; 0 means the compiler wrote it.
spineLines :: Term -> [(Int, [Term])]
spineLines = go 0
  where
    go ln (Seq n a b) = go ln a ++ go (if n == 0 then ln else n) b
    go ln (Tensor ts) = [(ln, ts)]
    go ln t           = [(ln, [t])]

chainTerm :: [[Term]] -> Term
chainTerm = chainLines . map ((,) 0)

-- The inverse of `spineLines`: rebuild the chain, giving each `>>` the
-- line of the stage it introduces — exactly the stamp the parser puts
-- there, so an elaborated body is addressable the same way a written
-- one is.
chainLines :: [(Int, [Term])] -> Term
chainLines ss =
  case [ (l, stageT s) | (l, s) <- ss, not (null s) ] of
    []  -> Prim "pass"
    sts -> chain sts
  where
    stageT [t] = t
    stageT ts' = Tensor ts'
    chain [(_, t)]                   = t
    chain ((_, t) : r@((l, _) : _))  = Seq l t (chain r)
    chain []                         = Prim "pass"

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
          ++ (if res then " | ---" else "") ++ ")"
    rAtom (OpenAbs slots hasRest b) =
      "(" ++ unwords (map (maybe "_" id) slots ++ ["..." | hasRest])
          ++ " -> " ++ renderTerm b ++ ")"
    -- headers are written out before reflection, so these are reached
    -- only when an error renders an unelaborated term — but the group
    -- wildcard below would rebuild them forever, so say them plainly
    rAtom (With _ ns b) = "(with " ++ unwords ns ++ " ; " ++ renderTerm b ++ ")"
    rAtom (In ns b)   = "(in " ++ unwords ns ++ " ; " ++ renderTerm b ++ ")"
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
    -- `with` is written out before reification; if one survives, the
    -- group wildcard below would loop forever rebuilding it
    atomVal (With _ _ _) =
      Left "internal: an unelaborated `with` reached code reification"
    atomVal (In _ _) =
      Left "internal: an unelaborated `in` reached code reification"
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

--------------------------------------------------------------------------------
-- 11.6 Reflected types (2026-09-16)
--
-- `Ty`, `SType`, `EffRow` and `Arrow` as DATA, in the language, plus a
-- `data`/`type`/`theory` declaration as data.  Everything here is a
-- STATIC FACT about the prefix scope — the checker already knows it —
-- so the words that read it are pure, usable at elaboration, and cost
-- nothing at run time.
--
-- What is NOT here, on its own merits: `∀a. a ⇒ TypeRep`.  Nothing
-- below produces a rep from a WIRE, only from a NAME or from CODE, so
-- no free theorem is lost and no type is passed at run time.  Such a
-- word cannot be written, either: there is no atom that takes a value
-- and answers its type (MANUAL §12).
--
-- EQUALITY.  Every rep built here is built from a NORMALIZED arrow
-- (`normalizeArrow`), so two schemes are the same scheme exactly when
-- their reps are `eq?`.  A rep assembled any other way carries no such
-- guarantee: `eq?` on unnormalized reps compares variable NAMES.
--
-- The nine alternatives of `data TypeRep`, by tag:
--   0 base   .Int .Float .Str .Sym
--   1 var    a type variable, by name
--   2 data   Name, and one stack per argument
--   3 fn     Fn⟨…⟩, around an arrow rep
--   4 sum    the alternatives, and the row tail (`.•` when closed)
--   5 tail   a stack's open end ρ — only ever LAST in a stack
--   6 arrow  Γ, Δ, the labels, and the effect tail (`.•` when closed)
--   7 rep    a closed SEGMENT repeated a width: `Aⁿ`, `(A B)ⁿ`
--   8 fin    `Fin(n)`, an index into a bundle of that width
-- A stack is `List(TypeRep)` (`type StackRep`), front wire first.
--
-- WIDTHS (2026-09-16).  `Aⁿ` is a STACK SEGMENT repeated n times — not
-- a wire — so `rep` stands in a stack beside `tail` and `wire?` says
-- false for it.  `Fin(n)` IS a wire, and carries the same width.  The
-- width tier is a second sort and keeps its own rep, `WidthRep`: a
-- literal, or a variable at an offset (`weaken : Fin(n) ⇒ Fin(n+1)`
-- needs the offset, so the rep says it rather than losing it).
--
-- THE RULE A WIDTH REP MUST NOT BREAK: never flatten a VARIABLE width
-- into a type.  A concrete one may reflect expanded, because the
-- checker itself expands it (`sexp`: `Int³` IS three wires and there is
-- no `SExp` left to reflect); a variable one must come back with its
-- variable, or `a0ⁿ⁰` and `a0ᵐ⁰` would be the same type.

-- the one sym that is not a name: the closed end of a row, of an effect
-- row, or the absence of a tail.  `•` is unwritable as a word, so it
-- cannot collide with a variable.
closedSym :: Value
closedSym = VSym ".•"

symOf :: String -> Value
symOf n = VSym ('.' : n)

-- A WIDTH, as data.  The checker's `Exp` is an offset plus an optional
-- variable, and the rep says exactly that: `lit k`, or `var n k` for
-- `n+k`.  It is its own type because a width is its own SORT — writing
-- it as a `TypeRep` alternative would let a width stand where a type
-- stands, which is the confusion the tier exists to prevent.
reprWidthV :: Exp -> Value
reprWidthV (Exp k Nothing)       = VSum 0 [VInt k]
reprWidthV (Exp k (Just (NV n))) = VSum 1 [symOf n, VInt k]

expOfRepV :: Value -> Either String Exp
expOfRepV (VSum 0 [VInt k])         = Right (Exp k Nothing)
expOfRepV (VSum 1 [VSym n, VInt k]) = Right (Exp k (Just (NV (drop 1 n))))
expOfRepV v = Left ("this is not a width rep: " ++ show v)

reprTyV :: Ty -> Either String Value
reprTyV TInt             = Right (VSum 0 [VSym ".Int"])
reprTyV TFloat           = Right (VSum 0 [VSym ".Float"])
reprTyV TStr             = Right (VSum 0 [VSym ".Str"])
reprTyV TSym             = Right (VSum 0 [VSym ".Sym"])
reprTyV (TVarTy (TV n))  = Right (VSum 1 [symOf n])
reprTyV (TData n args)   = do
  as <- mapM reprStackV args
  Right (VSum 2 [symOf n, encodeListV as])
reprTyV (TFn arr)        = (\a -> VSum 3 [a]) <$> reprArrowV arr
reprTyV (TSum row)       = do
  (alts, tl) <- reprRowV row
  Right (VSum 4 [encodeListV alts, tl])
reprTyV (TFin e)         = Right (VSum 8 [reprWidthV e])

reprStackV :: SType -> Either String Value
reprStackV st = encodeListV <$> go st
  where
    go SEnd             = Right []
    go (STail (SV n))   = Right [VSum 5 [symOf n]]
    go (SCons t r)      = (:) <$> reprTyV t <*> go r
    -- a repeated segment is a STACK ITEM, not a wire: the base is a
    -- closed stack, the width rides beside it, and the rest follows
    go (SExp b e r)     = do
      bv <- reprStackV b
      (VSum 7 [bv, reprWidthV e] :) <$> go r

reprRowV :: SumRow -> Either String ([Value], Value)
reprRowV RNil            = Right ([], closedSym)
reprRowV (RTail (RV n))  = Right ([], symOf n)
reprRowV (RCons st r)    = do
  v        <- reprStackV st
  (vs, tl) <- reprRowV r
  Right (v : vs, tl)

reprArrowV :: Arrow -> Either String Value
reprArrowV (Arrow i o (Eff ls tl)) = do
  iv <- reprStackV i
  ov <- reprStackV o
  Right (VSum 6 [ iv, ov
                , encodeListV (map symOf (S.toList ls))
                , maybe closedSym (\(EV n) -> symOf n) tl ])

-- A SCHEME's rep is its arrow's, normalized: the quantifiers become the
-- named variables `a0`, `ρ0`, `σ0`, `ε0` the REPL already prints, so a
-- rep needs no binder list and `eq?` decides equality.
reprSchemeV :: Scheme -> Either String Value
reprSchemeV (Forall _ _ _ _ _ _ arr) = reprArrowV (normalizeArrow arr)

-- ...and back.  The inverse is what `showType` is written on: the rep
-- goes home to a `Ty`/`Arrow` and the display is the REPL's own, alias
-- folding included, so there is exactly one renderer for a type.
tyOfRepV :: Value -> Either String Ty
tyOfRepV (VSum 0 [VSym s]) =
  Right $ case s of
    ".Int"   -> TInt
    ".Float" -> TFloat
    ".Str"   -> TStr
    ".Sym"   -> TSym
    _        -> TData (drop 1 s) []   -- a base name nobody declared
tyOfRepV (VSum 1 [VSym s]) = Right (TVarTy (TV (drop 1 s)))
tyOfRepV (VSum 2 [VSym s, asV]) = do
  as <- decodeListV asV >>= mapM stackOfRepV
  Right (TData (drop 1 s) as)
tyOfRepV (VSum 3 [a]) = TFn <$> arrowOfRepV a
tyOfRepV (VSum 8 [w]) = TFin <$> expOfRepV w
tyOfRepV (VSum 4 [altsV, VSym tl]) = do
  alts <- decodeListV altsV >>= mapM stackOfRepV
  let end | tl == ".•" = RNil
          | otherwise  = RTail (RV (drop 1 tl))
  Right (TSum (foldr RCons end alts))
tyOfRepV v = Left ("this type rep is not a WIRE: " ++ show v)

stackOfRepV :: Value -> Either String SType
stackOfRepV v = decodeListV v >>= go
  where
    go []                      = Right SEnd
    go [VSum 5 [VSym s]]       = Right (STail (SV (drop 1 s)))
    go (VSum 5 [VSym s] : _)   =
      Left ("a stack's open end " ++ drop 1 s ++ " is its LAST item, and \
            \this rep puts wires after it")
    go (VSum 7 [bv, w] : ts)   = do
      b <- stackOfRepV bv
      e <- expOfRepV w
      sexp b e <$> go ts
    go (t : ts)                = SCons <$> tyOfRepV t <*> go ts

arrowOfRepV :: Value -> Either String Arrow
arrowOfRepV (VSum 6 [iv, ov, lsV, VSym tl]) = do
  i  <- stackOfRepV iv
  o  <- stackOfRepV ov
  ls <- decodeListV lsV >>= mapM lab
  let end | tl == ".•" = Nothing
          | otherwise  = Just (EV (drop 1 tl))
  Right (Arrow i o (Eff (S.fromList ls) end))
  where
    lab (VSym s) = Right (drop 1 s)
    lab x        = Left ("a grade label is a Sym, and this one is " ++ show x)
arrowOfRepV v = Left ("this type rep is not an ARROW: " ++ show v)

-- the display context the reflection words render in: the module's own
-- aliases and carriered labels, exactly as the REPL builds it
dispOfRCtx :: RCtx -> Disp
dispOfRCtx ctx =
  Disp (rcAliases ctx)
       ((ioLabel, ioCarrier)
        : (dictLabel, dictCarrier)
        : [ (dName d, dName d) | d <- rcDatas ctx, dResource d ])

-- `showType` — the REPL's own display, from the rep.  An arrow rep
-- renders as an arrow, a stack-position rep as the stack it stands in,
-- everything else as the wire it is.
showTypeV :: RCtx -> Value -> Either String String
showTypeV ctx v@(VSum 6 _) = showArrowA d <$> arrowOfRepV v
  where d = dispOfRCtx ctx
showTypeV ctx v@(VSum 5 _) = showStackA d <$> stackOfRepV (encodeListV [v])
  where d = dispOfRCtx ctx
showTypeV ctx v@(VSum 7 _) = showStackA d <$> stackOfRepV (encodeListV [v])
  where d = dispOfRCtx ctx
showTypeV ctx v            = showTyA (dispOfRCtx ctx) <$> tyOfRepV v

-- A PARAMETER, as data: its name, its kind, and the arity a constructor
-- parameter's underscores counted (0 for every other kind).
reprParamV :: TyParam -> Value
reprParamV p = VSum 0 [symOf (pName p), VSym kind, VInt arity]
  where
    (kind, arity) = case p of
      PWire _  -> (".wire",  0)
      PStack _ -> (".stack", 0)
      PRow _   -> (".row",   0)
      PWidth _ -> (".width", 0)
      PCon _ k -> (".con",   length k)

-- The three alternatives of `data Decl`, by tag:
--   0 data   name, parameters, body, FIELD NAMES (empty when none)
--   1 type   name, parameters, body            (a transparent alias)
--   2 theory name, parameters, slots, law names
-- A `resource` is a `data` declaration and reflects as one; a `table`
-- reflects as the `data` declaration it wrote.
declOfV :: RCtx -> String -> Either String Value
declOfV ctx name =
  case ([ d | d <- rcDatas ctx, dName d == name ]
       ,[ a | a <- rcAliases ctx, aName a == name ]
       ,[ t | t <- rcTheories ctx, thName t == name ]) of
    (d : _, _, _) -> do
      b <- reprTyV (dBody d)
      Right (VSum 0 [ symOf (dName d)
                    , encodeListV (map reprParamV (dParams d))
                    , b
                    , encodeListV (map symOf (dFields d)) ])
    (_, a : _, _) -> do
      b <- reprTyV (aBody a)
      Right (VSum 1 [ symOf (aName a)
                    , encodeListV (map reprParamV (aParams a))
                    , b ])
    (_, _, t : _) -> do
      sl <- mapM (\(s, arr) -> (\r -> VSum 0 [symOf s, r])
                                 <$> reprArrowV (normalizeArrow arr))
                 (thSlots t)
      Right (VSum 2 [ symOf (thName t)
                    , encodeListV (map reprParamV (thParams t))
                    , encodeListV sl
                    , encodeListV [ symOf n | (n, _) <- thLaws t ] ])
    _ -> Left ("declOf: " ++ name ++ " is not a `data`, `type` or `theory` "
            ++ "declared at this point.  A model, a transformation and a "
            ++ "functor have no rep yet; a `table` reflects as the `data` "
            ++ "declaration it wrote.")

-- A WORD's principal scheme, as data.  Prims, prelude words, module
-- defs and every generated word are one lookup, because they are all in
-- one environment — which is the whole reason this is three lines.
typeOfWordV :: RCtx -> String -> Either String Value
typeOfWordV ctx w =
  case M.lookup w (rcEnv ctx) of
    Just sc -> reprSchemeV sc
    Nothing ->
      Left ("typeOfWord: " ++ w ++ " is not a word at this point.  A "
         ++ "template (`def f in T`) is not one either: it has no type "
         ++ "until a model reads it.")

-- the miss track carries the checker's own message, which is the whole
-- reason these words are total: "there is no such word" is an answer.
railed :: Either String Value -> Value
railed = either (\e -> VSum 1 [VStr e]) (\v -> VSum 0 [v])

-- ...and a CODE value's, inferred in the prefix scope.  Sound at
-- elaboration on a closed spine: the types read are the prefix scope's,
-- fixed before the definition being elaborated (design-macros.md).
typeOfCodeV :: RCtx -> Value -> Either String Value
typeOfCodeV ctx c = do
  term         <- codeToTermV c
  (arr, gsubs) <- inferTermSub (rcEnv ctx) term
  reprSchemeV (generalizeWith M.empty gsubs arr)

-- EVERY WORD IN SCOPE, with its scheme: the bootstrap seed.  Words
-- whose type has no rep (a bundle exponent, a `Fin`) are left out
-- rather than misreported \8212 `typeOfWord` still says why for each.
envOfV :: RCtx -> Value
envOfV ctx =
  encodeListV [ VSum 0 [VStr n, r]
              | (n, sc) <- M.toAscList (rcEnv ctx)
              , Right r <- [reprSchemeV sc] ]

-- embed a runtime value as code that pushes it
valueToCode :: Env -> Value -> Either String Term
valueToCode _   (VInt n)  = Right (Prim (show n))
valueToCode _   (VFloat d)
  | isNaN d || isInfinite d =
      Left "a non-finite Float has no literal form, so it cannot be spliced \
           \into code: NaN, Infinity and -Infinity are values, not literals"
  | otherwise = Right (Prim (showFloatLit d))
valueToCode _   (VStr t)  = Right (Prim ('"' : t))
valueToCode _   (VSym t)  = Right (Prim t)
valueToCode env (VFn _ cv t) = do
  t1 <- groundTerm env cv t
  t2 <- elimAbsTerm env t1
  pure (Quote t2)
valueToCode env (VSum tag vs) = do
  fields <- mapM (valueToCode env) vs
  let inj = Prim ("alt" ++ show (tag + 1))
  pure $ if null fields then inj else Seq 0 (Tensor fields) inj

-- substitute captured closure values (shadow-aware)
groundTerm :: Env -> VarEnv -> Term -> Either String Term
groundTerm env cv = go cv
  where
    go vars t@(Prim n)
      | Just v <- M.lookup n vars = valueToCode env v
      | otherwise                 = Right t
    go vars (Seq n a b)  = Seq n <$> go vars a <*> go vars b
    go vars (Tensor ts)  = Tensor <$> mapM (go vars) ts
    go vars (Quote t)    = Quote <$> go vars t
    go vars (Alts cs r)  = Alts <$> mapM (go vars) cs <*> pure r
    go vars (With ap rs b) = With ap rs <$> go vars b
    go vars (In rs b)    = In rs <$> go vars b
    go vars (OpenAbs slots hasRest b) =
      OpenAbs slots hasRest
        <$> go (foldr M.delete vars [ n | Just n <- slots ]) b

--------------------------------------------------------------------------------
-- 11.6 Abstraction elimination (grinding the non-concatenative edges)
--------------------------------------------------------------------------------

-- The parameter block is a RESOURCE for the duration of the body: it
-- sits at the DEEPEST position, exactly where `with` parks a resource
-- wire, and every body stage is routed over it with a leading `_` per
-- parameter (this is `P ⋉ stage`).  Open-arity atoms eat UPWARD from
-- where they stand, so the block beneath them is never touched — an
-- injection, a merge, an open group anywhere in the body is fine.  A
-- use of a parameter is a `dup` on the resource (it is a copyable one)
-- swapped up to its place in the stage; the number of swaps is the
-- width of the atoms to its LEFT in that stage, which is static.  No
-- stack width is ever needed, so an erased remainder (an open binder's
-- `...`) simply rides above everything, untouched.  The block is
-- dropped once, at the end.
-- `outer` is the enclosing binders' parameters: names that are wires at
-- some LEVEL ABOVE this one.  Bodies are eliminated innermost first, so
-- an inner level must leave such a name alone (a 0-in/1-out push, like a
-- literal) and let the level that owns it thread it — which is exactly
-- what `groupInfo` does when it sees the compiled inner abstraction.
elimAbsTerm :: Env -> Term -> Either String Term
elimAbsTerm env = go []
  where
    go o (Seq n a b)    = Seq n <$> go o a <*> go o b
    go o (Tensor ts)    = Tensor <$> mapM (go o) ts
    go o (Quote t)      = Quote <$> go o t
    go o (Alts cs r)    = Alts <$> mapM (go o) cs <*> pure r
    go o (With ap rs b) = With ap rs <$> go o b
    go o (In rs b)      = In rs <$> go o b
    go o (OpenAbs slots _ b) = do
      let ps = [ n | Just n <- slots ]
      b' <- go (ps ++ o) b
      -- Braid binders bind the DEEPEST wires in slot order, so the
      -- entry layout is already [params][remainder] unless a `_` slot
      -- interleaves a body wire with the names; then a permutation
      -- prefix sinks the names below the unnamed wires.
      inner <- compileAbs env o ps b'
      pure (foldr (Seq 0) inner (paramsBelowStages slots))
    go _ t = Right t

-- Adjacent-transposition stages that stably sink the NAMED slots below
-- the unnamed ones: [slots in written order][rest] → [names][`_`
-- wires][rest], the layout compileAbs compiles against.  Stable (a
-- bubble pass on the named/unnamed key), so each group keeps its written
-- order — in particular the first-written name stays the deepest param.
-- Empty when there is nothing to move.
paramsBelowStages :: [Maybe String] -> [Term]
paramsBelowStages slots0 = go (map key slots0) []
  where
    key = maybe (1 :: Int) (const 0)
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
    go (Seq _ a b)    = go a ++ go b
    go (Tensor ts)    = concatMap go ts
    go (Quote t)      = go t
    go (Alts cs _)    = concatMap go cs
    go (With _ _ b)   = go b
    go (In _ b)       = go b
    go (OpenAbs slots _ b) =
      filter (`notElem` [ n | Just n <- slots ]) (go b)

-- (input arity, param copies to insert at relative input offsets,
-- replacement atom)
data AtomInfo = AtomInfo Int [(Int, Int)] Term

-- Rewrite `body` so the parameters `ps` arrive as a block of wires
-- BELOW its input; the block is dropped at the end.
compileAbs :: Env -> [String] -> [String] -> Term -> Either String Term
compileAbs env outer ps body = do
  stages <- mapM rewriteStage (spineOf body)
  pure (chainTerm (concat stages ++ [finalStage]))
  where
    n = length ps

    swapAt d = replicate d (Prim "_") ++ [Prim "swap", Prim "pass"]
    dupAt d  = replicate d (Prim "_") ++ [Prim "dup", Prim "pass"]
    -- copy the parameter at depth `idx` up to depth `to` (to > idx)
    fetchTo idx to = dupAt idx : [ swapAt j | j <- [idx + 1 .. to - 1] ]

    finalStage = replicate n (Prim "drop") ++ [Prim "pass"]

    rewriteStage atoms0 = do
      let (atoms, open) = case reverse atoms0 of
            (Prim "pass" : rs) -> (reverse rs, True)
            _                  -> (atoms0, False)
      infos <- mapM classify atoms
      let inAs    = [ i | AtomInfo i _ _ <- infos ]
          offsets = init (scanl (+) 0 inAs)
          inserts = [ (off + rel, idx)
                    | (AtomInfo _ specs _, off) <- zip infos offsets
                    , (rel, idx) <- specs ]
          -- targets are final-layout depths above the block; inserting
          -- in ascending order, everything below a target is already in
          -- place when its copy arrives
          fetches = concat [ fetchTo idx (n + tgt) | (tgt, idx) <- inserts ]
          atoms'  = [ a | AtomInfo _ _ a <- infos ]
          stage   = replicate n (Prim "_") ++ atoms' ++ [ Prim "pass" | open ]
          isWire (Prim "_")    = True
          isWire (Prim "pass") = True
          isWire _             = False
      pure (fetches ++ [ stage | not (all isWire stage) ])

    classify :: Term -> Either String AtomInfo
    classify t@(Prim nm)
      | Just i <- elemIndex nm ps = Right (AtomInfo 1 [(0, i)] (Prim "_"))
      | nm == "pass" = Left "reflect: '...' before the end of a stage in an abstraction body"
      | isIntLiteral nm || isFloatLiteral nm || isStrLiteral nm
          || isSymLiteral nm = Right (AtomInfo 0 [] t)
      | Just _ <- finIndex nm = Right (AtomInfo 0 [] t)
      -- an injection is open-arity, hence final in its stage: nothing
      -- to its right needs its width
      | Just _ <- injIndex nm = Right (AtomInfo 0 [] t)
      -- an ENCLOSING binder's parameter: a wire at a level above this
      -- one, so it pushes here and is threaded by whoever owns it
      | nm `elem` outer = Right (AtomInfo 0 [] t)
      | otherwise =
          case M.lookup nm env of
            Nothing -> Left $ "reflect: unknown name in abstraction body: " ++ nm
            -- an open-tailed word is final in its stage, so only its
            -- closed prefix can sit left of anything
            Just (Forall _ _ _ _ _ _ (Arrow i _ _)) ->
              Right (AtomInfo (closedArity i) [] t)
    -- A quotation that mentions a parameter is a CLOSURE, and it is
    -- reified by the exponential's own maps (stage 5a¾).  Compile the
    -- body against a COPY of the block laid deepest INSIDE the quote —
    -- `Fn⟨P ρ0 ⇒ ρ1⟩` — and then bind the copies off the stack with
    -- `capture`, once each.  Every `capture` binds the wire directly
    -- below the Fn, which must be the Fn's own DEEPEST input; so the
    -- block inside the quote is laid in the REVERSE of the block on the
    -- stack, shallowest-outside binding deepest-inside first.  Nothing
    -- downstream changes: the result has the quotation's original type.
    classify t@(Quote b)
      | null (usedIn b) = Right (AtomInfo 0 [] t)
      | otherwise =
          let used = usedIn b
              m    = length used
              -- the block is m wires; the quote pushes on top of it
              capAt j = replicate (m - 1 - j) (Prim "_") ++ [Prim "capture"]
          in do
            inner <- compileAbs env outer (reverse used) b
            let stages = (replicate m (Prim "_") ++ [Quote inner])
                       : [ capAt j | j <- [0 .. m - 1] ]
            pure (AtomInfo m (zip [0 ..] (idxOf used)) (chainTerm stages))
    -- A row that mentions a parameter: distribute a copy of the block
    -- into every track (one `dist` per block wire, shallowest first, so
    -- the block lands in its own order at the bottom of each track),
    -- compile each branch against it, and let each branch drop its own
    -- copy at the end — which is what `compileAbs` already does.  The
    -- row keeps its ORIGINAL type: no `undist` is needed.
    -- WHICH dist: the derived prelude `dist2` for the closed binary row
    -- (that is the theorem, and reflected code should show it), the
    -- generator `#dist:K` for every other width and for a residual —
    -- the two corners 5a¾ pinned as refusals.  `#dist:K` passes the
    -- residual untouched, which is the only thing that CAN be done with
    -- alternatives nobody can name.
    classify t@(Alts cs residual)
      | null (usedIn t) = Right (AtomInfo 1 [] t)
      | otherwise =
          let used = usedIn t
              m    = length used
              dist | residual || length cs /= 2 = Prim (distPrimName (length cs))
                   | otherwise                  = Prim "dist2"
              distAt j = replicate (m - 1 - j) (Prim "_") ++ [dist]
          in do
            cs' <- mapM (compileAbs env outer used) cs
            let stages = [ distAt j | j <- [0 .. m - 1] ]
                      ++ [[Alts cs' residual]]
            pure (AtomInfo (m + 1) (zip [0 ..] (idxOf used)) (chainTerm stages))
    classify (OpenAbs {}) =
      Left "internal: nested abstraction not yet eliminated"
    classify g = groupInfo g

    -- the parameters an atom actually mentions, in first-use order, and
    -- their depths in the block
    usedIn t = nub [ nm | nm <- freeNamesIn t, nm `elem` ps ]
    idxOf us = [ i | Just i <- map (`elemIndex` ps) us ]

    -- a grouped compound: recursively thread the parameters it uses,
    -- which arrive as ITS block, below its own inputs
    groupInfo g = do
      let used = usedIn g
          usedIdx = idxOf used
      Arrow gi _ _ <- inferGroupArrow g
      let gIn = closedArity gi
      if null used
        then Right (AtomInfo gIn [] g)
        else do
          g' <- compileAbs env outer used g
          pure (AtomInfo (length used + gIn)
                         (zip [0 ..] usedIdx)
                         g')

    inferGroupArrow g = do
      let dummy = TV "_p"
          dummyScheme =
            Forall [dummy] [] [] [] [] [] (arrPure SEnd (SCons (TVarTy dummy) SEnd))
          arityEnv = foldr (\nm -> M.insert nm dummyScheme) env (ps ++ outer)
      inferTermIn arityEnv g

openTailedS :: SType -> Bool
openTailedS (SCons _ r)   = openTailedS r
openTailedS (STail _)     = True
openTailedS (SExp _ _ _)  = True   -- unknown width: not a closed stack
openTailedS SEnd          = False

-- Typecheck and run a whole module; main runs on the empty stack.
runModule :: String -> IO (Either String ([Value], [String]))
runModule = runModuleAt []

-- ...with the loader's line map, so a refusal names the file it is in.
runModuleAt :: LineMap -> String -> IO (Either String ([Value], [String]))
runModuleAt lm src = runExceptT $ do
  m <- liftEither (checkModuleAt lm src)
  -- AUDITED MODELS: every law runs before main and must answer true.
  -- A model that fails its theory's laws is not a model, and
  -- saying so at module start is the whole difference between a law
  -- that documents and a law that holds.
  mapM_ (runLaw m) [ (n, t) | (n, _, t) <- modDefs m, isJust (lawParts n) ]
  -- ...and every square a transformation could only decide at the samples.
  -- A square the normalizer PROVED is not sampled again: its law was
  -- generated before the verdict was in, and sampling a proved square
  -- could only weigh two carriers `eq?` has nothing true to say about.
  mapM_ (runSquare m) [ (n, t) | (n, _, t) <- modDefs m
                               , Just (mo, sl) <- [squareParts n]
                               , sampledSquare m mo sl ]
  -- ...and every CHECK a `test` keyword registered (stage 8).  Beside
  -- the laws, for the same reason: a claim a module makes about itself
  -- is worth as much as the moment it is decided, and that moment is
  -- before anything prints.
  mapM_ (runTest m) [ (n, t) | (n, _, t) <- modDefs m
                             , isJust (testParts n) ]
  case modMain m of
    Nothing -> pure ([], [])
    Just (term, arr@(Arrow i o _))
      | closedArity i > 0 ->
          throwError $ "main requires a nonempty input stack: " ++ show arr
      | otherwise -> do
          (out, logs) <- evalTerm (moduleRCtx m) (moduleRunDefs m) M.empty term []
          case desyncError o out of
            Just e  -> throwError e
            Nothing -> pure (out, logs)

-- Run one generated law def; anything but `true` is a module error.
runLaw :: Module -> (String, Term)
       -> ExceptT String IO ()
runLaw m (n, t) = do
  (out, _) <- evalTerm (moduleRCtx m) (moduleRunDefs m) M.empty t []
  case out of
    [VSum 0 []] -> pure ()
    _ ->
      let (inst, lw) = maybe ("?", n) id (lawParts n)
      in throwError $ "law '" ++ lw ++ "' fails for model " ++ inst
                   ++ ": a model must be an audited model of its theory"
                   ++ (if '(' `elem` inst
                         then "  (a model PARAMETERIZED by a model cannot be \
                              \audited once for the family \8212 that needs \
                              \equality modulo the parameter theory's laws, \
                              \which the checker has not got \8212 so its \
                              \laws are checked AT EACH INSTANTIATION, on \
                              \that member's own evidence, and this is the \
                              \first one that named it)"
                         else "")

-- One registered check, run at module start.  Anything but `true` is
-- a module error naming the test.
runTest :: Module -> (String, Term) -> ExceptT String IO ()
runTest m (n, t) = do
  (out, _) <- evalTerm (moduleRCtx m) (moduleRunDefs m) M.empty t []
  case out of
    [VSum 0 []] -> pure ()
    _ -> throwError $ "test '" ++ fromMaybe n (testParts n) ++ "' fails: a "
                   ++ "`test` runs at module start and must answer `true`"

-- Was this square left to the samples?  A transformation the module does not
-- know about (there is none) is sampled, which is what the check did
-- before the verdicts were recorded.
sampledSquare :: Module -> String -> String -> Bool
sampledSquare m mo sl =
  or [ True | mi <- modTransformations m, tiName mi == mo
            , (s, TVSampled _ _ _) <- tiSquares mi, s == sl ]
    || null [ () | mi <- modTransformations m, tiName mi == mo ]

-- One generated square, run at the theory's samples.  A transformation whose
-- square the normalizer could not prove is checked here instead, and a
-- failure names the slot whose square does not commute.
runSquare :: Module -> (String, Term) -> ExceptT String IO ()
runSquare m (n, t) = do
  (out, _) <- evalTerm (moduleRCtx m) (moduleRunDefs m) M.empty t []
  case out of
    [VSum 0 []] -> pure ()
    _ ->
      let (mo, sl) = fromMaybe ("?", n) (squareParts n)
          -- the comparison went through the theory's exit unless the
          -- theory declares none, and then it weighed the two carriers
          -- themselves: say so, because `eq?` on a carrier holding a
          -- quotation is syntactic and answers `false` for two
          -- extensionally equal continuations
          bare = or [ sl `elem` tiNoExit mi | mi <- modTransformations m
                                            , tiName mi == mo ]
      in throwError $ "transformation " ++ mo ++ ": the square for slot '"
                   ++ sl ++ "' does not commute at the theory's samples "
                   ++ "\8212 a transformation between models is a "
                   ++ "homomorphism, slot by slot"
                   ++ (if bare
                         then ".  The two carriers were compared with `eq?` "
                               ++ "directly, because the theory declares no "
                               ++ "exit whose input FITS this slot's result "
                               ++ "\8212 an exit at `k(Int, Int)` does not "
                               ++ "reach the hom-object at another pair of "
                               ++ "stacks. "
                               ++ "If the carrier holds a function, `eq?` is "
                               ++ "syntactic: declare an exit `observe` in "
                               ++ "the theory at the shape this slot leaves"
                         else "")

-- A scheme's runtime shape: how many wires it consumes, and whether it
-- wants the whole remaining segment.  Shared by the runtime scope
-- builder and the elaboration-time one.
arityOf :: Scheme -> Int
arityOf (Forall _ _ _ _ _ _ (Arrow i _ _)) = closedArity i

openOf :: Scheme -> Bool
openOf (Forall _ _ _ _ _ _ (Arrow i _ _)) = openTailed i

openTailed :: SType -> Bool
openTailed (SCons _ rest) = openTailed rest
openTailed (STail _)      = True
openTailed (SExp _ _ _)   = True   -- erased width: needs the whole segment
openTailed SEnd           = False

-- adjacent pairs of a segment (bases of width 2 come interleaved)
chunk2 :: [a] -> [(a, a)]
chunk2 (x : y : rest) = (x, y) : chunk2 rest
chunk2 _              = []
