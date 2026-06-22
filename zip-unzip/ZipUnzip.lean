/-!
# Unzip-Zip Identity

This file proves that `List.unzip` followed by `List.zip` is the identity
on `List (α × β)`. That is, for any `l : List (α × β)`:

  `l.unzip.1.zip l.unzip.2 = l`

or equivalently, using `Function.uncurry`:

  `(Function.uncurry List.zip) (List.unzip l) = l`

This is the formalization of the mathematical statement:

  ∀ l : List (α × β),  List.zip.uncurry (List.unzip l) = l

**Note**: In Mathlib this theorem exists as `List.zip_unzip`. This file
proves it from first principles using only Lean 4 core, without importing
Mathlib, to illustrate the proof methodology.

## Background

The two relevant functions are:

- `List.unzip : List (α × β) → List α × List β`
  Splits a list of pairs into a pair of lists. Defined by structural
  recursion:
  - `[].unzip              = ([], [])`
  - `((a, b) :: tl).unzip = (a :: tl.unzip.1, b :: tl.unzip.2)`

- `List.zip : List α → List β → List (α × β)`
  Merges two lists into a list of pairs, truncating to the shorter one.
  Lean 4 implements it as `List.zipWith Prod.mk`, defined by:
  - `[].zipWith f _             = []`
  - `_.zipWith f []             = []`
  - `(a :: as).zipWith f (b :: bs) = f a b :: as.zipWith f bs`

## Proof strategy

By structural induction on `l`.

- **Nil case**: `[].unzip = ([], [])` and `[].zip [] = []`,
  so both sides are `[]`. This is proved by `rfl`.

- **Cons case**: For `l = (a, b) :: tl`, the definitions of `List.unzip`
  and `List.zip`/`List.zipWith` reduce the left-hand side:

  `((a, b) :: tl).unzip.1.zip ((a, b) :: tl).unzip.2`
  `= (a :: tl.unzip.1).zip (b :: tl.unzip.2)`   -- by def. of `unzip`
  `= (a, b) :: tl.unzip.1.zip tl.unzip.2`        -- by def. of `zip`
  `= (a, b) :: tl`                               -- by the inductive hypothesis

  The last step is wrapped by `congrArg ((a, b) :: ·)`.
-/

universe u v

namespace ZipUnzip

def List.zip : List α → List β → List (α × β)
  | [], _ => []
  | _, [] => []
  | a :: as, b :: bs => (a, b) :: zip as bs

def List.unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (a, b) :: tail =>
      let unzipped := unzip tail
      (a :: unzipped.fst, b :: unzipped.snd)

/-!
## Tactic-mode proof (pedagogical)

The tactic proof makes each step explicit and is easier to read for those
unfamiliar with Lean.
-/

/-- **Unzip-Zip Identity** (tactic proof).

    For any list of pairs `l`, splitting it into component lists with
    `List.unzip` and merging them back with `List.zip` recovers `l`. -/
theorem zip_unzip_tac {α : Type u} {β : Type v} :
    ∀ (l : List (α × β)), l.unzip.1.zip l.unzip.2 = l := by
  intro l
  induction l with
  | nil =>
    -- [].unzip = ([], [])  and  [].zip [] = []  both hold by definition.
    rfl
  | cons hd tl ih =>
    -- Decompose the head pair into its two components.
    obtain ⟨a, b⟩ := hd
    -- After matching (a, b), the definitions of `List.unzip` and `List.zip`
    -- reduce the left-hand side to `(a, b) :: tl.unzip.1.zip tl.unzip.2`
    -- definitionally.  The inductive hypothesis
    --   ih : tl.unzip.1.zip tl.unzip.2 = tl
    -- then closes the goal via congruence.
    exact congrArg ((a, b) :: ·) ih

/-!
## Term-mode proof (concise)

The same result written in term mode.  Lean 4's definitional reduction makes
the proof a two-liner: `rfl` for the nil case and a single `congrArg` call
for the cons case.
-/

/-- **Unzip-Zip Identity** (term-mode proof).

    Same statement as `zip_unzip_tac`; this version uses term-mode pattern
    matching to expose the recursive structure more directly. -/
theorem zip_unzip {α : Type u} {β : Type v} :
    ∀ (l : List (α × β)), l.unzip.1.zip l.unzip.2 = l
  | []           => rfl
  | (a, b) :: tl => congrArg ((a, b) :: ·) (zip_unzip tl)

end ZipUnzip

/-!
## Quick sanity check

The following `#eval` commands verify the theorem on small concrete inputs.
They are not part of the formal proof but help build intuition.
-/

-- A list of (Nat × Char) pairs
#eval
  let l : List (Nat × Char) := [(1, 'a'), (2, 'b'), (3, 'c')]
  l.unzip.1.zip l.unzip.2 = l
  -- Expected: [(1, 'a'), (2, 'b'), (3, 'c')]

-- Empty list (nil case)
#eval
  let l : List (Nat × Nat) := []
  l.unzip.1.zip l.unzip.2 = l
  -- Expected: []

-- Singleton list (one cons, one nil)
#eval
  let l : List (Bool × Nat) := [(true, 42)]
  l.unzip.1.zip l.unzip.2 = l
  -- Expected: [(true, 42)]
