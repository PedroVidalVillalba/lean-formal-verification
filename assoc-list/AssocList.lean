/-!
# A verified finite map as an association list

This file gives a small example of **proof-oriented programming** in Lean:
we define a simple map datatype, implement lookup and insertion, and then
prove the key correctness properties of the implementation.

The example is intentionally lightweight.  A real hash table would require
additional invariants about buckets, hashing, resizing, and collisions.
An association list isolates the core dictionary behavior first, making it a
better teaching example for an early project milestone.

## Main ideas

- `AssocList α β` is represented as `List (α × β)`.
- `get? m k` searches the list for the first pair whose key is `k`.
- `insert m k v` overwrites the value of `k` if `k` is already present;
  otherwise it appends a new binding at the end.
- The central theorem is `get?_insert`, stating that looking up a key right
  after inserting it returns the inserted value.

This illustrates a common verification workflow:

1. Write a simple executable definition.
2. State the intended behavior as theorems.
3. Prove the theorems by induction and case analysis.
4. Use the proved theorems as a specification layer for later developments.
-/

universe u v

namespace AssocListMap

/-- A finite map represented as an association list. -/
abbrev AssocList (α : Type u) (β : Type v) := List (α × β)

variable {α : Type u} {β : Type v}

namespace AssocList

variable [DecidableEq α]

/-- Lookup in an association list.  Returns the first value whose key matches. -/
def get? : AssocList α β → α → Option β
  | [], _ => none
  | (k', v') :: xs, k =>
      if k = k' then
        some v'
      else
        get? xs k

/-- Insert into an association list.

If the key is already present, overwrite its first occurrence.
If the key is absent, append a new binding at the end. -/
def insert : AssocList α β → α → β → AssocList α β
  | [], k, v => [(k, v)]
  | (k', v') :: xs, k, v =>
      if k = k' then
        (k, v) :: xs
      else
        (k', v') :: insert xs k v


/-- Lookup in the empty map returns `none`. -/
@[simp] theorem get?_nil (k : α) :
    get? ([] : AssocList α β) k = none := by
  rfl

/-- If insertion happens into the empty map, the resulting map is a singleton. -/
@[simp] theorem insert_nil (k : α) (v : β) :
    insert ([] : AssocList α β) k v = [(k, v)] := by
  rfl


/-- After inserting a key-value pair, looking up that key returns the value just inserted. -/
theorem get?_insert (m : AssocList α β) (k : α) (v : β) :
    get? (insert m k v) k = some v := by
  induction m with
  | nil =>
      simp [insert, get?]
  | cons hd tl ih =>
      obtain ⟨k', v'⟩ := hd
      by_cases h : k = k'
      · simp [insert, get?, h]
      · simp [insert, get?, h, ih]

/-- Inserting at one key does not affect lookup at a different key. -/
theorem get?_insert_ne (m : AssocList α β) {k₁ k₂ : α} (v : β) (h : k₁ ≠ k₂) :
    get? (insert m k₁ v) k₂ = get? m k₂ := by
  induction m with
  | nil => simp [insert, get?, h.symm]
  | cons hd tl ih =>
      obtain ⟨k', v'⟩ := hd
      by_cases h1 : k₁ = k'
      · by_cases h2 : k₂ = k'
        · subst h2
          contradiction
        · simp [insert, get?, h1, h2]
      · by_cases h2 : k₂ = k'
        · simp [insert, get?, h1, h2]
        · simp [insert, get?, h1, h2, ih]

/-- A small extensionality principle for maps represented as association lists:
if all lookups agree, the observable map behavior agrees.  This is not equality
of lists, but equality of the lookup interface. -/
def MapsToSame (m₁ m₂ : AssocList α β) : Prop :=
  ∀ k, get? m₁ k = get? m₂ k

/-- Inserting the same key and value twice does not change the observable lookup behavior. -/
theorem mapsToSame_insert_insert (m : AssocList α β) (k : α) (v : β) :
    MapsToSame (insert (insert m k v) k v) (insert m k v) := by
  intro k'
  by_cases h : k = k'
  · -- Pos case: k = k', substitute and apply get?_insert twice.
    subst h
    simp [get?_insert]
  · -- Neg case: h : k ≠ k', exactly the right form for get?_insert_ne.
    rw [get?_insert_ne _ _ h]
    -- Goal is now: get? (insert m k v) k' = get? (insert m k v) k'

end AssocList

end AssocListMap

/-!
## Examples

These evaluations are only sanity checks.  The real guarantees come from the
proofs above.
-/

open AssocListMap
open AssocListMap.AssocList

#eval get? ([] : AssocList String Nat) "x"
#eval get? (insert ([] : AssocList String Nat) "x" 7) "x"
#eval get? (insert (insert ([] : AssocList String Nat) "x" 7) "y" 11) "y"
#eval get? (insert (insert ([] : AssocList String Nat) "x" 7) "x" 42) "x"
