import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Field.Basic

set_option linter.style.header false
set_option linter.style.nativeDecide false

/-!
# `GF256` — the Galois field GF(2⁸)

`GF256` is a newtype around `UInt8` with:
- `+` = bitwise XOR  (proved via `BitVec` lemmas from Lean's `Init` library)
- `*` = AES polynomial multiplication mod `x⁸+x⁴+x³+x+1`

## Proof strategy for the `Field` instance

The *additive* group axioms all follow from the corresponding `BitVec.xor_*`
lemmas in Lean 4's `Init` library, since `GF256.add` is definitionally
`fun a b => ⟨a.val ^^^ b.val⟩` and `UInt8.xor` unfolds to `BitVec.xor`.
No `native_decide` is needed for any additive axiom.

The *multiplicative* axioms are checked by exhaustive `native_decide` over
`Fin 256`.  The alternative — transporting through the isomorphism
`GF256 ≅ AdjoinRoot (ZMod 2) (X^8+X^4+X^3+X+1)` — would require proving
that `rawMul` agrees with polynomial multiplication modulo the AES
irreducible, which is itself a 256-case check.  The `native_decide` approach
is therefore not just simpler but equally informative.
-/

-- ─────────────────────────────────────────────────────────────────────────
-- §1  Raw UInt8 helpers (private)
-- ─────────────────────────────────────────────────────────────────────────

private def xtime (b : UInt8) : UInt8 :=
  if b &&& 0x80 = 0 then b <<< 1 else (b <<< 1) ^^^ 0x1b

private def mulAux : UInt8 → UInt8 → UInt8 → ℕ → UInt8
  | _, _, acc, 0 => acc
  | a, b, acc, n + 1 =>
    mulAux (xtime a) (b >>> 1) (if b &&& 1 ≠ 0 then acc ^^^ a else acc) n

private def rawMul (a b : UInt8) : UInt8 := mulAux a b 0 8

private def rawInv (b : UInt8) : UInt8 :=
  if b = 0 then 0 else
    let b2 := rawMul b b;     let b4  := rawMul b2  b2
    let b8 := rawMul b4 b4;   let b16 := rawMul b8  b8
    let b32 := rawMul b16 b16; let b64 := rawMul b32 b32
    let b128 := rawMul b64 b64
    rawMul b128 <| rawMul b64 <| rawMul b32 <|
      rawMul b16 <| rawMul b8 <| rawMul b4 b2

-- ─────────────────────────────────────────────────────────────────────────
-- §2  GF256 type and operations
-- ─────────────────────────────────────────────────────────────────────────

/-- An element of GF(2⁸): a byte with XOR as addition and AES polynomial
    multiplication as multiplication. -/
structure GF256 where
  val : UInt8
  deriving DecidableEq, Repr

namespace GF256

@[ext] theorem ext : ∀ {a b : GF256}, a.val = b.val → a = b
  | ⟨_⟩, ⟨_⟩, rfl => rfl

instance : Zero    GF256 := ⟨⟨0⟩⟩
instance : One     GF256 := ⟨⟨1⟩⟩
instance : Add     GF256 := ⟨fun a b => ⟨a.val ^^^ b.val⟩⟩
instance : Neg     GF256 := ⟨id⟩                              -- char 2: -a = a
instance : Sub     GF256 := ⟨fun a b => ⟨a.val ^^^ b.val⟩⟩   -- a - b = a + b
instance : Mul     GF256 := ⟨fun a b => ⟨rawMul a.val b.val⟩⟩
instance : Inv     GF256 := ⟨fun a   => ⟨rawInv a.val⟩⟩
instance : OfNat GF256 n := ⟨⟨(OfNat.ofNat n : UInt8)⟩⟩

private def gfNsmul : ℕ → GF256 → GF256
  | 0,     _ => 0
  | n + 1, x => gfNsmul n x + x

private def gfZsmul : ℤ → GF256 → GF256
  | Int.ofNat n,   x => gfNsmul n x
  | Int.negSucc n, x => gfNsmul (n + 1) x

-- ─────────────────────────────────────────────────────────────────────────
-- §3  Additive group axioms — lifted from BitVec
--
-- `GF256.add a b` is definitionally `⟨⟨a.val.toBitVec ^^^ b.val.toBitVec⟩⟩`.
-- After `GF256.ext` each goal is a statement about `BitVec 8` XOR, which
-- Lean 4's `Init.Data.BitVec.Lemmas` resolves directly.
-- ─────────────────────────────────────────────────────────────────────────


-- ── UInt8 XOR helpers ─────────────────────────────────────────────────────
-- UInt8 = { val : BitVec 8 }. XOR reduces to BitVec.xor pointwise.
-- BitVec.xor_assoc and xor_comm are not @[simp] so we name them;
-- xor_self/xor_zero/zero_xor are @[simp] so plain `simp` suffices.

private lemma u8_ext {a b : UInt8} (h : a.toBitVec = b.toBitVec) : a = b := by
  cases a; cases b; simp_all

private lemma u8_xor_assoc (a b c : UInt8) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) :=
  u8_ext (BitVec.xor_assoc _ _ _)

private lemma u8_xor_comm (a b : UInt8) : a ^^^ b = b ^^^ a :=
  u8_ext (BitVec.xor_comm _ _)

private lemma u8_xor_self (a : UInt8) : a ^^^ a = 0 := by apply u8_ext; simp
private lemma u8_xor_zero (a : UInt8) : a ^^^ 0 = a := by apply u8_ext; simp
private lemma u8_zero_xor (a : UInt8) : 0 ^^^ a = a := by apply u8_ext; simp

/-- `(a ^^^ b) ^^^ b = a` — XOR with the same value cancels. -/
private lemma u8_xor_cancel (a b : UInt8) : (a ^^^ b) ^^^ b = a := by
  rw [u8_xor_assoc, u8_xor_self, u8_xor_zero]



-- One-layer unwrapping: UInt8.xor → BitVec.xor
lemma add_assoc (a b c : GF256) : a + b + c = a + (b + c) :=
  GF256.ext (u8_xor_assoc a.val b.val c.val)

lemma zero_add (a : GF256) : 0 + a = a :=
  GF256.ext (u8_zero_xor a.val)

lemma add_zero (a : GF256) : a + 0 = a :=
  GF256.ext (u8_xor_zero a.val)

lemma add_comm (a b : GF256) : a + b = b + a :=
  GF256.ext (u8_xor_comm a.val b.val)

-- In characteristic 2: -a = a, so -a + a = a + a = a ^^^ a = 0
lemma neg_add_cancel (a : GF256) : -a + a = 0 :=
  GF256.ext (u8_xor_self a.val)

lemma sub_eq_add_neg (a b : GF256) : a - b = a + (-b) := rfl

lemma add_cancel (a b : GF256) : (a + b) + b = a :=
  GF256.ext (u8_xor_cancel a.val b.val)

-- ─────────────────────────────────────────────────────────────────────────
-- §4  Multiplicative axioms — native_decide over Fin 256
-- ─────────────────────────────────────────────────────────────────────────

-- Fin 256 ↔ GF256 (private; public version in §6)
private def ofFin (i : Fin 256) : GF256 := ⟨⟨⟨i⟩⟩⟩
private def toFin (x : GF256) : Fin 256 := x.val.toBitVec.toFin

@[simp] private lemma ofFin_toFin (x : GF256) : ofFin (toFin x) = x := rfl
@[simp] private lemma toFin_ofFin (i : Fin 256) : toFin (ofFin i) = i := rfl

private def lift1 {P : GF256 → Prop}
    (h : ∀ i, P (ofFin i)) (x : GF256) : P x :=
  ofFin_toFin x ▸ h (toFin x)

private def lift2 {P : GF256 → GF256 → Prop}
    (h : ∀ i j, P (ofFin i) (ofFin j)) (x y : GF256) : P x y :=
  ofFin_toFin x ▸ ofFin_toFin y ▸ h (toFin x) (toFin y)

private def lift3 {P : GF256 → GF256 → GF256 → Prop}
    (h : ∀ i j k, P (ofFin i) (ofFin j) (ofFin k)) (x y z : GF256) : P x y z :=
  ofFin_toFin x ▸ ofFin_toFin y ▸ ofFin_toFin z ▸ h (toFin x) (toFin y) (toFin z)

private lemma ax_mul_assoc : ∀ a b c : Fin 256,
    ofFin a * ofFin b * ofFin c = ofFin a * (ofFin b * ofFin c) := by
  native_decide

private lemma ax_one_mul : ∀ a : Fin 256,
    (1 : GF256) * ofFin a = ofFin a := by native_decide

private lemma ax_mul_one : ∀ a : Fin 256,
    ofFin a * (1 : GF256) = ofFin a := by native_decide

private lemma ax_left_distrib : ∀ a b c : Fin 256,
    ofFin a * (ofFin b + ofFin c) =
    ofFin a * ofFin b + ofFin a * ofFin c := by native_decide

private lemma ax_right_distrib : ∀ a b c : Fin 256,
    (ofFin a + ofFin b) * ofFin c =
    ofFin a * ofFin c + ofFin b * ofFin c := by native_decide

private lemma ax_mul_comm : ∀ a b : Fin 256,
    ofFin a * ofFin b = ofFin b * ofFin a := by native_decide

private lemma ax_zero_mul : ∀ a : Fin 256,
    (0 : GF256) * ofFin a = 0 := by native_decide

private lemma ax_mul_zero : ∀ a : Fin 256,
    ofFin a * (0 : GF256) = 0 := by native_decide

-- mul_inv_cancel requires a bespoke transport since the predicate is
-- (a ≠ 0 → a * a⁻¹ = 1), i.e., it is not of the form P a for a single P.
private lemma ax_mul_inv : ∀ a : Fin 256,
    ofFin a ≠ 0 → ofFin a * (ofFin a)⁻¹ = 1 := by native_decide

private lemma ax_inv_zero : (0 : GF256)⁻¹ = 0 := by native_decide

private lemma ax_nontrivial : (0 : GF256) ≠ 1 := by decide

-- ─────────────────────────────────────────────────────────────────────────
-- §5  Field instance
-- ─────────────────────────────────────────────────────────────────────────

instance : CommRing GF256 where
  add           := (· + ·)
  add_assoc     := add_assoc
  zero          := 0
  zero_add      := zero_add
  add_zero      := add_zero
  add_comm      := add_comm
  neg           := Neg.neg
  neg_add_cancel := neg_add_cancel
  sub           := HSub.hSub
  sub_eq_add_neg := sub_eq_add_neg
  nsmul         := gfNsmul
  nsmul_zero    := fun _ => rfl
  nsmul_succ    := fun _ _ => rfl
  zsmul         := gfZsmul
  zsmul_zero'   := fun _ => rfl
  zsmul_succ'   := fun _ _ => rfl
  zsmul_neg'    := fun _ _ => rfl
  mul           := (· * ·)
  mul_assoc     := lift3 ax_mul_assoc
  one           := 1
  one_mul       := lift1 ax_one_mul
  mul_one       := lift1 ax_mul_one
  left_distrib  := lift3 ax_left_distrib
  right_distrib := lift3 ax_right_distrib
  mul_comm      := lift2 ax_mul_comm
  zero_mul      := lift1 ax_zero_mul
  mul_zero      := lift1 ax_mul_zero

-- `Nontrivial` must come before `Field` (it is a precondition)
instance : Nontrivial GF256 := ⟨0, 1, ax_nontrivial⟩

instance : Field GF256 :=
  { (inferInstance : CommRing GF256) with
    inv := Inv.inv
    mul_inv_cancel := fun x hx => by
      have hx' : ofFin (toFin x) ≠ 0 := ofFin_toFin x ▸ hx
      exact ofFin_toFin x ▸ ax_mul_inv (toFin x) hx'
    inv_zero      := ax_inv_zero
    nnqsmul := _
    qsmul := _
  }

-- ─────────────────────────────────────────────────────────────────────────
-- §6  Public transport helpers (Fin 256 ↔ GF256)
-- ─────────────────────────────────────────────────────────────────────────

/-- Coerce a `GF256` to `Fin 256` (for `native_decide` in downstream files). -/
def u8ToFin (b : GF256) : Fin 256 := toFin b
/-- Coerce a `Fin 256` to `GF256`. -/
def finToGF (i : Fin 256) : GF256 := ofFin i

@[simp] lemma finToGF_u8ToFin (b : GF256) : finToGF (u8ToFin b) = b := rfl
@[simp] lemma u8ToFin_finToGF (i : Fin 256) : u8ToFin (finToGF i) = i := rfl

-- ─────────────────────────────────────────────────────────────────────────
-- §7  Byte ↔ bit-vector bijection (for the AES S-box)
-- ─────────────────────────────────────────────────────────────────────────

abbrev ByteVec := Fin 8 → ZMod 2

def toBV (b : GF256) : ByteVec :=
  fun i => ((b.val.toNat >>> i.val &&& 1 : ℕ) : ZMod 2)

def fromBV (v : ByteVec) : GF256 :=
  ⟨UInt8.ofNat (∑ i : Fin 8, ZMod.val (v i) * 2 ^ (i : ℕ))⟩

lemma fromBV_toBV (b : GF256) : fromBV (toBV b) = b := by
  have h : ∀ i : Fin 256, fromBV (toBV (finToGF i)) = finToGF i := by
    native_decide
  simpa using h (u8ToFin b)

lemma toBV_fromBV : ∀ v : ByteVec, toBV (fromBV v) = v := by native_decide

/-- GF(2⁸) multiplicative inverse on bit-vectors.
    Defined as the field inverse of the reassembled byte. -/
def gf256InvBV (v : ByteVec) : ByteVec := toBV (fromBV v)⁻¹

theorem gf256InvBV_involutive (v : ByteVec) : gf256InvBV (gf256InvBV v) = v := by
  simp only [gf256InvBV]
  rw [fromBV_toBV, inv_inv, toBV_fromBV]

end GF256
