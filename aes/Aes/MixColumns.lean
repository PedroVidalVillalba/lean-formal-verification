import Aes.Common
import Mathlib.Data.Matrix.Basic

set_option linter.style.header false
set_option linter.style.whitespace false

/-!
# `MixColumns` / `InvMixColumns`

## Proof strategy

`GF256` is a `Field`, so `Matrix (Fin 4) (Fin 4) GF256` is a module over it
and Mathlib's `Matrix.mulVec_mulVec` / `Matrix.one_mulVec` apply directly.

We verify `invMixMatrix * mixMatrix = 1` by `native_decide`; the concrete
matrix entries are `GF256` literals, so `native_decide` evaluates using
the `GF256` `Mul` and `Add` instances (polynomial multiplication and XOR)
rather than the raw `UInt8` arithmetic.
-/

open GF256 Matrix

-- ── MixColumns matrices ───────────────────────────────────────────────────────

/-- Forward MixColumns matrix (FIPS 197, §5.1.3). -/
def mixMatrix : Matrix (Fin 4) (Fin 4) GF256 :=
  ![![2, 3, 1, 1],
    ![1, 2, 3, 1],
    ![1, 1, 2, 3],
    ![3, 1, 1, 2]]

/-- Inverse MixColumns matrix (FIPS 197, §5.3.3). -/
def invMixMatrix : Matrix (Fin 4) (Fin 4) GF256 :=
  ![![0x0e, 0x0b, 0x0d, 0x09],
    ![0x09, 0x0e, 0x0b, 0x0d],
    ![0x0d, 0x09, 0x0e, 0x0b],
    ![0x0b, 0x0d, 0x09, 0x0e]]

/-- M⁻¹ · M = I  (evaluated using GF(2⁸) arithmetic). -/
private lemma invMix_mul_mix :
    invMixMatrix * mixMatrix = (1 : Matrix (Fin 4) (Fin 4) GF256) := by
  decide

-- ── Column operations ─────────────────────────────────────────────────────────

def mixCol    (v : Fin 4 → GF256) : Fin 4 → GF256 := mixMatrix    *ᵥ v
def invMixCol (v : Fin 4 → GF256) : Fin 4 → GF256 := invMixMatrix *ᵥ v

theorem invMixCol_mixCol (v : Fin 4 → GF256) : invMixCol (mixCol v) = v := by
  unfold invMixCol mixCol
  rw [mulVec_mulVec, invMix_mul_mix, one_mulVec]

-- ── State-level wrappers ──────────────────────────────────────────────────────

def mixColumns    (s : State) : State := fun r c => mixCol    (fun row => s row c) r
def invMixColumns (s : State) : State := fun r c => invMixCol (fun row => s row c) r

theorem invMixColumns_mixColumns (s : State) : invMixColumns (mixColumns s) = s := by
  funext r c; exact congrFun (invMixCol_mixCol (fun row => s row c)) r
