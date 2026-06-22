import Aes.SubBytes
import Aes.ShiftRows
import Aes.MixColumns
import Aes.AddRoundKey
import Aes.KeySchedule

set_option linter.style.whitespace false
set_option linter.style.header false
set_option linter.style.nativeDecide false

/-!
# AES-128: encrypt, decrypt, and correctness

## Round structure

### Encryption (FIPS 197 §5.1)
```
encRound rk s      = addRoundKey rk (mixColumns (shiftRows (subBytes s)))
encFinalRound rk s = addRoundKey rk (shiftRows (subBytes s))

aesEncrypt key p =
  encFinalRound rk[10]
    (encRounds ek 9 (addRoundKey rk[0] p))
```
where `encRounds ek n` applies `encRound rk[1]` … `encRound rk[n]` in order.

### Decryption (FIPS 197 §5.3, direct inverse)
```
decRound rk s      = invSubBytes (invShiftRows (invMixColumns (addRoundKey rk s)))
decFinalRound rk s = invSubBytes (invShiftRows (addRoundKey rk s))

aesDecrypt key c =
  addRoundKey rk[0]
    (decRounds ek 9 (decFinalRound rk[10] c))
```
where `decRounds ek n` applies `decRound rk[n]` … `decRound rk[1]` in order
(the reverse of the enc order, so each dec round sits directly outside the
corresponding enc round in the composed computation).

## Why recursive helpers instead of `foldl`

`foldl` over `List.finRange` grows the list by *prepending* (via `Fin.succ`),
so `List.finRange_succ` gives `⟨0⟩ :: map Fin.succ rest`.  This means the
induction step isolates the *first* enc round (`rk[1]`) while the matching
dec round (`rk[1]`) ends up *last* — the two sides never meet directly, and
`rw [decRound_encRound]` cannot fire.

With `encRounds`/`decRounds` defined by recursion on `n`, the inductive step
always exposes the pair `decRound rk[n+1] (encRound rk[n+1] …)` at the top
level, so `decRound_encRound` applies immediately.

## Correctness sketch

```
decRounds ek (n+1) (encRounds ek (n+1) s)
  = decRounds ek n (decRound rk[n+1] (encRound rk[n+1] (encRounds ek n s)))
  = decRounds ek n (encRounds ek n s)   -- decRound_encRound
  = s                                    -- induction hypothesis
```
-/

-- ── Round definitions ─────────────────────────────────────────────────────────

/-- One inner encryption round: SubBytes → ShiftRows → MixColumns → AddRoundKey -/
def encRound (rk : State) (s : State) : State :=
  addRoundKey rk (mixColumns (shiftRows (subBytes s)))

/-- Final encryption round (no MixColumns): SubBytes → ShiftRows → AddRoundKey -/
def encFinalRound (rk : State) (s : State) : State :=
  addRoundKey rk (shiftRows (subBytes s))

/-- One inner decryption round (direct inverse of `encRound`):
    AddRoundKey → InvMixColumns → InvShiftRows → InvSubBytes.
    `addRoundKey` is innermost so it directly cancels its enc counterpart. -/
def decRound (rk : State) (s : State) : State :=
  invSubBytes (invShiftRows (invMixColumns (addRoundKey rk s)))

/-- First decryption round (inverse of `encFinalRound`):
    AddRoundKey → InvShiftRows → InvSubBytes. -/
def decFinalRound (rk : State) (s : State) : State :=
  invSubBytes (invShiftRows (addRoundKey rk s))

-- ── Recursive n-round helpers ─────────────────────────────────────────────────

/-- Apply `encRound` with keys `rk[1]`, `rk[2]`, …, `rk[n]` in order. -/
private def encRounds (ek : Fin 44 → AESWord) : ∀ (n : ℕ), n ≤ 9 → State → State
  | 0, _, s => s
  | n + 1, hn, s => encRound (roundKey ek ⟨n + 1, by omega⟩) (encRounds ek n (by omega) s)

/-- Apply `decRound` with keys `rk[n]`, `rk[n-1]`, …, `rk[1]` in order.
    (Equivalent to applying `decRound rk[n+1]` first, then `decRounds ek n`.) -/
private def decRounds (ek : Fin 44 → AESWord) : ∀ (n : ℕ), n ≤ 9 → State → State
  | 0, _, s => s
  | n + 1, hn, s => decRounds ek n (by omega) (decRound (roundKey ek ⟨n + 1, by omega⟩) s)

-- ── Encrypt / Decrypt ─────────────────────────────────────────────────────────

/-- AES-128 encryption (FIPS 197 §5.1). -/
def aesEncrypt (key : Fin 4 → AESWord) (p : State) : State :=
  let ek := keyExpansion key
  encFinalRound (roundKey ek 10) (encRounds ek 9 (by omega) (addRoundKey (roundKey ek 0) p))

/-- AES-128 decryption (FIPS 197 §5.3, direct inverse). -/
def aesDecrypt (key : Fin 4 → AESWord) (c : State) : State :=
  let ek := keyExpansion key
  addRoundKey (roundKey ek 0) (decRounds ek 9 (by omega) (decFinalRound (roundKey ek 10) c))

-- ── Per-round cancellation ────────────────────────────────────────────────────

theorem decRound_encRound (rk s : State) :
    decRound rk (encRound rk s) = s := by
  change invSubBytes (invShiftRows (invMixColumns
         (addRoundKey rk (addRoundKey rk (mixColumns (shiftRows (subBytes s))))))) = s
  rw [addRoundKey_involutive, invMixColumns_mixColumns,
      invShiftRows_shiftRows, invSubBytes_subBytes]

theorem decFinalRound_encFinalRound (rk s : State) :
    decFinalRound rk (encFinalRound rk s) = s := by
  change invSubBytes (invShiftRows
         (addRoundKey rk (addRoundKey rk (shiftRows (subBytes s))))) = s
  rw [addRoundKey_involutive, invShiftRows_shiftRows, invSubBytes_subBytes]

-- ── Loop cancellation ─────────────────────────────────────────────────────────

/-- `n` dec rounds (keys `rk[n]`…`rk[1]`) cancel `n` enc rounds (keys `rk[1]`…`rk[n]`).
    Induction on `n`: the step peels off the matching pair at the boundary. -/
private lemma decRounds_encRounds
    (ek : Fin 44 → AESWord) (s : State) (n : ℕ) (hn : n ≤ 9) :
    decRounds ek n hn (encRounds ek n hn s) = s := by
  induction n with
  | zero => simp [encRounds, decRounds]
  | succ m ih =>
    simp only [encRounds, decRounds]
    rw [decRound_encRound]
    exact ih (Nat.le_of_succ_le hn)

-- ── Main correctness theorem ──────────────────────────────────────────────────

/-- **AES-128 correctness**: `aesDecrypt key (aesEncrypt key p) = p`. -/
theorem aesDecrypt_aesEncrypt (key : Fin 4 → AESWord) (p : State) :
    aesDecrypt key (aesEncrypt key p) = p := by
  simp only [aesDecrypt, aesEncrypt]
  set ek := keyExpansion key
  rw [decFinalRound_encFinalRound,
      decRounds_encRounds ek _ 9 le_rfl,
      addRoundKey_involutive]
