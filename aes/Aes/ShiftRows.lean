import Aes.Common

set_option linter.style.header false
set_option linter.style.whitespace false

-- ── Fin 4 arithmetic helpers ──────────────────────────────────────────────────

private lemma fin4_sub_add_cancel (r c : Fin 4) : c - r + r = c := by
  fin_cases r <;> fin_cases c <;> rfl

private lemma fin4_add_sub_cancel (r c : Fin 4) : c + r - r = c := by
  fin_cases r <;> fin_cases c <;> rfl

-- ── ShiftRows / InvShiftRows ──────────────────────────────────────────────────

def shiftRows    (s : State) : State := fun r c => s r (c + r)
def invShiftRows (s : State) : State := fun r c => s r (c - r)

theorem invShiftRows_shiftRows (s : State) : invShiftRows (shiftRows s) = s := by
  funext r c; simp only [invShiftRows, shiftRows]; congr 1; exact fin4_sub_add_cancel r c

theorem shiftRows_invShiftRows (s : State) : shiftRows (invShiftRows s) = s := by
  funext r c; simp only [shiftRows, invShiftRows]; congr 1; exact fin4_add_sub_cancel r c
