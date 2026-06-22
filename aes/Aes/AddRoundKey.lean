import Aes.Common

set_option linter.style.header false

/-!
# `AddRoundKey`

XOR each state byte with the corresponding round key byte (addition in GF256).
Since `(a ^^^ k) ^^^ k = a`, this operation is its own inverse (char GF256 = 2).
-/

def addRoundKey (k s : State) : State := fun r c => s r c + k r c

theorem addRoundKey_involutive (k s : State) : addRoundKey k (addRoundKey k s) = s := by
  funext r c; simp [addRoundKey, GF256.add_cancel]
