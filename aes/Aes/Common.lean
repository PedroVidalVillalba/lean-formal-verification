import Aes.GF256

set_option linter.style.header false

/-- The AES state: a 4×4 matrix of GF(2⁸) elements. -/
abbrev State := Fin 4 → Fin 4 → GF256

/-- A 32-bit AES word: 4 `GF256` elements. -/
abbrev AESWord := Fin 4 → GF256
instance : Inhabited AESWord := ⟨fun _ => 0⟩
