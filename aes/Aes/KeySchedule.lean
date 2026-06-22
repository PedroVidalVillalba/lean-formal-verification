import Aes.Common
import Aes.SubBytes

set_option linter.style.header false

open GF256

private def rcon : Fin 10 → GF256
  | 0 => 0x01 | 1 => 0x02 | 2 => 0x04 | 3 => 0x08 | 4 => 0x10
  | 5 => 0x20 | 6 => 0x40 | 7 => 0x80 | 8 => 0x1b | 9 => 0x36

def subWord (w : AESWord) : AESWord := fun i => sBox (w i)
def rotWord (w : AESWord) : AESWord := fun i => w ((i + 1) % 4)

def keyExpansion (k : Fin 4 → AESWord) : Fin 44 → AESWord :=
  let rec expand (acc : Array AESWord) (n : ℕ)
      (hn : acc.size = n + 4) : Array AESWord :=
    if h : n < 40 then
      have h3 : n + 3 < acc.size := by omega
      have h0 : n < acc.size     := by omega
      let prev  := acc[n + 3]
      let back4 := acc[n]
      let w : AESWord :=
        if (n + 4) % 4 = 0 then
          let rc : Fin 10 := ⟨(n + 4) / 4 - 1, by omega⟩
          fun j => back4 j + (subWord (rotWord prev)) j +
                   (if j = 0 then rcon rc else 0)
        else
          fun j => back4 j + prev j
      expand (acc.push w) (n + 1) (by simp [Array.size_push, hn])
    else
      acc
  termination_by 40 - n
  let arr := expand #[k 0, k 1, k 2, k 3] 0 (by rfl)
  fun ⟨n, _⟩ => arr[n]!

def roundKey (ek : Fin 44 → AESWord) (r : Fin 11) : State :=
  fun row col => ek ⟨r.val * 4 + col.val, by
    have := r.isLt; have := col.isLt; omega⟩ row
