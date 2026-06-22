import Aes

/-!
# Sanity checks against FIPS 197 Appendix B

Each check exercises exactly ONE transformation on the round-1 state,
so evaluation only needs to run a tiny fraction of the full AES computation.

## FIPS 197 Appendix B data (AES-128)

Key:       2b 7e 15 16  28 ae d2 a6  ab f7 15 88  09 cf 4f 3c
Plaintext: 32 43 f6 a8  88 5a 30 8d  31 31 98 a2  e0 37 07 34

State after initial AddRoundKey (round 0 output / round 1 input):
  19 a0 9a e9
  3d f4 c6 f8
  e3 e2 8d 48
  be 2b 2a 08

After SubBytes (round 1):
  d4 e0 b8 1e
  27 bf b4 41
  11 98 5d 52
  ae f1 e5 30

After ShiftRows (round 1):
  d4 e0 b8 1e
  bf b4 41 27
  5d 52 11 98
  30 ae f1 e5

After MixColumns (round 1):
  04 e0 48 28
  66 cb f8 06
  81 19 d3 26
  e5 9a 7a 4c

Round 1 key (w[4..7]):
  a0 88 23 2a
  fa 54 a3 6c
  fe 2c 39 76
  17 b1 39 05

After AddRoundKey (round 1 output):
  a4 68 6b 02
  9c 9f 5b 6a
  7f 35 ea 50
  f2 2b 43 49
-/

-- ── Helpers ──────────────────────────────────────────────────────────────────

/-- Build a State from 16 bytes in column-major order. -/
private def mkState (bs : Fin 16 → UInt8) : State :=
  fun r c => ⟨bs ⟨c.val + r.val * 4, by omega⟩⟩

/-- Build a round-key State from 16 bytes in column-major order. -/
private def mkRK (bs : Fin 16 → UInt8) : State :=
  fun r c => ⟨bs ⟨c.val * 4 + r.val , by omega⟩⟩

-- ── FIPS B intermediate states ────────────────────────────────────────────────
-- State after initial AddRoundKey (= round 1 input)
private def stateR1in : State := mkState fun i =>
  (#[0x19, 0xa0, 0x9a, 0xe9,
     0x3d, 0xf4, 0xc6, 0xf8,
     0xe3, 0xe2, 0x8d, 0x48,
     0xbe, 0x2b, 0x2a, 0x08] : Array UInt8)[i]!

-- After SubBytes
private def stateR1sb : State := mkState fun i =>
  (#[0xd4, 0xe0, 0xb8, 0x1e,
     0x27, 0xbf, 0xb4, 0x41,
     0x11, 0x98, 0x5d, 0x52,
     0xae, 0xf1, 0xe5, 0x30] : Array UInt8)[i]!

-- After ShiftRows
private def stateR1sr : State := mkState fun i =>
  (#[0xd4, 0xe0, 0xb8, 0x1e,
     0xbf, 0xb4, 0x41, 0x27,
     0x5d, 0x52, 0x11, 0x98,
     0x30, 0xae, 0xf1, 0xe5] : Array UInt8)[i]!

-- After MixColumns
private def stateR1mc : State := mkState fun i =>
  (#[0x04, 0xe0, 0x48, 0x28,
     0x66, 0xcb, 0xf8, 0x06,
     0x81, 0x19, 0xd3, 0x26,
     0xe5, 0x9a, 0x7a, 0x4c] : Array UInt8)[i]!

-- Round 1 key (w[4..7])
private def rkR1 : State := mkRK fun i =>
  (#[0xa0, 0xfa, 0xfe, 0x17,
     0x88, 0x54, 0x2c, 0xb1,
     0x23, 0xa3, 0x39, 0x39,
     0x2a, 0x6c, 0x76, 0x05] : Array UInt8)[i]!

-- After AddRoundKey (round 1 output)
private def stateR1out : State := mkState fun i =>
  (#[0xa4, 0x68, 0x6b, 0x02,
     0x9c, 0x9f, 0x5b, 0x6a,
     0x7f, 0x35, 0xea, 0x50,
     0xf2, 0x2b, 0x43, 0x49] : Array UInt8)[i]!

-- ── Tests ─────────────────────────────────────────────────────────────────────

#eval (subBytes stateR1in) = stateR1sb
#eval (shiftRows stateR1sb) = stateR1sr
#eval (mixColumns stateR1sr) = stateR1mc
#eval (addRoundKey rkR1 stateR1mc) = stateR1out
#eval (encRound rkR1 stateR1in) = stateR1out

#eval (invSubBytes (subBytes stateR1in)) = stateR1in
#eval (invShiftRows (shiftRows stateR1sb)) = stateR1sb
#eval (invMixColumns (mixColumns stateR1sr)) = stateR1sr
