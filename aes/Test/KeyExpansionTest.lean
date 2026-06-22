import Aes.KeySchedule
import Aes.SubBytes

/-!
# Key expansion sanity checks — FIPS 197 Appendix A.1

Key: 2b 7e 15 16  28 ae d2 a6  ab f7 15 88  09 cf 4f 3c

FIPS 197 lists all 44 expanded words w[0]…w[43].
Each word is 4 bytes; `ek n : AESWord = Fin 4 → GF256` stores
byte `i` of word `n` at index `i` (row-within-word).

We check every word to confirm the key schedule is correct.
-/

-- ── Test key ──────────────────────────────────────────────────────────────────

-- k i : AESWord where i is the word index (0..3), j is byte index (0..3)
private def testKey : Fin 4 → AESWord := fun row col =>
  ⟨(#[0x2b, 0x7e, 0x15, 0x16,   -- w[0]
      0x28, 0xae, 0xd2, 0xa6,   -- w[1]
      0xab, 0xf7, 0x15, 0x88,   -- w[2]
      0x09, 0xcf, 0x4f, 0x3c]   -- w[3]
     : Array UInt8)[row.val * 4 + col.val]!⟩


private def ek := keyExpansion testKey

-- ── Expected words from FIPS 197 Appendix A.1 ────────────────────────────────
-- Format: each row is one word (4 bytes = one AESWord)

private def expectedWords : Array (Array UInt8) := #[
  -- Round 0 (original key)
  #[0x2b, 0x7e, 0x15, 0x16],  -- w[0]
  #[0x28, 0xae, 0xd2, 0xa6],  -- w[1]
  #[0xab, 0xf7, 0x15, 0x88],  -- w[2]
  #[0x09, 0xcf, 0x4f, 0x3c],  -- w[3]
  -- Round 1
  #[0xa0, 0xfa, 0xfe, 0x17],  -- w[4]
  #[0x88, 0x54, 0x2c, 0xb1],  -- w[5]
  #[0x23, 0xa3, 0x39, 0x39],  -- w[6]
  #[0x2a, 0x6c, 0x76, 0x05],  -- w[7]
  -- Round 2
  #[0xf2, 0xc2, 0x95, 0xf2],  -- w[8]
  #[0x7a, 0x96, 0xb9, 0x43],  -- w[9]
  #[0x59, 0x35, 0x80, 0x7a],  -- w[10]
  #[0x73, 0x59, 0xf6, 0x7f],  -- w[11]
  -- Round 3
  #[0x3d, 0x80, 0x47, 0x7d],  -- w[12]
  #[0x47, 0x16, 0xfe, 0x3e],  -- w[13]
  #[0x1e, 0x23, 0x7e, 0x44],  -- w[14]
  #[0x6d, 0x7a, 0x88, 0x3b],  -- w[15]
  -- Round 4
  #[0xef, 0x44, 0xa5, 0x41],  -- w[16]
  #[0xa8, 0x52, 0x5b, 0x7f],  -- w[17]
  #[0xb6, 0x71, 0x25, 0x3b],  -- w[18]
  #[0xdb, 0x0b, 0xad, 0x00],  -- w[19]
  -- Round 5
  #[0xd4, 0xd1, 0xc6, 0xf8],  -- w[20]
  #[0x7c, 0x83, 0x9d, 0x87],  -- w[21]
  #[0xca, 0xf2, 0xb8, 0xbc],  -- w[22]
  #[0x11, 0xf9, 0x15, 0xbc],  -- w[23]
  -- Round 6
  #[0x6d, 0x88, 0xa3, 0x7a],  -- w[24]
  #[0x11, 0x0b, 0x3e, 0xfd],  -- w[25]
  #[0xdb, 0xf9, 0x86, 0x41],  -- w[26]
  #[0xca, 0x00, 0x93, 0xfd],  -- w[27]
  -- Round 7
  #[0x4e, 0x54, 0xf7, 0x0e],  -- w[28]
  #[0x5f, 0x5f, 0xc9, 0xf3],  -- w[29]
  #[0x84, 0xa6, 0x4f, 0xb2],  -- w[30]
  #[0x4e, 0xa6, 0xdc, 0x4f],  -- w[31]
  -- Round 8
  #[0xea, 0xd2, 0x73, 0x21],  -- w[32]
  #[0xb5, 0x8d, 0xba, 0xd2],  -- w[33]
  #[0x31, 0x2b, 0xf5, 0x60],  -- w[34]
  #[0x7f, 0x8d, 0x29, 0x2f],  -- w[35]
  -- Round 9
  #[0xac, 0x77, 0x66, 0xf3],  -- w[36]
  #[0x19, 0xfa, 0xdc, 0x21],  -- w[37]
  #[0x28, 0xd1, 0x29, 0x41],  -- w[38]
  #[0x57, 0x5c, 0x00, 0x6e],  -- w[39]
  -- Round 10
  #[0xd0, 0x14, 0xf9, 0xa8],  -- w[40]
  #[0xc9, 0xee, 0x25, 0x89],  -- w[41]
  #[0xe1, 0x3f, 0x0c, 0xc8],  -- w[42]
  #[0xb6, 0x63, 0x0c, 0xa6]   -- w[43]
]

-- ── Check helpers ─────────────────────────────────────────────────────────────

private def wordToArray (w : AESWord) : Array UInt8 :=
  Array.ofFn fun (i : Fin 4) => w i |>.val

private def checkWord (n : Fin 44) : Bool :=
  wordToArray (ek n) == expectedWords[n.val]!

-- ── Individual word checks ────────────────────────────────────────────────────
-- Each #eval prints true if the computed word matches FIPS 197 Appendix A.1.

-- Round 0 (original key words — sanity check that input parsing is correct)
#eval checkWord 0   -- w[0]  = 2b 7e 15 16
#eval checkWord 1   -- w[1]  = 28 ae d2 a6
#eval checkWord 2   -- w[2]  = ab f7 15 88
#eval checkWord 3   -- w[3]  = 09 cf 4f 3c

-- Round 1 (first derived words — exercises rotWord, subWord, rcon[0]=01)
#eval checkWord 4   -- w[4]  = a0 fa fe 17
#eval checkWord 5   -- w[5]  = 88 54 2c b1
#eval checkWord 6   -- w[6]  = 23 a3 39 39
#eval checkWord 7   -- w[7]  = 2a 6c 76 05

-- Round 2
#eval checkWord 8   -- w[8]  = f2 c2 95 f2
#eval checkWord 9   -- w[9]  = 7a 96 b9 43
#eval checkWord 10  -- w[10] = 59 35 80 7a
#eval checkWord 11  -- w[11] = 73 59 f6 7f

-- Round 3
#eval checkWord 12  -- w[12] = 3d 80 47 7d
#eval checkWord 13  -- w[13] = 47 16 fe 3e
#eval checkWord 14  -- w[14] = 1e 23 7e 44
#eval checkWord 15  -- w[15] = 6d 7a 88 3b

-- Round 4
#eval checkWord 16  -- w[16] = ef 44 a5 41
#eval checkWord 17  -- w[17] = a8 52 5b 7f
#eval checkWord 18  -- w[18] = b6 71 25 3b
#eval checkWord 19  -- w[19] = db 0b ad 00

-- Round 5
#eval checkWord 20  -- w[20] = d4 d1 c6 f8
#eval checkWord 21  -- w[21] = 7c 83 9d 87
#eval checkWord 22  -- w[22] = ca f2 b8 bc
#eval checkWord 23  -- w[23] = 11 f9 15 bc

-- Round 6
#eval checkWord 24  -- w[24] = 6d 88 a3 7a
#eval checkWord 25  -- w[25] = 11 0b 3e fd
#eval checkWord 26  -- w[26] = db f9 86 41
#eval checkWord 27  -- w[27] = ca 00 93 fd

-- Round 7
#eval checkWord 28  -- w[28] = 4e 54 f7 0e
#eval checkWord 29  -- w[29] = 5f 5f c9 f3
#eval checkWord 30  -- w[30] = 84 a6 4f b2
#eval checkWord 31  -- w[31] = 4e a6 dc 4f

-- Round 8
#eval checkWord 32  -- w[32] = ea d2 73 21
#eval checkWord 33  -- w[33] = b5 8d ba d2
#eval checkWord 34  -- w[34] = 31 2b f5 60
#eval checkWord 35  -- w[35] = 7f 8d 29 2f

-- Round 9
#eval checkWord 36  -- w[36] = ac 77 66 f3
#eval checkWord 37  -- w[37] = 19 fa dc 21
#eval checkWord 38  -- w[38] = 28 d1 29 41
#eval checkWord 39  -- w[39] = 57 5c 00 6e

-- Round 10
#eval checkWord 40  -- w[40] = d0 14 f9 a8
#eval checkWord 41  -- w[41] = c9 ee 25 89
#eval checkWord 42  -- w[42] = e1 3f 0c c8
#eval checkWord 43  -- w[43] = b6 63 0c a6

-- ── Bulk check (all 44 words at once) ────────────────────────────────────────
#eval (List.finRange 44).all checkWord   -- should print true
