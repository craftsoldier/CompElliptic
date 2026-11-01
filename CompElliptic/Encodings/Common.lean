/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import Mathlib.Data.Vector.Defs
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.ZMod.Basic

/-!
# Common encoding primitives (integers, bit sequences, and endianness)

The Zcash Protocol Specification's integer / bit-sequence / octet-string conversion primitives,
shared by the concrete point and field encodings in `CompElliptic/Encodings/`. Following the
*Separate types with explicit conversions* and *Give mistakes nowhere to hide* principles: bit-
and byte-sequence depictions are distinct fixed-length types with their lengths in the types
(so truncation / padding errors are caught), and the endianness is carried *in the name* of each
primitive, never a silent default.

Every primitive in this family takes a *bit* length (never a byte length), so there is no
bit-vs-byte ambiguity to remember at a call site; an octet primitive like `I2LEOSP` produces
`⌈ℓ/8⌉` bytes from a bit length `ℓ`.

So far: `I2LEOSP` and `LEOS2IP` (integer ↔ little-endian octet string), which undo each other
(`LEOS2IP_I2LEOSP`, `I2LEOSP_LEOS2IP`); the little-endian bit-sequence conversions `I2LEBSP` and
`LEBS2IP`, with bit sequences as `BitVec ℓ` (bit `i` of the sequence is `getLsbD i`); and the
bit-to-byte bridge `LEBS2OSP`, under which bits and bytes agree (`LEBS2OSP_I2LEBSP`). `LEOS2BSP`
will join it here when a consumer needs it.
-/

namespace CompElliptic

/-- `I2LEOSP ℓ n`: the little-endian octet (byte) encoding of the integer `n`, as `⌈ℓ/8⌉ = (ℓ+7)/8`
bytes, least-significant byte first (Zcash spec, "Integers, Bit Sequences, and Endianness").
Byte `i` is `⌊n / 256^i⌋ mod 256`.

`ℓ` is a *bit* length (uniform with the rest of the family), and the domain `Fin (2^ℓ)` ensures
that `n` is in range by construction, so that there can be no silent high-byte truncation
(*Give mistakes nowhere to hide*). -/
def I2LEOSP (ℓ : ℕ) (n : Fin (2^ℓ)) : Vector UInt8 ((ℓ + 7) / 8) :=
  Vector.ofFn (fun i : Fin ((ℓ + 7) / 8) => UInt8.ofNat (n.val / 256^(i : ℕ) % 256))

/-- `LEOS2IP S`: the integer represented in little-endian byte order by the `m`-byte string `S`
(Zcash spec, "Integers, Bit Sequences, and Endianness") — the decode-direction inverse of
`I2LEOSP` on byte-aligned lengths. The byte length `m` is carried by `S`'s type, and the result
lies in `[0, 2^(8*m))`. -/
def LEOS2IP {m : ℕ} (S : Vector UInt8 m) : ℕ :=
  Nat.ofDigits 256 (S.toList.map UInt8.toNat)

/-- The integer `x.val + (y.val % 2)·2^k` of a compressed point encoding (an `x`-coordinate with a
single parity/sign bit at position `k`) is `< 2^(k+1)`, provided the base field modulus fits in `k`
bits (`Fact (n ≤ 2^k)`). This is the field-size precondition that lets such an integer inhabit
`Fin (2^(k+1))`, e.g. for `I2LEOSP (k+1)`. -/
theorem encodedInt_lt {k n : ℕ} [Fact (Nat.Prime n)] [Fact (n ≤ 2^k)] (x y : ZMod n) :
    x.val + (y.val % 2) * 2^k < 2^(k + 1) := by
  haveI : NeZero n := ⟨(Fact.out : Nat.Prime n).pos.ne'⟩
  have hx : x.val < 2^k := lt_of_lt_of_le (ZMod.val_lt x) Fact.out
  have hkk : (2 : ℕ)^(k + 1) = 2^k + 2^k := by rw [pow_succ]; ring
  have hpar : y.val % 2 ≤ 1 := by omega
  have hprod : (y.val % 2) * 2^k ≤ 2^k := by
    calc (y.val % 2) * 2^k ≤ 1 * 2^k := by gcongr
      _ = 2^k := one_mul _
  omega

/-! ## Round trips between integers and octet strings -/

/-- The little-endian base-256 digits of `n`, `k` of them, read back give `n mod 256^k`. -/
private theorem ofDigits_ofFn_mod (k n : ℕ) :
    Nat.ofDigits 256 (List.ofFn (fun i : Fin k => n / 256 ^ (i : ℕ) % 256)) = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
    rw [List.ofFn_succ, Nat.ofDigits_cons]
    simp only [Fin.val_zero, pow_zero, Nat.div_one, Fin.val_succ, pow_succ']
    have h : ∀ i : Fin k, n / (256 * 256 ^ (i : ℕ)) % 256 = n / 256 / 256 ^ (i : ℕ) % 256 :=
      fun i => by rw [Nat.div_div_eq_div_mul]
    simp only [h, ih (n / 256)]
    rw [Nat.mod_mul]

/-- `LEOS2IP` undoes `I2LEOSP`. -/
theorem LEOS2IP_I2LEOSP (ℓ : ℕ) (n : Fin (2 ^ ℓ)) : LEOS2IP (I2LEOSP ℓ n) = n.val := by
  have hlt : n.val < 256 ^ ((ℓ + 7) / 8) := by
    calc n.val < 2 ^ ℓ := n.isLt
      _ ≤ 2 ^ (8 * ((ℓ + 7) / 8)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 256 ^ ((ℓ + 7) / 8) := by rw [pow_mul]; norm_num
  simp only [LEOS2IP, I2LEOSP, Vector.toList_ofFn, List.map_ofFn]
  have e : (UInt8.toNat ∘ fun i : Fin ((ℓ + 7) / 8) => UInt8.ofNat (n.val / 256 ^ (i : ℕ) % 256)) =
      fun i : Fin ((ℓ + 7) / 8) => n.val / 256 ^ (i : ℕ) % 256 := by
    funext i
    simp only [Function.comp, UInt8.toNat_ofNat']
    exact Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (by norm_num)) (by norm_num))
  rw [e, ofDigits_ofFn_mod, Nat.mod_eq_of_lt hlt]

/-- The digits of a base-256 number are read back by division and remainder. -/
private theorem ofDigits_div_pow_mod (L : List ℕ) (hL : ∀ x ∈ L, x < 256) (i : ℕ) :
    Nat.ofDigits 256 L / 256 ^ i % 256 = L.getD i 0 := by
  induction L generalizing i with
  | nil => simp
  | cons a L ih =>
    have ha : a < 256 := hL a (by simp)
    have hL' : ∀ x ∈ L, x < 256 := fun x hx => hL x (by simp [hx])
    rw [Nat.ofDigits_cons]
    cases i with
    | zero => simp; omega
    | succ i =>
      rw [pow_succ', ← Nat.div_div_eq_div_mul,
        show (a + 256 * Nat.ofDigits 256 L) / 256 = Nat.ofDigits 256 L by omega, ih hL' i]
      simp

/-- `LEOS2IP` of `m` bytes is below `2^(8·m)`. -/
theorem LEOS2IP_lt {m : ℕ} (S : Vector UInt8 m) : LEOS2IP S < 2 ^ (8 * m) := by
  have h := Nat.ofDigits_lt_base_pow_length (b := 256) (l := S.toList.map UInt8.toNat)
    (by norm_num) (fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact y.toNat_lt)
  simpa [LEOS2IP, pow_mul] using h

/-- `I2LEOSP 256` undoes `LEOS2IP` on 32 bytes. -/
theorem I2LEOSP_LEOS2IP (S : Vector UInt8 32) : I2LEOSP 256 ⟨LEOS2IP S, LEOS2IP_lt S⟩ = S := by
  ext i hi
  simp only [I2LEOSP, Vector.getElem_ofFn, LEOS2IP]
  rw [ofDigits_div_pow_mod _ (fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact y.toNat_lt)]
  simp [List.getD_eq_getElem?_getD, hi]

/-- `LEOS2IP` is injective on 32 bytes. -/
theorem LEOS2IP_injective : Function.Injective (LEOS2IP (m := 32)) := fun S T h => by
  rw [← I2LEOSP_LEOS2IP S, ← I2LEOSP_LEOS2IP T]
  congr 1
  exact Fin.ext h

/-! ## Bit sequences -/

/-- `I2LEBSP ℓ n`: the bit sequence of length `ℓ` representing `n` in little-endian order (Zcash
spec, "Integers, Bit Sequences, and Endianness"). Bit `i` of the sequence is `getLsbD i`. -/
def I2LEBSP (ℓ : ℕ) (n : Fin (2 ^ ℓ)) : BitVec ℓ := BitVec.ofNat ℓ n

/-- `LEBS2IP S`: the integer represented in little-endian order by the bit sequence `S` (Zcash
spec, "Integers, Bit Sequences, and Endianness"). -/
def LEBS2IP {ℓ : ℕ} (S : BitVec ℓ) : ℕ := S.toNat

/-- `LEBS2OSP S`: the bit sequence `S`, padded on the right with zero bits to a multiple of 8, as
the `⌈ℓ/8⌉` bytes whose bits, least significant first, are the groups of 8 in order (Zcash spec,
"Integers, Bit Sequences, and Endianness"). -/
def LEBS2OSP {ℓ : ℕ} (S : BitVec ℓ) : Vector UInt8 ((ℓ + 7) / 8) :=
  Vector.ofFn fun j : Fin ((ℓ + 7) / 8) => UInt8.ofNat (S.extractLsb' (8 * j) 8).toNat

/-- `LEBS2IP` undoes `I2LEBSP`. -/
theorem LEBS2IP_I2LEBSP (ℓ : ℕ) (n : Fin (2 ^ ℓ)) : LEBS2IP (I2LEBSP ℓ n) = n.val := by
  simp [LEBS2IP, I2LEBSP]

/-- The bytes of the bit encoding of `n` are the byte encoding of `n`. -/
theorem LEBS2OSP_I2LEBSP (ℓ : ℕ) (n : Fin (2 ^ ℓ)) : LEBS2OSP (I2LEBSP ℓ n) = I2LEOSP ℓ n := by
  ext j hj
  simp only [LEBS2OSP, I2LEBSP, I2LEOSP, Vector.getElem_ofFn, BitVec.extractLsb'_toNat,
    BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt n.isLt, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

end CompElliptic
