/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Julian Abraham
-/
import CompElliptic.Curves.JubjubOrder
import CompElliptic.Encoding
import CompElliptic.Encodings.Common
import CompElliptic.Fields.BLS12_381

/-!
# Encodings of Jubjub curve points

The compressed point encoding for Jubjub, per the Zcash Protocol Specification
[§5.4.9.3 "Jubjub"](https://zips.z.cash/protocol/protocol.pdf#jubjub). A point `(u, v)` encodes as
the 32-byte little-endian octet string of `v` with the free top bit (bit 255, since the field
modulus is `< 2^255`) set to the parity of `u` (`toBytes`): the specification's
`repr_𝕁(u, v) = I2LEBSP₂₅₆(v + 2^255·ũ)`, `ũ = u mod 2`, packed into bytes
(`toBytes_eq_LEBS2OSP`). Matches the `jubjub` crate's `AffinePoint::to_bytes`.

`fromBytesPreZip216` is the specification's `abst_𝕁`: it reads `v` from the first 255 bits and `ũ`
from the last (`bits_of_lt`), rejects `v ≥ q`, takes a square root of `(1 − v²)/(a − d·v²)` (the
curve equation solved for `u²`; the denominator is never zero, `a_sub_d_mul_sq_ne_zero`), and
returns that root as `u` if its parity is `ũ` and its negation otherwise. For `u = 0` both are `0`,
whatever `ũ` is, so the specification's current `abst_𝕁` accepts the two
non-canonical encodings of [ZIP 216](https://zips.z.cash/zip-0216), as does the crate's
`AffinePoint::from_bytes_pre_zip216_compatibility`, so it is the decoder of a `LenientEncoding`
(`JubjubLenientEncoding`).

[ZIP 216](https://zips.z.cash/zip-0216) requires rejecting those two encodings at the places
where Jubjub points are encoded in the consensus protocol and in addresses and keys, and the
crate's `AffinePoint::from_bytes`, the decoder `sapling-crypto` and Zebra use, rejects them:
`fromBytes` is `fromBytesPreZip216` with ZIP 216's check that the point re-encodes to
the input, the decoder of the canonical encoding `JubjubEncoding`
(`LenientEncoding.toCanonical`). `nonCanonical_iff` proves that the two encodings ZIP 216 names,
`zip216Identity` and `zip216NegOne`, are the only ones `fromBytesPreZip216` accepts and `toBytes`
does not produce, so `fromBytes` rejects exactly those two besides what `fromBytesPreZip216`
rejects (`fromBytes_eq_none_iff`).

The fixtures check `toBytes`, `fromBytesPreZip216` and `fromBytes` against the `jubjub` crate's
own test vectors, by kernel evaluation.
-/

namespace CompElliptic

/-- The BLS12-381 scalar field modulus (Jubjub's base field) fits in 255 bits, so the compressed
encoding has a free top bit for the parity of `u`. -/
instance : Fact (Fields.BLS12_381.BLS12_381_SCALAR_CARD ≤ 2^255) := ⟨by decide⟩

end CompElliptic

namespace CompElliptic.Curves.Jubjub

open CompElliptic.CurveForms.CtEdwards CompElliptic.Fields CompElliptic.Fields.BLS12_381

/-- The compressed encoding of a Jubjub point: the 32-byte (`I2LEOSP 256`) little-endian encoding
of `v` with bit 255 set to the parity of `u`. The integer is `< 2^256` by `encodedInt_lt`. -/
def toBytes (P : CtEdwardsPoint curve) : Vector UInt8 32 :=
  I2LEOSP 256 ⟨P.v.val + (P.u.val % 2) * 2^255, encodedInt_lt P.v P.u⟩

/-- `toBytes` is the specification's `repr_𝕁`, the bit sequence `I2LEBSP₂₅₆(v + 2^255·ũ)`, packed
into bytes by `LEBS2OSP`. -/
theorem toBytes_eq_LEBS2OSP (P : CtEdwardsPoint curve) :
    toBytes P = LEBS2OSP (I2LEBSP 256 ⟨P.v.val + (P.u.val % 2) * 2^255, encodedInt_lt P.v P.u⟩) :=
  (LEBS2OSP_I2LEBSP 256 _).symm

/-- In the bit sequence `I2LEBSP₂₅₆(n)`, the first 255 bits are `n % 2^255` and the last bit is
`n / 2^255`: the two parts that `abst_𝕁` reads, and that `fromBytesPreZip216` takes from
`LEOS2IP`. -/
theorem bits_of_lt (n : Fin (2 ^ 256)) :
    LEBS2IP ((I2LEBSP 256 n).setWidth 255) = n.val % 2 ^ 255 ∧
      (I2LEBSP 256 n).getLsbD 255 = decide (n.val / 2 ^ 255 = 1) := by
  have h1 : n.val / 2 ^ 255 ≤ 1 := by have := n.isLt; omega
  constructor
  · simp [LEBS2IP, I2LEBSP]
  · rw [I2LEBSP, BitVec.getLsbD_ofNat, Nat.testBit, Nat.shiftRight_eq_div_pow]
    simp only [show (255 : ℕ) < 256 by decide, decide_true, Bool.true_and]
    generalize n.val / 2 ^ 255 = m at h1 ⊢
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with rfl | rfl <;> rfl

/-- `u² = (1 − v²)/(a − d·v²)` puts `(u, v)` on the curve. -/
theorem onCurve_of_sq {u v : BLS12381ScalarField}
    (h : u * u = (1 - v ^ 2) / (curve.a - curve.d * v ^ 2)) : OnCurve curve.a curve.d (u, v) := by
  rw [eq_div_iff (curve.a_sub_d_mul_sq_ne_zero v)] at h
  simp only [OnCurve]
  linear_combination h

/-- The curve equation solved for `u²`: `(1 − v²)/(a − d·v²)`. -/
def uSq (v : BLS12381ScalarField) : BLS12381ScalarField :=
  (1 - v ^ 2) / (curve.a - curve.d * v ^ 2)

/-- On the curve, `uSq v = u²`. -/
theorem uSq_eq (P : CtEdwardsPoint curve) : uSq P.v = P.u * P.u := by
  have h : curve.a * P.u ^ 2 + P.v ^ 2 = 1 + curve.d * P.u ^ 2 * P.v ^ 2 := P.onCurve
  rw [uSq, div_eq_iff (curve.a_sub_d_mul_sq_ne_zero P.v)]
  linear_combination -h

/-- The point with this `v` and `u = r` if `r` has parity `s`, `u = −r` otherwise, for a root `r`
of `uSq v`. -/
def ofRoot (v r : BLS12381ScalarField) (s : ℕ) (hr : r * r = uSq v) : CtEdwardsPoint curve :=
  ⟨if r.val % 2 = s then r else -r, v, onCurve_of_sq (by split_ifs <;> simp [hr, uSq])⟩

/-- Decoding once `v` and the sign bit `s` are read: `none` if `uSq v` is not a square, otherwise
the point `ofRoot` builds from the square root `sqrt?` returns. -/
def decodeAt (v : BLS12381ScalarField) (s : ℕ) : Option (CtEdwardsPoint curve) :=
  (bls12_381Scalar.sqrtSub? (uSq v)).map fun r => ofRoot v r.1 s r.2

/-- `decodeAt` returns the point built from the root `sqrt?` returns. -/
theorem decodeAt_of {v r : BLS12381ScalarField} {s : ℕ}
    (h : bls12_381Scalar.sqrt? (uSq v) = some r) : ∃ hr, decodeAt v s = some (ofRoot v r s hr) := by
  obtain ⟨hr, hsub⟩ := TonelliShanks.sqrtSub?_of_sqrt? bls12_381Scalar h
  exact ⟨hr, by unfold decodeAt; rw [hsub]; rfl⟩

/-- The specification's `abst_𝕁` (§5.4.9.3), the decoder before ZIP 216's canonicity check: `none`
if the low 255 bits, as `v`, are `≥ q` or `uSq v` is not a square; otherwise the point with that
`v` and, as `u`, the square root of `uSq v` if its parity is the top bit and its negation if not.
Matches the `jubjub` crate's `AffinePoint::from_bytes_pre_zip216_compatibility`. -/
def fromBytesPreZip216 (b : Vector UInt8 32) : Option (CtEdwardsPoint curve) :=
  if LEOS2IP b % 2 ^ 255 < BLS12_381_SCALAR_CARD then
    decodeAt ((LEOS2IP b % 2 ^ 255 : ℕ) : BLS12381ScalarField) (LEOS2IP b / 2 ^ 255)
  else none

/-- If `r² = u²`, picking `r` or `−r` by the parity of `u` gives `u`: `r = ±u`, and for `u ≠ 0`
the two roots have opposite parity because `q` is odd. -/
theorem sign_fix {u r : BLS12381ScalarField} (h : r * r = u * u) :
    (if r.val % 2 = u.val % 2 then r else -r) = u := by
  rcases mul_self_eq_mul_self_iff.mp h with rfl | rfl
  · simp
  · by_cases hu : u = 0
    · simp [hu]
    · have hq : BLS12_381_SCALAR_CARD % 2 = 1 := by decide
      have hlt : u.val < BLS12_381_SCALAR_CARD := ZMod.val_lt u
      have hpos : 0 < u.val := by rwa [Nat.pos_iff_ne_zero, ne_eq, ZMod.val_eq_zero]
      rw [ZMod.neg_val, if_neg hu, if_neg (by omega), neg_neg]

/-- **Decoding undoes encoding.** -/
theorem fromBytesPreZip216_toBytes (P : CtEdwardsPoint curve) :
    fromBytesPreZip216 (toBytes P) = some P := by
  have hvlt : P.v.val < BLS12_381_SCALAR_CARD := ZMod.val_lt P.v
  have hq : BLS12_381_SCALAR_CARD < 2 ^ 255 := by decide
  have hn : LEOS2IP (toBytes P) = P.v.val + (P.u.val % 2) * 2 ^ 255 := LEOS2IP_I2LEOSP 256 _
  -- Name the bytes, so that no step evaluates the concrete encoding.
  generalize toBytes P = b at hn ⊢
  have hv : LEOS2IP b % 2 ^ 255 = P.v.val := by rw [hn]; omega
  have hs : LEOS2IP b / 2 ^ 255 = P.u.val % 2 := by rw [hn]; omega
  obtain ⟨r, hr⟩ := TonelliShanks.sqrt?_isSome_of_isSquare bls12_381Scalar ⟨P.u, uSq_eq P⟩
  have hrr : r * r = P.u * P.u :=
    (TonelliShanks.sqrt?_mul_self bls12_381Scalar hr).trans (uSq_eq P)
  obtain ⟨_, hdec⟩ := decodeAt_of (v := P.v) (s := P.u.val % 2) hr
  unfold fromBytesPreZip216
  simp only [hv, hs, if_pos hvlt, ZMod.natCast_zmod_val, hdec, Option.some.injEq]
  refine CtEdwardsPoint.ext_pair ?_
  show ((if r.val % 2 = P.u.val % 2 then r else -r), P.v) = (P.u, P.v)
  simp only [sign_fix hrr]

end CompElliptic.Curves.Jubjub

namespace CompElliptic

open CompElliptic.CurveForms.CtEdwards CompElliptic.Curves.Jubjub

/-- The lenient encoding of Jubjub points: `toBytes` and the specification's `abst_𝕁`. -/
def JubjubLenientEncoding : LenientEncoding (CtEdwardsPoint curve) (Vector UInt8 32) where
  encode := toBytes
  decode := fromBytesPreZip216
  encodek := fromBytesPreZip216_toBytes

end CompElliptic

namespace CompElliptic.Curves.Jubjub

open CompElliptic.CurveForms.CtEdwards CompElliptic.Fields.BLS12_381

/-! ### Fixtures

A point with `u = 3`, and its negation, round-trip; `v = 2` is on no point (`uSq 2` is a
non-square) and `v = q` fails the range check. -/

/-- A point with `u = 3`. -/
def uThreePoint : CtEdwardsPoint curve :=
  ⟨3, 26155723652191673091881779851507865815856437797311909079256717375290769542325, by decide⟩

example : fromBytesPreZip216 (toBytes uThreePoint) = some uThreePoint := by decide +kernel
example : fromBytesPreZip216 (toBytes (-uThreePoint)) = some (-uThreePoint) := by decide +kernel
example : fromBytesPreZip216 (I2LEOSP 256 ⟨2, by decide⟩) = none := by decide +kernel
example : fromBytesPreZip216 (I2LEOSP 256 ⟨BLS12_381_SCALAR_CARD, by decide⟩) = none := by decide

/-! ### Fixtures against the `jubjub` crate

The crate's `test_serialization_consistency`
(<https://github.com/zkcrypto/jubjub/blob/0cabeca668d89f9e8edbb3cbccdefeffdf21f651/src/lib.rs#L1817>)
starts from `FULL_GENERATOR`
(<https://github.com/zkcrypto/jubjub/blob/0cabeca668d89f9e8edbb3cbccdefeffdf21f651/src/lib.rs#L1588>),
whose coordinates its `from_raw` gives as little-endian `u64` limbs, multiplies it by the cofactor
`8`, and checks that the `k`-th multiple of the result serializes to the `k`-th of 16 byte strings,
quoted below verbatim in decimal. `jubjub` 0.11.1 is the version `sapling-crypto` 0.9.0 depends
on. -/

/-- The crate's `FULL_GENERATOR`. -/
def fullGenerator : CtEdwardsPoint curve :=
  ⟨44746807950788659978687200207992930935149218647843500701850233404325651525118,
    11, by decide⟩

/-- `[8] FULL_GENERATOR`, the crate's `gen`. -/
def G8 : CtEdwardsPoint curve := 8 • fullGenerator

example : (toBytes ((1 : ℕ) • G8)).toList =
    [203, 85, 12, 213, 56, 234, 12, 193, 19, 132, 128, 64, 142, 110, 170, 185, 179, 108, 97, 63,
     13, 211, 247, 120, 79, 219, 110, 234, 131, 123, 19, 215] := by
  decide +kernel

example : (toBytes ((2 : ℕ) • G8)).toList =
    [113, 154, 240, 230, 224, 198, 208, 170, 104, 15, 59, 126, 151, 222, 233, 195, 203, 195,
     167, 129, 89, 121, 240, 142, 51, 166, 64, 250, 184, 202, 154, 177] := by
  decide +kernel

example : (toBytes ((3 : ℕ) • G8)).toList =
    [197, 41, 93, 209, 203, 55, 164, 174, 88, 0, 90, 199, 1, 156, 149, 141, 240, 29, 14, 82, 86,
     225, 126, 129, 186, 157, 148, 162, 219, 51, 156, 199] := by
  decide +kernel

example : (toBytes ((4 : ℕ) • G8)).toList =
    [182, 117, 250, 241, 81, 196, 199, 227, 151, 74, 243, 17, 221, 97, 200, 139, 192, 83, 231,
     35, 214, 14, 95, 69, 130, 201, 4, 116, 177, 19, 179, 0] := by
  decide +kernel

example : (toBytes ((5 : ℕ) • G8)).toList =
    [118, 41, 29, 200, 60, 189, 119, 252, 78, 40, 230, 18, 208, 221, 38, 214, 176, 250, 4, 10,
     77, 101, 26, 216, 193, 198, 226, 84, 25, 177, 230, 185] := by
  decide +kernel

example : (toBytes ((6 : ℕ) • G8)).toList =
    [226, 189, 227, 208, 112, 117, 136, 98, 72, 38, 211, 167, 254, 82, 174, 113, 112, 166, 138,
     171, 166, 113, 52, 251, 129, 197, 138, 45, 195, 7, 61, 140] := by
  decide +kernel

example : (toBytes ((7 : ℕ) • G8)).toList =
    [38, 198, 156, 196, 146, 225, 55, 163, 138, 178, 157, 128, 115, 135, 204, 215, 0, 33, 171,
     20, 60, 32, 142, 209, 33, 233, 125, 146, 207, 12, 16, 24] := by
  decide +kernel

example : (toBytes ((8 : ℕ) • G8)).toList =
    [17, 187, 231, 83, 165, 36, 232, 184, 140, 205, 195, 252, 166, 85, 59, 86, 3, 226, 211, 67,
     179, 29, 238, 181, 102, 142, 58, 63, 57, 89, 174, 138] := by
  decide +kernel

example : (toBytes ((9 : ℕ) • G8)).toList =
    [210, 159, 80, 16, 181, 39, 221, 204, 224, 144, 145, 79, 54, 231, 8, 140, 142, 216, 93, 190,
     183, 116, 174, 63, 33, 242, 177, 118, 148, 40, 241, 203] := by
  decide +kernel

example : (toBytes ((10 : ℕ) • G8)).toList =
    [0, 143, 107, 102, 149, 187, 27, 124, 18, 10, 98, 28, 113, 123, 121, 185, 29, 152, 14, 130,
     149, 28, 87, 35, 135, 135, 153, 54, 112, 53, 54, 68] := by
  decide +kernel

example : (toBytes ((11 : ℕ) • G8)).toList =
    [178, 131, 85, 160, 214, 51, 208, 157, 196, 152, 247, 93, 202, 56, 81, 239, 155, 122, 59,
     188, 237, 253, 11, 169, 208, 236, 12, 4, 163, 211, 88, 97] := by
  decide +kernel

example : (toBytes ((12 : ℕ) • G8)).toList =
    [246, 194, 231, 195, 159, 101, 180, 133, 80, 21, 185, 220, 195, 115, 144, 12, 90, 150, 44,
     117, 8, 156, 168, 248, 206, 41, 60, 82, 67, 75, 57, 67] := by
  decide +kernel

example : (toBytes ((13 : ℕ) • G8)).toList =
    [212, 205, 171, 153, 113, 16, 194, 241, 224, 43, 177, 110, 190, 248, 22, 201, 208, 166, 2,
     83, 134, 130, 85, 129, 166, 136, 185, 191, 163, 38, 54, 10] := by
  decide +kernel

example : (toBytes ((14 : ℕ) • G8)).toList =
    [8, 60, 190, 39, 153, 222, 119, 23, 142, 237, 12, 110, 146, 9, 19, 219, 143, 64, 161, 99,
     199, 77, 39, 148, 70, 213, 246, 227, 150, 178, 237, 178] := by
  decide +kernel

example : (toBytes ((15 : ℕ) • G8)).toList =
    [11, 114, 217, 160, 101, 37, 100, 220, 56, 114, 42, 31, 138, 33, 84, 157, 214, 167, 73, 233,
     115, 81, 124, 134, 15, 31, 181, 60, 184, 130, 175, 159] := by
  decide +kernel

example : (toBytes ((16 : ℕ) • G8)).toList =
    [141, 238, 235, 202, 241, 32, 210, 10, 127, 230, 54, 31, 146, 80, 247, 9, 107, 124, 0, 26,
     203, 16, 237, 34, 214, 147, 133, 15, 29, 236, 37, 88] := by
  decide +kernel

/-- The third string decodes back to `[3] G8`. -/
example : fromBytesPreZip216 (Vector.mk
    #[197, 41, 93, 209, 203, 55, 164, 174, 88, 0, 90, 199, 1, 156, 149, 141, 240, 29, 14, 82, 86,
      225, 126, 129, 186, 157, 148, 162, 219, 51, 156, 199] rfl) =
    some ((3 : ℕ) • G8) := by
  decide +kernel

end CompElliptic.Curves.Jubjub

namespace CompElliptic.Curves.Jubjub

open CompElliptic CompElliptic.CurveForms.CtEdwards CompElliptic.Fields.BLS12_381

/-! ## The canonical encoding (ZIP 216) -/

/-- What `fromBytesPreZip216` returns: the range check passed, `v` is the low 255 bits, and `u` is
a root `r` of `uSq v`, or its negation, by the top bit. -/
theorem fromBytesPreZip216_spec {b : Vector UInt8 32} {P : CtEdwardsPoint curve}
    (h : fromBytesPreZip216 b = some P) :
    LEOS2IP b % 2 ^ 255 < BLS12_381_SCALAR_CARD ∧
      P.v = ((LEOS2IP b % 2 ^ 255 : ℕ) : BLS12381ScalarField) ∧
      ∃ r, r * r = uSq P.v ∧ P.u = if r.val % 2 = LEOS2IP b / 2 ^ 255 then r else -r := by
  unfold fromBytesPreZip216 at h
  split_ifs at h with hlt
  unfold decodeAt at h
  obtain ⟨⟨r, hr⟩, -, hP⟩ := Option.map_eq_some_iff.mp h
  subst hP
  exact ⟨hlt, rfl, r, hr, rfl⟩

/-- The non-canonical encoding of the identity `(0, 1)` that ZIP 216 names:
`I2LEOSP₂₅₆(2^255 + 1)`. -/
def zip216Identity : Vector UInt8 32 := I2LEOSP 256 ⟨2 ^ 255 + 1, by decide⟩

/-- The non-canonical encoding of `(0, −1)` that ZIP 216 names: `I2LEOSP₂₅₆(2^255 + q − 1)`. -/
def zip216NegOne : Vector UInt8 32 :=
  I2LEOSP 256 ⟨2 ^ 255 + BLS12_381_SCALAR_CARD - 1, by decide⟩

/-- **The non-canonical encodings** of [ZIP 216](https://zips.z.cash/zip-0216): the byte strings
that `fromBytesPreZip216` decodes but `toBytes` does not produce are exactly `zip216Identity` and
`zip216NegOne`. A decoded `u` of the wrong parity must be `0`, so the point is `(0, ±1)` and the top
bit is set. -/
theorem nonCanonical_iff (b : Vector UInt8 32) :
    (∃ P, fromBytesPreZip216 b = some P ∧ toBytes P ≠ b) ↔
      b = zip216Identity ∨ b = zip216NegOne := by
  constructor
  · rintro ⟨P, hP, hne⟩
    obtain ⟨hlt, hv, r, -, hu⟩ := fromBytesPreZip216_spec hP
    have hq : BLS12_381_SCALAR_CARD < 2 ^ 255 := by decide
    have hq2 : BLS12_381_SCALAR_CARD % 2 = 1 := by decide
    have hblt : LEOS2IP b < 2 ^ 256 := LEOS2IP_lt b
    have hs1 : LEOS2IP b / 2 ^ 255 ≤ 1 := by omega
    have hval : P.v.val = LEOS2IP b % 2 ^ 255 := by rw [hv, ZMod.val_natCast_of_lt hlt]
    -- If `u` had the parity of the top bit, `P` would re-encode to `b`.
    have hpar : P.u.val % 2 ≠ LEOS2IP b / 2 ^ 255 := by
      intro hpu
      apply hne
      rw [← I2LEOSP_LEOS2IP b]
      unfold toBytes
      congr 1
      apply Fin.ext
      show P.v.val + (P.u.val % 2) * 2 ^ 255 = LEOS2IP b
      rw [hval, hpu]
      omega
    -- So `u = −r` with both of the wrong parity, which forces `r = 0`, `u = 0` and a set top bit.
    have hu0 : P.u = 0 := by
      split_ifs at hu with hrs
      · exact absurd (hu ▸ hrs) hpar
      · by_contra hu0
        have hr0 : r ≠ 0 := fun h => hu0 (by rw [hu, h, neg_zero])
        have hrv : 0 < r.val := by rwa [Nat.pos_iff_ne_zero, ne_eq, ZMod.val_eq_zero]
        have hrlt : r.val < BLS12_381_SCALAR_CARD := ZMod.val_lt r
        rw [hu, ZMod.neg_val, if_neg hr0] at hpar
        omega
    have hs : LEOS2IP b / 2 ^ 255 = 1 := by
      rw [hu0, ZMod.val_zero] at hpar; omega
    have hn : LEOS2IP b = P.v.val + 2 ^ 255 := by omega
    rcases (u_eq_zero_iff P.onCurve).mp hu0 with h1 | h1
    · left
      rw [← I2LEOSP_LEOS2IP b]
      unfold zip216Identity
      congr 1
      apply Fin.ext
      show LEOS2IP b = 2 ^ 255 + 1
      rw [hn, h1, ZMod.val_one]
      omega
    · right
      rw [← I2LEOSP_LEOS2IP b]
      unfold zip216NegOne
      congr 1
      apply Fin.ext
      show LEOS2IP b = 2 ^ 255 + BLS12_381_SCALAR_CARD - 1
      rw [hn, h1, ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one]
      omega
  · rintro (rfl | rfl)
    · exact ⟨0, by decide, by decide⟩
    · exact ⟨zeroNegOne, by decide, by decide⟩

end CompElliptic.Curves.Jubjub

namespace CompElliptic

open CompElliptic.CurveForms.CtEdwards CompElliptic.Curves.Jubjub

/-- The canonical encoding of Jubjub points: `toBytes`, and `abst_𝕁` with ZIP 216's check that the
point re-encodes to the input. -/
def JubjubEncoding : CanonicalEncoding (CtEdwardsPoint curve) (Vector UInt8 32) :=
  JubjubLenientEncoding.toCanonical

end CompElliptic

namespace CompElliptic.Curves.Jubjub

open CompElliptic.CurveForms.CtEdwards CompElliptic.Fields.BLS12_381

/-- The decoder with ZIP 216's check, `JubjubEncoding`'s. Matches the `jubjub` crate's
`AffinePoint::from_bytes`. -/
def fromBytes (b : Vector UInt8 32) : Option (CtEdwardsPoint curve) := JubjubEncoding.decode b

/-- `fromBytes` is `fromBytesPreZip216`, keeping the point only if it re-encodes to the input. -/
theorem fromBytes_eq (b : Vector UInt8 32) :
    fromBytes b = (fromBytesPreZip216 b).filter fun P => toBytes P = b := rfl

/-- **What `fromBytes` rejects**: a byte string exactly when
`fromBytesPreZip216` does, or it is one of the two non-canonical encodings of ZIP 216. -/
theorem fromBytes_eq_none_iff (b : Vector UInt8 32) :
    fromBytes b = none ↔
      fromBytesPreZip216 b = none ∨ b = zip216Identity ∨ b = zip216NegOne := by
  rw [fromBytes_eq]
  rcases h : fromBytesPreZip216 b with _ | P
  · simp
  · rw [← nonCanonical_iff]
    simp only [Option.filter_some, reduceCtorEq, false_or]
    constructor
    · intro h0
      refine ⟨P, h, fun e => ?_⟩
      simp [e] at h0
    · rintro ⟨P', hP', hne⟩
      rw [h] at hP'
      obtain rfl := Option.some.inj hP'
      simp [hne]

/-! ### Fixtures against the `jubjub` crate (ZIP 216)

The crate's `test_zip_216`
(<https://github.com/zkcrypto/jubjub/blob/0cabeca668d89f9e8edbb3cbccdefeffdf21f651/src/lib.rs#L1903>)
lists the two non-canonical encodings, quoted below verbatim in hex, and checks that `from_bytes`
rejects them while `from_bytes_pre_zip216_compatibility` accepts them. -/

example : zip216Identity.toList =
    [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
     0x00, 0x80] := by
  decide

example : zip216NegOne.toList =
    [0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xfe, 0x5b, 0xfe, 0xff, 0x02, 0xa4, 0xbd,
     0x53, 0x05, 0xd8, 0xa1, 0x09, 0x08, 0xd8, 0x39, 0x33, 0x48, 0x7d, 0x9d, 0x29, 0x53, 0xa7,
     0xed, 0xf3] := by
  decide

example : fromBytesPreZip216 zip216Identity = some 0 := by decide
example : fromBytesPreZip216 zip216NegOne = some zeroNegOne := by decide
example : fromBytes zip216Identity = none := by decide
example : fromBytes zip216NegOne = none := by decide
example : fromBytes (toBytes uThreePoint) = some uThreePoint := by decide +kernel

end CompElliptic.Curves.Jubjub
