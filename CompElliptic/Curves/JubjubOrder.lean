/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Julian Abraham
-/
import CompElliptic.Curves.JubjubWitnesses
import CompElliptic.CurveOrder

/-!
# The order of the Jubjub curve group

The Jubjub curve group has order `8·r_𝕁`, and has a unique subgroup of order `r_𝕁`, the
counterpart of `𝕁⁽ʳ⁾` in the Zcash Protocol Specification §5.4.9.3 "Jubjub". Here `r_𝕁` is
`JUBJUB_SCALAR_CARD`, the prime written `ℓ` in `Fields/Jubjub.lean`, and `q` is the size of the
base field. Both facts are about the short-Weierstrass model `Jubjub.SW.curve`; transferring them to
the twisted Edwards curve needs the group isomorphism, which is not defined here.

No point counting is needed, and no Hasse bound:

1. the witnesses `Gpt` (order `r_𝕁`) and `Tpt` (order `8`) give `8·r_𝕁 ∣ #E`;
2. the fibre bound `#E ≤ 2·q + 1 < 24·r_𝕁` leaves `8·r_𝕁` and `16·r_𝕁`;
3. the twist witness `Wpt` rules out `16·r_𝕁` (`CurveOrder.card_eq_of_twist_witness`).

Every witness is checked by the kernel (`Curves/JubjubWitnesses.lean`), so nothing here uses
`native_decide`.
-/

namespace CompElliptic.Curves.Jubjub.SW

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder
  CompElliptic.Fields.BLS12_381 CompElliptic.Fields.Jubjub

/-- **The Jubjub curve group has order `8·r_𝕁`.** -/
theorem card_eq : Nat.card (SWPoint curve) = 8 * JUBJUB_SCALAR_CARD := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq : Fintype.card BLS12381ScalarField = BLS12_381_SCALAR_CARD := ZMod.card _
  have hr : JUBJUB_SCALAR_CARD ∣ Nat.card (SWPoint curve) :=
    dvd_natCard_of_prime_witness JUBJUB_SCALAR_is_prime Gpt_ne_zero r_nsmul_Gpt
  -- `addOrderOf_eq_prime_pow` states the order as `p^(n+1)`, hence `2^(2+1)` for `8`.
  have hT : addOrderOf Tpt = 2^(2+1) :=
    addOrderOf_eq_prime_pow (p := 2) (n := 2) four_nsmul_Tpt_ne_zero eight_nsmul_Tpt
  have h8 : 2^(2+1) ∣ Nat.card (SWPoint curve) := hT ▸ addOrderOf_dvd_natCard Tpt
  replace h8 : 8 ∣ Nat.card (SWPoint curve) := by simpa using h8
  refine card_eq_of_twist_witness (by decide) curve twist seven_not_isSquare rfl rfl
    (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by decide) h8 hr) (W := Wpt) ?_ ?_
  · rw [hq]; decide
  · rw [hq]; exact Wpt_witness

/-- The subgroup of order `r_𝕁`, the counterpart in this model of `𝕁⁽ʳ⁾` (§5.4.9.3): the points
killed by `r_𝕁`. -/
def primeOrderSubgroup : AddSubgroup (SWPoint curve) :=
  AddSubgroup.torsionBy (SWPoint curve) (JUBJUB_SCALAR_CARD : ℤ)

/-- `primeOrderSubgroup` has `r_𝕁` points. -/
theorem card_primeOrderSubgroup : Nat.card primeOrderSubgroup = JUBJUB_SCALAR_CARD :=
  card_torsionBy_eq JUBJUB_SCALAR_is_prime card_eq (by decide)

/-- `primeOrderSubgroup` is the only subgroup of order `r_𝕁`. -/
theorem eq_primeOrderSubgroup (K : AddSubgroup (SWPoint curve))
    (hK : Nat.card K = JUBJUB_SCALAR_CARD) : K = primeOrderSubgroup :=
  eq_torsionBy_of_card_eq JUBJUB_SCALAR_is_prime card_eq (by decide) K hK

end CompElliptic.Curves.Jubjub.SW
