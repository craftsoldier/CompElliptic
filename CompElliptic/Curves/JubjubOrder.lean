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
base field. Both facts are first proved for the short-Weierstrass model `Jubjub.SW.curve`. The
order is then carried to the twisted Edwards curve `Jubjub.curve` along `Jubjub.swEquiv`, and
gives `𝕁⁽ʳ⁾` there and its uniqueness in the same way (`§ The ctEdwards curve`), with the facts
about small order that the specification relies on and the injectivity of the `u`-coordinate on
`𝕁⁽ʳ⁾`.

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

/-! ## The ctEdwards curve

The order of `Jubjub.curve`, carried along `swEquiv`, and its subgroup `𝕁⁽ʳ⁾`, which `swEquiv`
maps onto `SW.primeOrderSubgroup`; the cofactor map
`P ↦ [8] P` onto `𝕁⁽ʳ⁾`; points of small order (Zcash Protocol Specification
[§5.4.9.5 "Group Hash into
Jubjub"](https://zips.z.cash/protocol/protocol.pdf#concretegrouphashjubjub) and
[§A.3.3.6 "Affine-ctEdwards nonsmall-order
check"](https://zips.z.cash/protocol/protocol.pdf#cctednonsmallorder)); and the injectivity of
the `u`-coordinate on `𝕁⁽ʳ⁾` ([§5.4.9.4 "Coordinate Extractor for
Jubjub"](https://zips.z.cash/protocol/protocol.pdf#concreteextractorjubjub)). A point is of small
order when `[8] P = 0`, as in the specification. -/

namespace CompElliptic.Curves.Jubjub

open CompElliptic.CurveForms.CtEdwards CompElliptic.CurveOrder CompElliptic.Fields.Jubjub

/-- **The Jubjub curve group has order `8·r_𝕁`.** -/
theorem card_eq : Nat.card (CtEdwardsPoint curve) = 8 * JUBJUB_SCALAR_CARD :=
  (Nat.card_congr swEquiv.toEquiv).trans SW.card_eq

/-- `𝕁⁽ʳ⁾` (§5.4.9.3): the points killed by `r_𝕁`. -/
def primeOrderSubgroup : AddSubgroup (CtEdwardsPoint curve) :=
  AddSubgroup.torsionBy (CtEdwardsPoint curve) (JUBJUB_SCALAR_CARD : ℤ)

/-- `swEquiv` maps `𝕁⁽ʳ⁾` onto `SW.primeOrderSubgroup`. -/
theorem swEquiv_mem_primeOrderSubgroup_iff (P : CtEdwardsPoint curve) :
    swEquiv P ∈ SW.primeOrderSubgroup ↔ P ∈ primeOrderSubgroup := by
  simp only [SW.primeOrderSubgroup, primeOrderSubgroup, AddSubgroup.torsionBy.nsmul_iff,
    ← map_nsmul, AddEquiv.map_eq_zero_iff]

/-- `𝕁⁽ʳ⁾` has `r_𝕁` points. -/
theorem card_primeOrderSubgroup : Nat.card primeOrderSubgroup = JUBJUB_SCALAR_CARD :=
  card_torsionBy_eq JUBJUB_SCALAR_is_prime card_eq (by decide)

/-- `𝕁⁽ʳ⁾` is the only subgroup of order `r_𝕁`. -/
theorem eq_primeOrderSubgroup (K : AddSubgroup (CtEdwardsPoint curve))
    (hK : Nat.card K = JUBJUB_SCALAR_CARD) : K = primeOrderSubgroup :=
  eq_torsionBy_of_card_eq JUBJUB_SCALAR_is_prime card_eq (by decide) K hK

/-- `[8] P` is in `𝕁⁽ʳ⁾` for every point `P`. -/
theorem eight_nsmul_mem_primeOrderSubgroup (P : CtEdwardsPoint curve) :
    8 • P ∈ primeOrderSubgroup :=
  nsmul_mem_torsionBy card_eq P

/-- **`P ↦ [8] P` maps the curve onto `𝕁⁽ʳ⁾`** (§5.4.9.5). -/
theorem range_eight_nsmul :
    (nsmulAddMonoidHom (α := CtEdwardsPoint curve) 8).range = primeOrderSubgroup :=
  range_nsmul_eq_torsionBy JUBJUB_SCALAR_is_prime card_eq (by decide)

/-- **`P ↦ [8] P` is exactly `8`-to-`1` onto `𝕁⁽ʳ⁾`** (§5.4.9.5): each point of `𝕁⁽ʳ⁾` is
`[8] P` for exactly `8` points `P`. -/
theorem card_eight_nsmul_fibre {Q : CtEdwardsPoint curve} (hQ : Q ∈ primeOrderSubgroup) :
    Nat.card {P : CtEdwardsPoint curve // 8 • P = Q} = 8 :=
  card_nsmul_fibre JUBJUB_SCALAR_is_prime card_eq (by decide) hQ

/-- A point not of small order has order divisible by `r_𝕁`: its order divides `8·r_𝕁`, and if
`r_𝕁` did not divide it, it would divide `8`. -/
theorem dvd_addOrderOf_of_eight_nsmul_ne_zero {P : CtEdwardsPoint curve} (hP : 8 • P ≠ 0) :
    JUBJUB_SCALAR_CARD ∣ addOrderOf P := by
  by_contra hr
  have hdvd : addOrderOf P ∣ 8 * JUBJUB_SCALAR_CARD := card_eq ▸ addOrderOf_dvd_natCard P
  have hcop : Nat.Coprime (addOrderOf P) JUBJUB_SCALAR_CARD :=
    ((Nat.Prime.coprime_iff_not_dvd JUBJUB_SCALAR_is_prime).2 hr).symm
  exact hP (addOrderOf_dvd_iff_nsmul_eq_zero.mp (hcop.dvd_of_dvd_mul_right hdvd))

/-- **The small-order test** (§A.3.3.6): `P` is of small order exactly when `[4] P` has
`u = 0`. The only points with `u = 0` are `0` and `(0, −1)` (`u_eq_zero_iff`), which are the
points killed by `2` (`CtEdwardsPoint.two_nsmul_eq_zero_iff`). -/
theorem eight_nsmul_eq_zero_iff_u_eq_zero (P : CtEdwardsPoint curve) :
    8 • P = 0 ↔ (4 • P).u = 0 := by
  rw [show 8 • P = 2 • (4 • P) by rw [smul_smul]; rfl, CtEdwardsPoint.two_nsmul_eq_zero_iff,
    u_eq_zero_iff (4 • P).onCurve]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact Or.inl (by rw [h]; rfl)
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl (CtEdwardsPoint.eq_zero_of_v_eq_one h)
    · exact Or.inr ⟨Or.inr h, h⟩

/-- The point `(0, −1)`, of order `2`. -/
def zeroNegOne : CtEdwardsPoint curve := ⟨0, -1, by simp [OnCurve]⟩

/-- `(0, −1)` is not in `𝕁⁽ʳ⁾`: it has order `2`, and `r_𝕁` is odd. -/
theorem zeroNegOne_not_mem_primeOrderSubgroup : zeroNegOne ∉ primeOrderSubgroup := by
  have h2 : 2 • zeroNegOne = 0 :=
    CtEdwardsPoint.two_nsmul_eq_zero_iff.mpr (Or.inr ⟨rfl, rfl⟩)
  have hne : zeroNegOne ≠ 0 := fun h => by
    have : zeroNegOne.v = (0 : CtEdwardsPoint curve).v := by rw [h]
    exact absurd this (by decide)
  intro hmem
  have hr : JUBJUB_SCALAR_CARD • zeroNegOne = 0 := AddSubgroup.torsionBy.nsmul_iff.mp hmem
  obtain ⟨m, hm⟩ : ∃ m, JUBJUB_SCALAR_CARD = 2 * m + 1 := ⟨JUBJUB_SCALAR_CARD / 2, by decide⟩
  rw [hm, succ_nsmul, mul_nsmul, h2, nsmul_zero, _root_.zero_add] at hr
  exact hne hr

/-- **`(0, −1)` is not `[8] P` for any `P`** (§A.3.3.6): `[8] P` is in `𝕁⁽ʳ⁾`, and `(0, −1)` is
not. -/
theorem eight_nsmul_ne_zeroNegOne (P : CtEdwardsPoint curve) : 8 • P ≠ zeroNegOne :=
  fun h => zeroNegOne_not_mem_primeOrderSubgroup (h ▸ eight_nsmul_mem_primeOrderSubgroup P)

/-- **The nonsmall-order check** (§A.3.3.6): `[8] P` has `u = 0` exactly when it is `0`, since
the only other point with `u = 0`, `(0, −1)`, is never `[8] P` (`eight_nsmul_ne_zeroNegOne`). So
checking that the `u`-coordinate of `[8] P` is nonzero rejects exactly the points of small
order. -/
theorem eight_nsmul_u_eq_zero_iff (P : CtEdwardsPoint curve) : (8 • P).u = 0 ↔ 8 • P = 0 := by
  constructor
  · intro h
    rcases (u_eq_zero_iff (8 • P).onCurve).mp h with hv | hv
    · exact CtEdwardsPoint.eq_zero_of_v_eq_one hv
    · exact absurd (CtEdwardsPoint.ext_pair (by rw [h, hv]; rfl)) (eight_nsmul_ne_zeroNegOne P)
  · intro h; rw [h]; rfl

/-- The point `(u, −v)`, on the curve whenever `(u, v)` is. -/
def negV (P : CtEdwardsPoint curve) : CtEdwardsPoint curve :=
  ⟨P.u, -P.v, by have h := P.onCurve; simp only [OnCurve] at h ⊢; linear_combination h⟩

/-- `(u, −v)` is `(0, −1) − P`. -/
theorem negV_eq (P : CtEdwardsPoint curve) : negV P = zeroNegOne + -P := by
  refine CtEdwardsPoint.ext_pair ?_
  show (P.u, -P.v) = add curve.a curve.d (0, -1) (-P.u, P.v)
  simp [add]

/-- **The lemma of §5.4.9.4**: if `(u, v)` is in `𝕁⁽ʳ⁾`, then `(u, −v)` is not. Otherwise
`(0, −1) = (u, −v) + (u, v)` would be in `𝕁⁽ʳ⁾` (`negV_eq`), and it is not. -/
theorem negV_not_mem_primeOrderSubgroup {P : CtEdwardsPoint curve} (hP : P ∈ primeOrderSubgroup) :
    negV P ∉ primeOrderSubgroup := by
  intro h
  apply zeroNegOne_not_mem_primeOrderSubgroup
  have := primeOrderSubgroup.add_mem h hP
  rwa [negV_eq, neg_add_cancel_right] at this

/-- **The theorem of §5.4.9.4: the `u`-coordinate is injective on `𝕁⁽ʳ⁾`.** Two points with the
same `u` have `v² (1 − d·u²) = 1 − a·u²` with `1 − d·u² ≠ 0`, so the same `v` up to sign; by the
lemma, `(u, −v)` is not in `𝕁⁽ʳ⁾`. -/
theorem u_injOn_primeOrderSubgroup {P Q : CtEdwardsPoint curve} (hP : P ∈ primeOrderSubgroup)
    (hQ : Q ∈ primeOrderSubgroup) (h : P.u = Q.u) : P = Q := by
  have cP : curve.a * P.u ^ 2 + P.v ^ 2 = 1 + curve.d * P.u ^ 2 * P.v ^ 2 := P.onCurve
  have cQ : curve.a * Q.u ^ 2 + Q.v ^ 2 = 1 + curve.d * Q.u ^ 2 * Q.v ^ 2 := Q.onCurve
  rw [← h] at cQ
  -- `1 − d·u² ≠ 0`: otherwise `d = (1/u)²` would be a square.
  have hdu : 1 - curve.d * P.u ^ 2 ≠ 0 := by
    intro e
    have hu : P.u ≠ 0 := fun hu => by rw [hu] at e; simp at e
    exact curve.d_nonsquare ⟨P.u⁻¹, by field_simp; linear_combination -e⟩
  have e : (Q.v - P.v) * (Q.v + P.v) * (1 - curve.d * P.u ^ 2) = 0 := by
    linear_combination cQ - cP
  rcases mul_eq_zero.1 ((mul_eq_zero.1 e).resolve_right hdu) with h' | h'
  · exact CtEdwardsPoint.ext_pair (by rw [h, show P.v = Q.v by linear_combination -h'])
  · exfalso
    have hQn : Q = negV P := CtEdwardsPoint.ext_pair (by
      show (Q.u, Q.v) = (P.u, -P.v)
      rw [h, show Q.v = -P.v by linear_combination h'])
    exact negV_not_mem_primeOrderSubgroup hP (hQn ▸ hQ)

end CompElliptic.Curves.Jubjub
