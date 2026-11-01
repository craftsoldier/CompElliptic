/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Julian Abraham
-/
import CompElliptic.CurveForms.ShortWeierstrass
import CompElliptic.CurveForms.CtEdwardsMontgomery
import CompElliptic.Fields.BLS12_381

/-!
# The Jubjub curve

Jubjub (Zcash Protocol Specification
[§5.4.9.3 "Jubjub"](https://zips.z.cash/protocol/protocol.pdf#jubjub)) is the complete twisted
Edwards curve `a·u² + v² = 1 + d·u²·v²` over the BLS12-381 scalar field, with `a = -1` and
`d = -10240/10241`. This module gives it as an `SWCurve`, through the specification's Montgomery
curve `𝕄: y² = x³ + A·x² + x` with `A = 40962`
([§A.2 "Elliptic curve background"](https://zips.z.cash/protocol/protocol.pdf#ecbackground)).
The coefficient of `y²` in `𝕄` is `1`, so `𝕄` is already a Weierstrass curve, and the
translation `x ↦ x + A/3` takes it to

`y² = x³ + a₄·x + a₆`, with `a₄ = (3 - A²)/3 = -559295147` and
`a₆ = (2·A³ - 9·A)/27 = 5091077286874`.

The module then gives Jubjub itself as a `CtEdwardsCurve`, `curve` (`§ The ctEdwards curve`), and
the additive equivalence `swEquiv` between its points and those of `SW.curve`: the twisted Edwards
to Montgomery isomorphism of `CurveForms/CtEdwardsMontgomery.lean`, onto Mathlib's model of the
Montgomery curve with `B = 4/(a − d) = −40964`, followed by the change of variables
`(X, Y) ↦ (s²·X + A/3, s³·Y)` with `s = √⁺(−40964)`, whose scaling takes that model onto `𝕄` and
whose translation takes `𝕄` onto `SW.curve`. Away from the points where the specification leaves
them undefined, its conversion maps `ctEdwardsToMont` and `montToCtEdwards` are this equivalence
in `𝕄`'s coordinates (`swEquiv_eq_ctEdwardsToMont`, `swEquiv_symm_eq_montToCtEdwards`).

The coefficients of `SW.curve` and of `curve`, and the constants of the change of variables,
are literals, each proved equal to its formula in the specification's parameters, so the kernel
never inverts a field element to evaluate them.
-/

namespace CompElliptic.Curves.Jubjub

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Fields.BLS12_381

/-- The twisted Edwards parameter `a = -1` (§5.4.9.3). -/
def a : BLS12381ScalarField := -1

/-- The twisted Edwards parameter `d = -10240/10241` (§5.4.9.3). -/
def d : BLS12381ScalarField := -10240 / 10241

/-- The literal value of `d`, which is `EDWARDS_D` in the `jubjub` crate. -/
theorem d_eq :
    d = 19257038036680949359750312669786877991949435402254120286184196891950884077233 := by
  unfold d
  rw [div_eq_iff (by decide)]
  decide

/-- The coefficient `A = 40962` of the Montgomery curve `𝕄` (§A.2). -/
def montA : BLS12381ScalarField := 40962

/-- `A = 2·(a + d)/(a - d)`: the `A` of the Montgomery curve birationally equivalent to Jubjub
(Bernstein–Birkner–Joye–Lange–Peters,
[Twisted Edwards Curves](https://cr.yp.to/newelliptic/twisted-20080313.pdf), Theorem 3.2).
That curve has `B = 4/(a - d)`; the change of variables `swChange` relates it to `𝕄`, which has
`B = 1` (`montgomery_eq_swChange_smul`). -/
theorem montA_eq : montA = 2 * (a + d) / (a - d) := by
  rw [d_eq, eq_div_iff (by unfold a; decide)]
  unfold montA a
  decide

namespace SW

/-- The short-Weierstrass coefficient `a₄ = -559295147`. -/
def a₄ : BLS12381ScalarField := -559295147

/-- The short-Weierstrass coefficient `a₆ = 5091077286874`. -/
def a₆ : BLS12381ScalarField := 5091077286874

/-- `a₄ = (3 - A²)/3`, from translating `𝕄` by `x ↦ x + A/3`. -/
theorem a₄_eq : a₄ = (3 - montA^2) / 3 := by
  rw [eq_div_iff (by decide)]
  unfold a₄ montA
  decide

/-- `a₆ = (2·A³ - 9·A)/27`, from translating `𝕄` by `x ↦ x + A/3`. -/
theorem a₆_eq : a₆ = (2 * montA^3 - 9 * montA) / 27 := by
  rw [eq_div_iff (by decide)]
  unfold a₆ montA
  decide

/-- Jubjub's short-Weierstrass model, `y² = x³ + a₄·x + a₆`. -/
def curve : SWCurve BLS12381ScalarField where
  A := a₄
  B := a₆
  IsElliptic := by rw [isUnit_iff_ne_zero]; decide
  B_nonzero := by decide

/-- `curve` is `𝕄` translated by `x ↦ x + A/3`: `(x + A/3, y)` is on `curve` exactly when
`y² = x³ + A·x² + x`. -/
theorem onCurve_iff_mont (x y : BLS12381ScalarField) :
    OnCurve curve.A curve.B (x + montA / 3, y) ↔ y^2 = x^3 + montA * x^2 + x := by
  have h3 : montA / 3 = 13654 := by rw [div_eq_iff (by decide)]; unfold montA; decide
  -- Expand the translated cubic; its three leftover coefficients vanish in the field.
  have key : (x + 13654)^3 + (-559295147) * (x + 13654) + 5091077286874 =
      x^3 + 40962 * x^2 + x + ((13654 : BLS12381ScalarField)^3 - 559295147 * 13654 +
        5091077286874) + (3 * 13654 - 40962) * x^2 + (3 * 13654^2 - 559295147 - 1) * x := by
    ring
  have c0 : (13654 : BLS12381ScalarField)^3 - 559295147 * 13654 + 5091077286874 = 0 := by decide
  have c1 : (3 : BLS12381ScalarField) * 13654 - 40962 = 0 := by decide
  have c2 : (3 : BLS12381ScalarField) * 13654^2 - 559295147 - 1 = 0 := by decide
  show y^2 = (x + montA / 3)^3 + curve.A * (x + montA / 3) + curve.B ↔ _
  rw [h3, show curve.A = -559295147 from rfl, show curve.B = 5091077286874 from rfl, key, c0, c1,
    c2, show montA = 40962 from rfl]
  constructor <;> intro h <;> linear_combination h

/-- The quadratic twist of `curve` by the non-square `7` (`seven_not_isSquare`):
`y² = x³ + 7²·a₄·x + 7³·a₆`. -/
def twist : SWCurve BLS12381ScalarField where
  A := 7^2 * a₄
  B := 7^3 * a₆
  IsElliptic := by rw [isUnit_iff_ne_zero]; decide
  B_nonzero := by decide

end SW

/-! ## The ctEdwards curve

Jubjub as a complete twisted Edwards curve (§5.4.9.3), and its points against those of
`SW.curve`. -/

open CompElliptic.CurveForms CompElliptic.CurveForms.CtEdwards

/-- `a = −1` is a square in the BLS12-381 scalar field. -/
theorem a_square : IsSquare a :=
  ⟨3465144826073652318776269530687742778270252468765361963008, by unfold a; decide⟩

/-- `d` is not a square in the BLS12-381 scalar field, by Euler's criterion. -/
theorem d_nonsquare : ¬ IsSquare d := by
  rw [d_eq, ZMod.euler_criterion BLS12_381_SCALAR_CARD (by decide)]
  reduce_mod_char
  decide

/-- Jubjub as a complete twisted Edwards curve, `a·u² + v² = 1 + d·u²·v²` (§5.4.9.3), with `d`
as its literal value (`d_eq`). -/
def curve : CtEdwardsCurve BLS12381ScalarField where
  a := a
  d := 19257038036680949359750312669786877991949435402254120286184196891950884077233
  a_nonzero := by unfold a; decide
  a_square := a_square
  d_nonsquare := d_eq ▸ d_nonsquare
  F_nonbinary := by decide

/-- `√⁺(−40964)`, the square root of `−40964` in `[0, (q − 1)/2]`
([§2 "Notation"](https://zips.z.cash/protocol/protocol.pdf#notation)), which the specification uses
to convert between ctEdwards and Montgomery coordinates ([§A.3.3.3 "ctEdwards ↔ Montgomery
conversion"](https://zips.z.cash/protocol/protocol.pdf#cctconversion)). It is
`MONTGOMERY_SCALE` in the `sapling-crypto` crate. -/
def montScale : BLS12381ScalarField :=
  17814886934372412843466061268024708274627479829237077604635722030778476050649

/-- `montScale` is a square root of `−40964`. -/
theorem montScale_sq : montScale ^ 2 = -40964 := by unfold montScale; decide

/-- `montScale` is in `[0, (q − 1)/2]`, so it is the root `√⁺(−40964)` and not its negation. -/
theorem montScale_val_le : montScale.val ≤ (BLS12_381_SCALAR_CARD - 1) / 2 := by
  unfold montScale; decide

/-- `montScale` is nonzero. -/
theorem montScale_ne_zero : montScale ≠ 0 := by unfold montScale; decide

/-- The Montgomery curve of `curve` (`CtEdwardsCurve.montgomery`) has `A = 40962`. -/
theorem curve_montA : curve.montA = montA := by
  rw [CtEdwardsCurve.montA, montA_eq, show curve.a = a from rfl, show curve.d = d from d_eq.symm]

/-- The Montgomery curve of `curve` has `B = 4/(a − d) = −40964`. -/
theorem curve_montB : curve.montB = -40964 := by
  rw [CtEdwardsCurve.montB, show curve.a = a from rfl, show curve.d = d from d_eq.symm, d_eq,
    div_eq_iff (by unfold a; decide)]
  unfold a
  decide

/-- `A/3 = 13654`, the translation from `𝕄` to `SW.curve`. -/
theorem montA_div_three : montA / 3 = 13654 := by
  rw [div_eq_iff (by decide)]; unfold montA; decide

/-- The change of variables `x = s²·x' + A/3`, `y = s³·y'` with `s = montScale`, written with
`A/3 = 13654` (`montA_div_three`). -/
def swChange : WeierstrassCurve.VariableChange BLS12381ScalarField :=
  ⟨Units.mk0 montScale montScale_ne_zero, 13654, 0, 0⟩

/-- The Mathlib model of `curve`'s Montgomery curve is `swChange • SW.curve`. -/
theorem montgomery_eq_swChange_smul :
    curve.montgomery = swChange • ShortWeierstrass.toW SW.curve.A SW.curve.B := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := Montgomery.variableChange_coeffs
    (W := ShortWeierstrass.toW SW.curve.A SW.curve.B) (C := swChange) rfl rfl
  have hu : (swChange.u : BLS12381ScalarField) = montScale := rfl
  have hr : swChange.r = 13654 := rfl
  have hi : (swChange.u : BLS12381ScalarField)⁻¹ ^ 2 = curve.montB⁻¹ := by
    rw [hu, inv_pow, montScale_sq, curve_montB]
  simp only [ShortWeierstrass.toW_a₁, ShortWeierstrass.toW_a₂, ShortWeierstrass.toW_a₃,
    ShortWeierstrass.toW_a₄, ShortWeierstrass.toW_a₆, hr] at h₁ h₂ h₃ h₄ h₆
  ext
  · rw [h₁, mul_zero]; rfl
  · rw [h₂, hi, show (0 : BLS12381ScalarField) + 3 * 13654 = montA by unfold montA; decide,
      ← curve_montA]
    show curve.montA / curve.montB = _
    rw [div_eq_inv_mul]
  · rw [h₃, mul_zero, _root_.add_zero, mul_zero]; rfl
  · rw [h₄, show (swChange.u : BLS12381ScalarField)⁻¹ ^ 4 =
        ((swChange.u : BLS12381ScalarField)⁻¹ ^ 2) ^ 2 by ring, hi,
      show SW.curve.A + 2 * 13654 * 0 + 3 * 13654 ^ 2 = 1 by decide, mul_one]
    show 1 / curve.montB ^ 2 = _
    rw [one_div, inv_pow]
  · rw [h₆, show SW.curve.B + 13654 * SW.curve.A + 13654 ^ 2 * 0 + 13654 ^ 3 = 0 by decide,
      mul_zero]
    rfl

/-- **The additive equivalence** between the points of `curve` and those of `SW.curve`. -/
def swEquiv : CtEdwardsPoint curve ≃+ SWPoint SW.curve :=
  CtEdwardsPoint.montgomeryEquiv.trans ((Montgomery.variableChangeEquiv rfl rfl
    montgomery_eq_swChange_smul).trans (SWPoint.equivPoint SW.curve).symm)

/-- The specification's `CtEdwardsToMont` (§A.3.3.3), on coordinates:
`(u, v) ↦ ((1 + v)/(1 − v), √⁺(−40964)·(1 + v)/((1 − v)·u))`. -/
def ctEdwardsToMont (p : BLS12381ScalarField × BLS12381ScalarField) :
    BLS12381ScalarField × BLS12381ScalarField :=
  ((1 + p.2) / (1 - p.2), montScale * ((1 + p.2) / ((1 - p.2) * p.1)))

/-- The specification's `MontToCtEdwards` (§A.3.3.3), on coordinates:
`(x, y) ↦ (√⁺(−40964)·x/y, (x − 1)/(x + 1))`. -/
def montToCtEdwards (p : BLS12381ScalarField × BLS12381ScalarField) :
    BLS12381ScalarField × BLS12381ScalarField :=
  (montScale * (p.1 / p.2), (p.1 - 1) / (p.1 + 1))

/-- **`swEquiv` is `CtEdwardsToMont`**, followed by the translation `x ↦ x + A/3` from `𝕄` to
`SW.curve`, at every point other than the identity `(0, 1)`. The specification defines
`CtEdwardsToMont` where `1 − v ≠ 0` and `u ≠ 0`; the formula here also covers `(0, −1)`, where
Lean's `x/0 = 0` makes it `(0, 0)`, the image of `(0, −1)`. -/
theorem swEquiv_eq_ctEdwardsToMont (P : CtEdwardsPoint curve) (hv : P.v ≠ 1) :
    ((swEquiv P).x - montA / 3, (swEquiv P).y) = ctEdwardsToMont (P.u, P.v) := by
  have hB : curve.montB ≠ 0 := curve.montB_ne_zero
  have hs : montScale ^ 2 = curve.montB := by rw [montScale_sq, curve_montB]
  have e : swEquiv P = SWPoint.ofPoint (Montgomery.variableChangeMap rfl rfl
      montgomery_eq_swChange_smul (CtEdwardsPoint.toMontgomery P)) := rfl
  rw [e, CtEdwardsPoint.toMontgomery, dif_neg hv, Montgomery.variableChangeMap_some,
    SWPoint.ofPoint_some, montA_div_three]
  show (montScale ^ 2 * ((toMontgomeryXY (P.u, P.v)).1 / curve.montB) + 13654 - 13654,
    montScale ^ 3 * ((toMontgomeryXY (P.u, P.v)).2 / curve.montB)) = _
  rw [add_sub_cancel_right, hs, mul_div_cancel₀ _ hB, show montScale ^ 3 = montScale * montScale ^ 2
    by ring, hs, mul_assoc, mul_div_cancel₀ _ hB]
  rfl

/-- **`swEquiv.symm` is `MontToCtEdwards`**, after the translation `x ↦ x − A/3` from `SW.curve`
to `𝕄`, at every point with `y ≠ 0`. The specification defines `MontToCtEdwards` where
`x + 1 ≠ 0` and `y ≠ 0`; the proof needs only `y ≠ 0`. -/
theorem swEquiv_symm_eq_montToCtEdwards (Q : SWPoint SW.curve) (hy : Q.y ≠ 0) :
    ((swEquiv.symm Q).u, (swEquiv.symm Q).v) = montToCtEdwards (Q.x - montA / 3, Q.y) := by
  set P := swEquiv.symm Q
  have hQ : swEquiv P = Q := swEquiv.apply_symm_apply Q
  have hv : P.v ≠ 1 := by
    intro e
    apply hy
    rw [← hQ, CtEdwardsPoint.eq_zero_of_v_eq_one e, map_zero]
    rfl
  have e := swEquiv_eq_ctEdwardsToMont P hv
  rw [hQ] at e
  simp only [ctEdwardsToMont, Prod.mk.injEq] at e
  obtain ⟨ex, ey⟩ := e
  have hs : montScale ≠ 0 := montScale_ne_zero
  have hm : 1 - P.v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv)
  have h1 : 1 + P.v ≠ 0 := fun h => hy (by rw [ey, h, zero_div, mul_zero])
  have hu : P.u ≠ 0 := fun h => hy (by rw [ey, h, mul_zero, div_zero, mul_zero])
  have h2 : (2 : BLS12381ScalarField) ≠ 0 := by decide
  rw [ex, ey]
  simp only [montToCtEdwards, Prod.mk.injEq]
  constructor
  · field_simp
  · rw [div_sub_one hm, div_add_one hm, div_div_div_cancel_right₀ hm,
      eq_div_iff (by rw [show 1 + P.v + (1 - P.v) = 2 by ring]; exact h2)]
    ring

/-- **Distinct `x` on `𝕄`.** For `Q` of order `s` on Jubjub and nonzero `k₁`, `k₂` with
`|kᵢ| ≤ (s − 1)/2` and `k₂ ≠ ±k₁`, the points `[k₁] Q` and `[k₂] Q` have distinct Montgomery
`x`-coordinates, `CtEdwardsToMont`'s first component: the curve fact behind the Distinct-`x`
theorem ([§A.3.3.4 "Affine-Montgomery
arithmetic"](https://zips.z.cash/protocol/protocol.pdf#cctmontarithmetic)),
`SWPoint.x_ne_of_addOrderOf` carried along `swEquiv`. -/
theorem ctEdwardsToMont_fst_ne {Q : CtEdwardsPoint curve} {s : ℕ} (hQ : addOrderOf Q = s)
    {k₁ k₂ : ℤ} (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0) (hb₁ : |k₁| ≤ ((s - 1) / 2 : ℕ))
    (hb₂ : |k₂| ≤ ((s - 1) / 2 : ℕ)) (hne : k₂ ≠ k₁) (hne' : k₂ ≠ -k₁) :
    (ctEdwardsToMont ((k₁ • Q).u, (k₁ • Q).v)).1 ≠
      (ctEdwardsToMont ((k₂ • Q).u, (k₂ • Q).v)).1 := by
  have hQ' : addOrderOf (swEquiv Q) = s := by
    rw [AddEquiv.addOrderOf_eq, hQ]
  have hv (k : ℤ) (hk : k ≠ 0) (hb : |k| ≤ ((s - 1) / 2 : ℕ)) : (k • Q).v ≠ 1 := by
    have h1 : (1 : ℤ) ≤ ((s - 1) / 2 : ℕ) := (Int.one_le_abs hk).trans hb
    intro e
    refine SWPoint.zsmul_ne_zero_of_abs_lt hQ' hk (by omega) ?_
    rw [← map_zsmul, CtEdwardsPoint.eq_zero_of_v_eq_one e, map_zero]
  have hx (k : ℤ) (hk : k ≠ 0) (hb : |k| ≤ ((s - 1) / 2 : ℕ)) :
      (ctEdwardsToMont ((k • Q).u, (k • Q).v)).1 = (k • swEquiv Q).x - montA / 3 := by
    rw [← map_zsmul, ← swEquiv_eq_ctEdwardsToMont _ (hv k hk hb)]
  rw [hx k₁ hk₁ hb₁, hx k₂ hk₂ hb₂]
  exact fun e => SWPoint.x_ne_of_addOrderOf hQ' hk₁ hk₂ hb₁ hb₂ hne hne' (sub_left_inj.mp e)

end CompElliptic.Curves.Jubjub
