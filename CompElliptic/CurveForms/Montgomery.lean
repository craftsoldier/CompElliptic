/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Julian Abraham
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Montgomery curves

The Montgomery curve form

`B·y² = x³ + A·x² + x`,

as in the Zcash Protocol Specification
[§A.2 "Elliptic curve background"](https://zips.z.cash/protocol/protocol.pdf#ecbackground).

The curve is given to Mathlib as the Weierstrass curve `toW A B`, `Y² = X³ + (A/B)·X² + X/B²`,
which the scaling `(x, y) ↦ (x/B, y/B)` reaches (`equation_toW`), so that Mathlib's group of
affine points applies. No translation to short Weierstrass form is made, so no condition on the
characteristic beyond `2 ≠ 0` is needed. The discriminant is `16·(A² − 4)/B⁶` (`toW_Δ`).

Mathlib's `addX`, `addY` at the scaled points are the curve's chord and tangent formulas,
scaled by `1/B`, and its slopes are the curve's slopes (`§ Chord and tangent`). The module
then gives the facts about exceptional points that the specification relies on
(`§ Exceptional points`), and closes with the changes of variables `x = u²·x' + r`, `y = u³·y'`
of Mathlib's `VariableChange`, by which a Mathlib model such as `toW A B` can be brought to short
Weierstrass form; each is an additive equivalence of affine points (`§ Changes of variables`).
-/

namespace CompElliptic.CurveForms.Montgomery

variable {F : Type*} [Field F]

/-- The curve equation `B·y² = x³ + A·x² + x`. -/
def OnCurve (A B : F) (p : F × F) : Prop := B * p.2 ^ 2 = p.1 ^ 3 + A * p.1 ^ 2 + p.1

/-- The curve as a Mathlib `WeierstrassCurve`, `Y² = X³ + (A/B)·X² + X/B²`. -/
def toW (A B : F) : WeierstrassCurve F :=
  { a₁ := 0, a₂ := A / B, a₃ := 0, a₄ := 1 / B ^ 2, a₆ := 0 }

@[simp] lemma toW_a₁ (A B : F) : (toW A B).a₁ = 0 := rfl
@[simp] lemma toW_a₂ (A B : F) : (toW A B).a₂ = A / B := rfl
@[simp] lemma toW_a₃ (A B : F) : (toW A B).a₃ = 0 := rfl
@[simp] lemma toW_a₄ (A B : F) : (toW A B).a₄ = 1 / B ^ 2 := rfl
@[simp] lemma toW_a₆ (A B : F) : (toW A B).a₆ = 0 := rfl

/-- The discriminant of `toW A B` is `16·(A² − 4)/B⁶`. -/
theorem toW_Δ (A B : F) : (toW A B).Δ = 16 * (A ^ 2 - 4) / B ^ 6 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, toW_a₁, toW_a₂, toW_a₃, toW_a₄, toW_a₆]
  ring

/-- `toW A B` is nonsingular when `2`, `B` and `A² − 4` are nonzero. -/
theorem isElliptic_toW {A B : F} (two : (2 : F) ≠ 0) (hB : B ≠ 0) (hA : A ^ 2 - 4 ≠ 0) :
    (toW A B).IsElliptic := by
  have h16 : (16 : F) ≠ 0 := by
    rw [show (16 : F) = 2 ^ 4 by norm_num]; exact pow_ne_zero 4 two
  exact ⟨isUnit_iff_ne_zero.2 (by
    rw [toW_Δ]; exact div_ne_zero (mul_ne_zero h16 hA) (pow_ne_zero 6 hB))⟩

/-- A point `(x, y)` is on the curve exactly when `(x/B, y/B)` is on `toW A B`. -/
theorem equation_toW {A B x y : F} (hB : B ≠ 0) :
    (toW A B).toAffine.Equation (x / B) (y / B) ↔ OnCurve A B (x, y) := by
  have e : (y / B) ^ 2 - ((x / B) ^ 3 + A / B * (x / B) ^ 2 + 1 / B ^ 2 * (x / B))
      = (B * y ^ 2 - (x ^ 3 + A * x ^ 2 + x)) / B ^ 3 := by
    field_simp
  rw [WeierstrassCurve.Affine.equation_iff, OnCurve, ← sub_eq_zero, ← sub_eq_zero (a := B * _)]
  simp only [toW_a₁, toW_a₂, toW_a₃, toW_a₄, toW_a₆, zero_mul, add_zero]
  rw [e, div_eq_zero_iff, or_iff_left (pow_ne_zero 3 hB)]

/-! ## Chord and tangent -/

/-- The chord-and-tangent formula for the `x`-coordinate of a sum, `B·ℓ² − A − x₁ − x₂`, where `ℓ`
is the slope of the line through `(x₁, y₁)` and `(x₂, y₂)` (the tangent, if they are equal). -/
def addX (A B x₁ x₂ ℓ : F) : F := B * ℓ ^ 2 - A - x₁ - x₂

/-- The matching formula for the `y`-coordinate, `ℓ·(x₁ − x₃) − y₁`, where
`x₃ = addX A B x₁ x₂ ℓ`. -/
def addY (A B x₁ x₂ y₁ ℓ : F) : F := ℓ * (x₁ - addX A B x₁ x₂ ℓ) - y₁

/-- Mathlib's `addX` on `toW A B` at the scaled points is `addX`, scaled. -/
theorem addX_toW {A B : F} (hB : B ≠ 0) (x₁ x₂ ℓ : F) :
    (toW A B).toAffine.addX (x₁ / B) (x₂ / B) ℓ = addX A B x₁ x₂ ℓ / B := by
  simp only [WeierstrassCurve.Affine.addX, toW_a₁, toW_a₂, addX]
  field_simp
  ring

/-- Mathlib's `addY` on `toW A B` at the scaled points is `addY`, scaled. -/
theorem addY_toW {A B : F} (hB : B ≠ 0) (x₁ x₂ y₁ ℓ : F) :
    (toW A B).toAffine.addY (x₁ / B) (x₂ / B) (y₁ / B) ℓ = addY A B x₁ x₂ y₁ ℓ / B := by
  simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX, toW_a₁, toW_a₂, toW_a₃, addY,
    addX]
  field_simp
  ring

variable [DecidableEq F]

/-- Through two points with distinct `x`, Mathlib's slope at the scaled points is the chord slope
`(y₁ − y₂)/(x₁ − x₂)`. -/
theorem slope_toW_of_x_ne {A B x₁ x₂ y₁ y₂ : F} (hB : B ≠ 0) (hx : x₁ ≠ x₂) :
    (toW A B).toAffine.slope (x₁ / B) (x₂ / B) (y₁ / B) (y₂ / B) = (y₁ - y₂) / (x₁ - x₂) := by
  have hX : x₁ / B ≠ x₂ / B := fun h => hx (by rwa [div_left_inj' hB] at h)
  rw [WeierstrassCurve.Affine.slope_of_X_ne hX, ← sub_div, ← sub_div,
    div_div_div_cancel_right₀ hB]

/-- At a point with `y ≠ 0`, Mathlib's slope at the scaled point is the tangent slope
`(3·x² + 2·A·x + 1)/(2·B·y)`. -/
theorem slope_toW_self {A B x y : F} (two : (2 : F) ≠ 0) (hB : B ≠ 0) (hy : y ≠ 0) :
    (toW A B).toAffine.slope (x / B) (x / B) (y / B) (y / B)
      = (3 * x ^ 2 + 2 * A * x + 1) / (2 * B * y) := by
  have e : y / B - (toW A B).toAffine.negY (x / B) (y / B) = 2 * y / B := by
    simp only [WeierstrassCurve.Affine.negY, toW_a₁, toW_a₃]
    ring
  have hY : y / B ≠ (toW A B).toAffine.negY (x / B) (y / B) := fun h => by
    rw [← sub_eq_zero, e] at h
    exact div_ne_zero (mul_ne_zero two hy) hB h
  rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl hY, e]
  simp only [toW_a₁, toW_a₂, toW_a₄]
  field_simp
  ring

/-! ## Exceptional points

The facts the specification relies on to convert Montgomery points to ctEdwards points. -/

omit [DecidableEq F]

/-- If `A² − 4` is a non-square, the only point with `y = 0` is `(0, 0)`. Zcash Protocol
Specification [§A.2 "Elliptic curve
background"](https://zips.z.cash/protocol/protocol.pdf#ecbackground), the theorem that `(0, 0)` is
the only point with `y = 0` on certain Montgomery curves. -/
theorem x_eq_zero_of_y_eq_zero {A B x : F} (hA : ¬ IsSquare (A ^ 2 - 4))
    (h : OnCurve A B (x, 0)) : x = 0 := by
  unfold OnCurve at h
  by_contra hx
  have hq : x ^ 2 + A * x + 1 = 0 :=
    (mul_eq_zero.1 (show x * (x ^ 2 + A * x + 1) = 0 by linear_combination -h)).resolve_left hx
  exact hA ⟨2 * x + A, by linear_combination (-4) * hq⟩

/-- If `(A − 2)/B` is a non-square, no point has `x = −1`, since there `y² = (A − 2)/B`. Zcash
Protocol Specification [§A.3.3.3 "ctEdwards ↔ Montgomery
conversion"](https://zips.z.cash/protocol/protocol.pdf#cctconversion), exceptional points
(Montgomery → ctEdwards), where `(A − 2)/B` is the parameter `d` of a birationally equivalent
ctEdwards curve. -/
theorem x_add_one_ne_zero {A B x y : F} (hB : B ≠ 0) (hd : ¬ IsSquare ((A - 2) / B))
    (h : OnCurve A B (x, y)) : x + 1 ≠ 0 := by
  intro hx
  obtain rfl : x = -1 := by linear_combination hx
  unfold OnCurve at h
  exact hd ⟨y, by rw [div_eq_iff hB]; linear_combination -h⟩

/-! ## Changes of variables

Mathlib's `VariableChange` `C = ⟨u, r, s, t⟩` acts on Weierstrass curves so that a point
`(x', y')` of `C • W` is the point `(u²·x' + r, u³·y' + s·u²·x' + t)` of `W`. For `s = t = 0`
this is `(x', y') ↦ (u²·x' + r, u³·y')`, which carries Mathlib's chord-and-tangent formulas on
`C • W` to those on `W` (the slope scales by `u`), so it is an additive equivalence of affine
points (`variableChangeEquiv`). The equivalence takes the curve `W'` and a proof of `W' = C • W`,
so that a curve given otherwise (such as `toW A B`) needs no cast. -/

section VariableChange

open WeierstrassCurve WeierstrassCurve.Affine

variable {W : WeierstrassCurve F} {C : VariableChange F}

/-- The coefficients of `C • W` for `s = t = 0`, with `u⁻¹` written as an inverse in `F`. -/
theorem variableChange_coeffs (hs : C.s = 0) (ht : C.t = 0) :
    (C • W).a₁ = (C.u : F)⁻¹ * W.a₁ ∧ (C • W).a₂ = (C.u : F)⁻¹ ^ 2 * (W.a₂ + 3 * C.r) ∧
      (C • W).a₃ = (C.u : F)⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁) ∧
      (C • W).a₄ = (C.u : F)⁻¹ ^ 4 * (W.a₄ + 2 * C.r * W.a₂ + 3 * C.r ^ 2) ∧
      (C • W).a₆ = (C.u : F)⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3) := by
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, hs, ht, Units.val_inv_eq_inv_val]
  exact ⟨by ring, by ring, by ring, by ring, by ring⟩

/-- For `s = t = 0`, `(x, y)` is on `C • W` exactly when `(u²·x + r, u³·y)` is on `W`. -/
theorem equation_variableChange_iff (hs : C.s = 0) (ht : C.t = 0) (x y : F) :
    (C • W).toAffine.Equation x y ↔
      W.toAffine.Equation ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₆⟩ := variableChange_coeffs (W := W) hs ht
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rw [equation_iff, equation_iff]
  simp only [h₁, h₂, h₃, h₄, h₆]
  -- `W`'s equation at the image is `u⁶` times `C • W`'s equation at the point.
  have key : ((C.u : F) ^ 3 * y) ^ 2 + W.a₁ * ((C.u : F) ^ 2 * x + C.r) * ((C.u : F) ^ 3 * y) +
      W.a₃ * ((C.u : F) ^ 3 * y) - (((C.u : F) ^ 2 * x + C.r) ^ 3 +
      W.a₂ * ((C.u : F) ^ 2 * x + C.r) ^ 2 + W.a₄ * ((C.u : F) ^ 2 * x + C.r) + W.a₆) =
      (C.u : F) ^ 6 * (y ^ 2 + (C.u : F)⁻¹ * W.a₁ * x * y +
        (C.u : F)⁻¹ ^ 3 * (W.a₃ + C.r * W.a₁) * y - (x ^ 3 +
        (C.u : F)⁻¹ ^ 2 * (W.a₂ + 3 * C.r) * x ^ 2 +
        (C.u : F)⁻¹ ^ 4 * (W.a₄ + 2 * C.r * W.a₂ + 3 * C.r ^ 2) * x +
        (C.u : F)⁻¹ ^ 6 * (W.a₆ + C.r * W.a₄ + C.r ^ 2 * W.a₂ + C.r ^ 3))) := by
    field_simp
    ring
  constructor
  · intro e
    linear_combination key + (C.u : F) ^ 6 * e
  · intro e
    apply mul_left_cancel₀ (pow_ne_zero 6 hu)
    linear_combination e - key

/-- For `s = t = 0`, `negY` commutes with the change of variables. -/
theorem negY_variableChange (hs : C.s = 0) (ht : C.t = 0) (x y : F) :
    W.toAffine.negY ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y) =
      (C.u : F) ^ 3 * (C • W).toAffine.negY x y := by
  obtain ⟨h₁, -, h₃, -, -⟩ := variableChange_coeffs (W := W) hs ht
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [Affine.negY, h₁, h₃]
  field_simp
  ring

/-- For `s = t = 0`, `addX` commutes with the change of variables when the slope is scaled by
`u`. -/
theorem addX_variableChange (hs : C.s = 0) (ht : C.t = 0) (x₁ x₂ ℓ : F) :
    W.toAffine.addX ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) * ℓ) =
      (C.u : F) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  obtain ⟨h₁, h₂, -, -, -⟩ := variableChange_coeffs (W := W) hs ht
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [Affine.addX, h₁, h₂]
  field_simp
  ring

/-- For `s = t = 0`, `addY` commutes with the change of variables when the slope is scaled by
`u`. -/
theorem addY_variableChange (hs : C.s = 0) (ht : C.t = 0) (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.addY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) ^ 3 * y₁)
      ((C.u : F) * ℓ) = (C.u : F) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ := by
  rw [Affine.addY, Affine.negAddY, addX_variableChange hs ht,
    show (C.u : F) * ℓ * ((C.u : F) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r -
        ((C.u : F) ^ 2 * x₁ + C.r)) + (C.u : F) ^ 3 * y₁ =
      (C.u : F) ^ 3 * (C • W).toAffine.negAddY x₁ x₂ y₁ ℓ by rw [Affine.negAddY]; ring,
    negY_variableChange hs ht, Affine.addY]

variable [DecidableEq F]

/-- For `s = t = 0`, the slope of `W` at the images is `u` times the slope of `C • W`: in each of
Mathlib's three cases (chord, tangent, vertical), both sides are in the same case. -/
theorem slope_variableChange (hs : C.s = 0) (ht : C.t = 0) (x₁ x₂ y₁ y₂ : F) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) ^ 3 * y₁)
      ((C.u : F) ^ 3 * y₂) = (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ := by
  obtain ⟨h₁, h₂, h₃, h₄, -⟩ := variableChange_coeffs (W := W) hs ht
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  by_cases hx : x₁ = x₂
  · subst hx
    by_cases hy : y₁ = (C • W).toAffine.negY x₁ y₂
    · rw [slope_of_Y_eq rfl hy, slope_of_Y_eq rfl (by rw [negY_variableChange hs ht, hy]),
        mul_zero]
    · have hy' : (C.u : F) ^ 3 * y₁ ≠
          W.toAffine.negY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 3 * y₂) := by
        rw [negY_variableChange hs ht]
        exact fun e => hy (mul_left_cancel₀ (pow_ne_zero 3 hu) e)
      rw [slope_of_Y_ne rfl hy, slope_of_Y_ne rfl hy', negY_variableChange hs ht, ← mul_sub]
      -- The tangent numerator scales by `u⁴`, the denominator by `u³`.
      have num : 3 * ((C.u : F) ^ 2 * x₁ + C.r) ^ 2 + 2 * W.a₂ * ((C.u : F) ^ 2 * x₁ + C.r) +
          W.a₄ - W.a₁ * ((C.u : F) ^ 3 * y₁) = (C.u : F) ^ 4 * (3 * x₁ ^ 2 +
          2 * (C • W).a₂ * x₁ + (C • W).a₄ - (C • W).a₁ * y₁) := by
        rw [h₁, h₂, h₄]
        field_simp
        ring
      rw [num, show (C.u : F) ^ 4 * (3 * x₁ ^ 2 + 2 * (C • W).a₂ * x₁ + (C • W).a₄ -
          (C • W).a₁ * y₁) = (C.u : F) ^ 3 * ((C.u : F) * (3 * x₁ ^ 2 + 2 * (C • W).a₂ * x₁ +
          (C • W).a₄ - (C • W).a₁ * y₁)) by ring, mul_div_mul_left _ _ (pow_ne_zero 3 hu),
        mul_div_assoc]
  · have hx' : (C.u : F) ^ 2 * x₁ + C.r ≠ (C.u : F) ^ 2 * x₂ + C.r := fun e =>
      hx (mul_left_cancel₀ (pow_ne_zero 2 hu) (add_right_cancel e))
    rw [slope_of_X_ne hx, slope_of_X_ne hx',
      show (C.u : F) ^ 2 * x₁ + C.r - ((C.u : F) ^ 2 * x₂ + C.r) = (C.u : F) ^ 2 * (x₁ - x₂) by
        ring, ← mul_sub, show (C.u : F) ^ 3 * (y₁ - y₂) = (C.u : F) ^ 2 * ((C.u : F) * (y₁ - y₂)) by
        ring, mul_div_mul_left _ _ (pow_ne_zero 2 hu), mul_div_assoc]

variable [W.IsElliptic] {W' : WeierstrassCurve F}

/-- The map `(x', y') ↦ (u²·x' + r, u³·y')` from the affine points of `W' = C • W` to those of
`W`, for `s = t = 0`. -/
def variableChangeMap (hs : C.s = 0) (ht : C.t = 0) (h : W' = C • W) :
    W'.toAffine.Point → W.toAffine.Point
  | .zero => 0
  | .some x y hn => .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y)
      (equation_iff_nonsingular.mp ((equation_variableChange_iff hs ht x y).mp (h ▸ hn.1)))

/-- The inverse map `(x, y) ↦ ((x − r)/u², y/u³)`. -/
def variableChangeUnmap (hs : C.s = 0) (ht : C.t = 0) (h : W' = C • W) :
    W.toAffine.Point → W'.toAffine.Point
  | .zero => 0
  | .some x y hn => .some ((x - C.r) / (C.u : F) ^ 2) (y / (C.u : F) ^ 3) (by
      subst h
      refine equation_iff_nonsingular.mp ((equation_variableChange_iff hs ht _ _).mpr ?_)
      rw [mul_div_cancel₀ _ (pow_ne_zero 2 C.u.ne_zero), sub_add_cancel,
        mul_div_cancel₀ _ (pow_ne_zero 3 C.u.ne_zero)]
      exact hn.1)

omit [DecidableEq F] in
/-- The map on an affine point. -/
theorem variableChangeMap_some (hs : C.s = 0) (ht : C.t = 0) (h : W' = C • W) {x y : F}
    (hn : W'.toAffine.Nonsingular x y) :
    variableChangeMap hs ht h (.some x y hn) =
      .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y)
      (equation_iff_nonsingular.mp ((equation_variableChange_iff hs ht x y).mp (h ▸ hn.1))) :=
  rfl

/-- The map is additive. -/
theorem variableChangeMap_add (hs : C.s = 0) (ht : C.t = 0) (h : W' = C • W)
    (P Q : W'.toAffine.Point) :
    variableChangeMap hs ht h (P + Q) =
      variableChangeMap hs ht h P + variableChangeMap hs ht h Q := by
  subst h
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2]
    exact (Point.add_of_Y_eq (by rw [hxy.1]) (by rw [negY_variableChange hs ht, hxy.2])).symm
  · have hxy' : ¬((C.u : F) ^ 2 * x₁ + C.r = (C.u : F) ^ 2 * x₂ + C.r ∧ (C.u : F) ^ 3 * y₁ =
        W.toAffine.negY ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) ^ 3 * y₂)) := by
      rintro ⟨ex, ey⟩
      rw [negY_variableChange hs ht] at ey
      exact hxy ⟨mul_left_cancel₀ (pow_ne_zero 2 hu) (add_right_cancel ex),
        mul_left_cancel₀ (pow_ne_zero 3 hu) ey⟩
    rw [Point.add_some hxy, variableChangeMap_some, variableChangeMap_some,
      variableChangeMap_some, Point.add_some hxy', Point.some.injEq, slope_variableChange hs ht,
      addX_variableChange hs ht, addY_variableChange hs ht]
    exact ⟨rfl, rfl⟩

/-- **The additive equivalence** between the affine points of `W' = C • W` and those of `W`, for
a change of variables with `s = t = 0`. -/
def variableChangeEquiv (hs : C.s = 0) (ht : C.t = 0) (h : W' = C • W) :
    W'.toAffine.Point ≃+ W.toAffine.Point where
  toFun := variableChangeMap hs ht h
  invFun := variableChangeUnmap hs ht h
  left_inv := by
    subst h
    rintro (_ | ⟨x, y, hn⟩)
    · rfl
    · have hu : (C.u : F) ≠ 0 := C.u.ne_zero
      refine (Point.some.injEq _ _ _ _ _ _).mpr ⟨?_, ?_⟩
      · rw [add_sub_cancel_right, mul_div_cancel_left₀ _ (pow_ne_zero 2 hu)]
      · rw [mul_div_cancel_left₀ _ (pow_ne_zero 3 hu)]
  right_inv := by
    subst h
    rintro (_ | ⟨x, y, hn⟩)
    · rfl
    · have hu : (C.u : F) ≠ 0 := C.u.ne_zero
      refine (Point.some.injEq _ _ _ _ _ _).mpr ⟨?_, ?_⟩
      · rw [mul_div_cancel₀ _ (pow_ne_zero 2 hu), sub_add_cancel]
      · rw [mul_div_cancel₀ _ (pow_ne_zero 3 hu)]
  map_add' := variableChangeMap_add hs ht h

end VariableChange

end CompElliptic.CurveForms.Montgomery
