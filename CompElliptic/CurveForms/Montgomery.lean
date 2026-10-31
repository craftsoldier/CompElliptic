/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Julian Abraham
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula
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
closes with the facts about exceptional points that the specification relies on
(`§ Exceptional points`).
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

end CompElliptic.CurveForms.Montgomery
