/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import CompElliptic.CoordinateSystem

/-!
# Short-Weierstrass elliptic curves

One module for the short-Weierstrass curve form `y² = x³ + A x + B`, layered:

1. **Raw computable kernel** — `OnCurve`, `neg`, complete `add` (identity `𝒪 ≡ (0, 0)`), `smul`,
   as plain functions on `F × F`. `add` models complete addition: it is total and evaluable
   using `native_decide`, with a decidable case split for `𝒪` / doubling / `P + (-P)`.
2. **Transport foundation** — `toW`, identifying the form with Mathlib's `WeierstrassCurve` so
   that the hard group axioms can be borrowed from Mathlib's proven `AddCommGroup`.
3. **Rich bundled types** — `SWCurve` (bundles ellipticity and `B ≠ 0`) and `SWPoint E`
   (correct-by-construction: on the curve or `𝒪`). This is the correct-by-construction interface
   used to express the group structure and circuit gadgets.
4. **Fast scalar multiplication** — the group action `n • _` on `SWPoint E` is the generic binary
   double-and-add `CompElliptic.binNsmul` (`ScalarMul.lean`), so `n • P` computes in `O(log n)` and
   is `native_decide`-friendly for cryptographic-size scalars, while remaining the genuine scalar
   action (every Mathlib `n • _` lemma still applies, since they follow from `nsmul_zero` /
   `nsmul_succ`).

The field assumption is a generic `[Field F]`: `SWCurve.IsElliptic` excludes characteristic 2
(`sw_Δ = 0` there), so binary fields are gracefully excluded, but without precluding any future
separate binary-field curve form. See `TODO.md`.
-/

namespace CompElliptic.CurveForms.ShortWeierstrass

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Raw computable kernel -/

/-- `p` lies on `y² = x³ + a x + b` as an affine point. -/
def OnCurve (a b : F) (p : F × F) : Prop := p.2 ^ 2 = p.1 ^ 3 + a * p.1 + b

instance (a b : F) (p : F × F) : Decidable (OnCurve a b p) := by unfold OnCurve; infer_instance

/-- A representable point: on the curve, or the `(0, 0)` identity sentinel `𝒪`. -/
def Valid (a b : F) (p : F × F) : Prop := OnCurve a b p ∨ p = (0, 0)

/-- Representability is decidable too: being on the curve is, and so is the `(0, 0)` sentinel test.
This is what lets a representable point be exhibited by `decide`, and `SWPoint E` be counted as a
subtype of `F × F`. -/
instance (a b : F) (p : F × F) : Decidable (Valid a b p) := by unfold Valid; infer_instance

omit [DecidableEq F] in
/-- The `(0, 0)` sentinel is off the curve exactly when `b ≠ 0` (which holds for any elliptic
curve: `a = b = 0` is the singular cusp `y² = x³`). This is what makes `(0, 0) ≡ 𝒪` unambiguous. -/
theorem not_onCurve_zero {a b : F} (hb : b ≠ 0) : ¬ OnCurve a b (0, 0) := by
  intro h
  apply hb
  have h' : (0 : F) ^ 2 = (0 : F) ^ 3 + a * 0 + b := h
  simpa using h'.symm

omit [DecidableEq F] in
/-- Two points on the curve sharing an `x`-coordinate have `y`-coordinates equal up to sign,
because their curve equations subtract to `(y₁ - y₂)·(y₁ + y₂) = 0`. -/
theorem y_eq_pm_of_onCurve_x_eq {a b x y₁ y₂ : F}
    (h₁ : OnCurve a b (x, y₁)) (h₂ : OnCurve a b (x, y₂)) : y₁ = y₂ ∨ y₁ = -y₂ := by
  have h : (y₁ - y₂) * (y₁ + y₂) = 0 := by
    simp only [OnCurve] at h₁ h₂
    linear_combination h₁ - h₂
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (by linear_combination h)

/-- Negation `(x, y) ↦ (x, -y)`; fixes the `(0, 0)` sentinel. -/
def neg (p : F × F) : F × F := (p.1, -p.2)

/-- Complete affine addition with `(0, 0) ≡ 𝒪`.
Only the curve coefficient `a` appears (in the doubling slope `(3x² + a)/(2y)`);
`b` is not needed. -/
def add (a : F) (p q : F × F) : F × F :=
  if p = (0, 0) then q
  else if q = (0, 0) then p
  else if p.1 = q.1 then
    if p.2 + q.2 = 0 then (0, 0)                 -- q = -p ⇒ 𝒪
    else                                         -- doubling (same x, so same nonzero y)
      let lam := (3 * p.1 ^ 2 + a) / (2 * p.2)
      let x₃ := lam ^ 2 - p.1 - q.1
      (x₃, lam * (p.1 - x₃) - p.2)
  else                                           -- distinct x-coordinates
    let lam := (q.2 - p.2) / (q.1 - p.1)
    let x₃ := lam ^ 2 - p.1 - q.1
    (x₃, lam * (p.1 - x₃) - p.2)

/-- `n • p`, by iterated addition (spec-level, not the windowed circuit form). On `SWPoint E` the
`AddCommGroup` instance below provides the genuine `n • _` / `k • _` scalar actions. -/
def smul (a : F) : ℕ → F × F → F × F
  | 0, _ => (0, 0)
  | n + 1, p => add a (smul a n p) p

/-! ## Identity, involution, and inverse laws (raw, no hypotheses) -/

/-- `𝒪 + p = p`. -/
theorem zero_add (a : F) (p : F × F) : add a (0, 0) p = p := by
  simp [add]

/-- `p + 𝒪 = p`. -/
theorem add_zero (a : F) (p : F × F) : add a p (0, 0) = p := by
  rcases eq_or_ne p (0, 0) with h | h <;> simp [add, h]

omit [DecidableEq F] in
/-- `-(-p) = p`. -/
theorem neg_neg (p : F × F) : neg (neg p) = p := by
  simp [neg]

/-- `p + (-p) = 𝒪`: for `p = 𝒪` immediate; otherwise the addends share an `x`-coordinate with
`p.2 + (neg p).2 = 0`, so the `q = -p` branch fires. Proved by an explicit `if`-branch walk
rather than `split_ifs <;> simp_all`, which blows the recursion limit on the nested `ite`. -/
theorem add_neg (a : F) (p : F × F) : add a p (neg p) = (0, 0) := by
  rcases eq_or_ne p (0, 0) with h | h
  · simp [add, neg, h]
  · have hn : neg p ≠ (0, 0) := fun hc => h (by simpa [neg, Prod.ext_iff] using hc)
    have hx : p.1 = (neg p).1 := rfl
    have hy : p.2 + (neg p).2 = 0 := by simp [neg]
    unfold add
    rw [if_neg h, if_neg hn, if_pos hx, if_pos hy]

/-! ## Transport foundation: identify the short form with a Mathlib `WeierstrassCurve`

For the short form (`a₁ = a₂ = a₃ = 0`, `a₄ = a`, `a₆ = b`) Mathlib's computable coordinate
formulas (`negY`, `slope`, `addX`, `addY`) reduce to exactly our `add`/`neg`, so closure and
associativity can be borrowed from Mathlib's proven `AddCommGroup` on `WeierstrassCurve.Affine.Point`
(`Affine/Point.lean`). The carried `Nonsingular` proof is a `Prop`, so the bridge is
computation-erasable. The curve must be nonsingular (`[(toW a b).IsElliptic]`). -/

/-- The short-Weierstrass curve `y² = x³ + a x + b` as a Mathlib `WeierstrassCurve`. -/
def toW (a b : F) : WeierstrassCurve F := { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := a, a₆ := b }

omit [DecidableEq F]
@[simp] lemma toW_a₁ (a b : F) : (toW a b).a₁ = 0 := rfl
@[simp] lemma toW_a₂ (a b : F) : (toW a b).a₂ = 0 := rfl
@[simp] lemma toW_a₃ (a b : F) : (toW a b).a₃ = 0 := rfl
@[simp] lemma toW_a₄ (a b : F) : (toW a b).a₄ = a := rfl
@[simp] lemma toW_a₆ (a b : F) : (toW a b).a₆ = b := rfl

/-- Our on-curve predicate is Mathlib's affine curve equation for `toW a b`. -/
lemma equation_toW {a b x y : F} :
    WeierstrassCurve.Affine.Equation (toW a b) x y ↔ OnCurve a b (x, y) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [toW_a₁, toW_a₂, toW_a₃, toW_a₄, toW_a₆, OnCurve]
  constructor <;> intro h <;> linear_combination h

/-- On a nonsingular curve, every on-curve point gives a nonsingular Mathlib point. -/
lemma nonsingular_toW {a b : F} [(toW a b).IsElliptic] {x y : F}
    (h : OnCurve a b (x, y)) : WeierstrassCurve.Affine.Nonsingular (toW a b) x y :=
  WeierstrassCurve.Affine.equation_iff_nonsingular.mp (equation_toW.mpr h)

end CompElliptic.CurveForms.ShortWeierstrass

namespace CompElliptic.CurveForms.ShortWeierstrass
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Closure, commutativity, associativity (raw workhorses)

Stated with the hypotheses the transport needs: `[(toW a b).IsElliptic]` throughout, and `b ≠ 0`
for the laws whose `𝒪`-sentinel cases require `(0, 0)` to be off the curve. The `SWPoint`
`AddCommGroup` instance below discharges these from `SWCurve`'s bundled fields. -/

open WeierstrassCurve.Affine

/-- For two on-curve points that are neither `𝒪` nor mutual inverses, our affine `add` agrees with
Mathlib's chord/tangent coordinates `(addX, addY)` for `toW a b`. This is the shared engine behind
closure (and, via the `Point` group, associativity). -/
lemma add_eq_addXY {a b : F} {x₁ y₁ x₂ y₂ : F}
    (hp0 : (x₁, y₁) ≠ (0, 0)) (hq0 : (x₂, y₂) ≠ (0, 0))
    (hxy : ¬(x₁ = x₂ ∧ y₁ + y₂ = 0)) :
    add a (x₁, y₁) (x₂, y₂)
      = (addX (toW a b) x₁ x₂ (slope (toW a b) x₁ x₂ y₁ y₂),
         addY (toW a b) x₁ x₂ y₁ (slope (toW a b) x₁ x₂ y₁ y₂)) := by
  have hnegY1 : negY (toW a b) x₁ y₁ = -y₁ := by simp [negY]
  have hnegY2 : negY (toW a b) x₂ y₂ = -y₂ := by simp [negY]
  unfold add
  dsimp only
  rw [if_neg hp0, if_neg hq0]
  by_cases hx : x₁ = x₂
  · have hy : ¬(y₁ + y₂ = 0) := fun h => hxy ⟨hx, h⟩
    have hyne : y₁ ≠ negY (toW a b) x₂ y₂ := by
      rw [hnegY2]; intro h; exact hy (by rw [h]; ring)
    rw [if_pos hx, if_neg hy]
    rw [slope_of_Y_ne hx hyne, hnegY1]
    simp only [addX, addY, negAddY, negY, toW_a₁, toW_a₂, toW_a₃, toW_a₄, mul_zero, zero_mul, sub_zero]
    rw [Prod.mk.injEq]
    refine ⟨by ring, by ring⟩
  · have hd1 : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
    have hd2 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    rw [if_neg hx]
    rw [slope_of_X_ne hx]
    simp only [addX, addY, negAddY, negY, toW_a₁, toW_a₂, toW_a₃, zero_mul, sub_zero]
    rw [Prod.mk.injEq]
    refine ⟨?_, ?_⟩ <;> field_simp <;> ring

/-- Closure: `add` preserves `Valid`. (Result coords = Mathlib `addX`/`addY`; `nonsingular_add`
gives on-curveness.) -/
theorem valid_add {a b : F} [(toW a b).IsElliptic] {p q : F × F}
    (hp : Valid a b p) (hq : Valid a b q) : Valid a b (add a p q) := by
  by_cases hp0 : p = (0, 0)
  · rw [hp0, zero_add]; exact hq
  by_cases hq0 : q = (0, 0)
  · rw [hq0, add_zero]; exact hp
  obtain ⟨x₁, y₁⟩ := p
  obtain ⟨x₂, y₂⟩ := q
  have hOp : OnCurve a b (x₁, y₁) := hp.resolve_right hp0
  have hOq : OnCurve a b (x₂, y₂) := hq.resolve_right hq0
  by_cases hinv : x₁ = x₂ ∧ y₁ + y₂ = 0
  · right
    obtain ⟨hx, hy⟩ := hinv
    have hqp : (x₂, y₂) = neg (x₁, y₁) := by
      simp only [neg, Prod.mk.injEq]
      exact ⟨hx.symm, by linear_combination hy⟩
    rw [hqp, add_neg]
  · left
    rw [add_eq_addXY hp0 hq0 hinv]
    have hn : negY (toW a b) x₂ y₂ = -y₂ := by simp [negY]
    have hxy' : ¬(x₁ = x₂ ∧ y₁ = negY (toW a b) x₂ y₂) := by
      rintro ⟨hx, hyeq⟩
      refine hinv ⟨hx, ?_⟩
      rw [hn] at hyeq; rw [hyeq]; ring
    have hns := nonsingular_add (nonsingular_toW hOp) (nonsingular_toW hOq) hxy'
    exact equation_toW.mp hns.left

/-- Commutativity. (Generic branch is pure field algebra; doubling branch forces `p = q` from
on-curve; `𝒪` branches from the identity laws.) -/
theorem add_comm {a b : F} {p q : F × F} (hp : Valid a b p) (hq : Valid a b q) :
    add a p q = add a q p := by
  by_cases hp0 : p = (0, 0)
  · rw [hp0, zero_add, add_zero]
  by_cases hq0 : q = (0, 0)
  · rw [hq0, zero_add, add_zero]
  obtain ⟨x₁, y₁⟩ := p
  obtain ⟨x₂, y₂⟩ := q
  have hOp : OnCurve a b (x₁, y₁) := hp.resolve_right hp0
  have hOq : OnCurve a b (x₂, y₂) := hq.resolve_right hq0
  by_cases hinv : x₁ = x₂ ∧ y₁ + y₂ = 0
  · obtain ⟨hx, hy⟩ := hinv
    have e1 : add a (x₁, y₁) (x₂, y₂) = (0, 0) := by
      have h : (x₂, y₂) = neg (x₁, y₁) := by
        simp only [neg, Prod.mk.injEq]; exact ⟨hx.symm, by linear_combination hy⟩
      rw [h, add_neg]
    have e2 : add a (x₂, y₂) (x₁, y₁) = (0, 0) := by
      have h : (x₁, y₁) = neg (x₂, y₂) := by
        simp only [neg, Prod.mk.injEq]; exact ⟨hx, by linear_combination hy⟩
      rw [h, add_neg]
    rw [e1, e2]
  · have hinv' : ¬(x₂ = x₁ ∧ y₂ + y₁ = 0) :=
      fun ⟨hx, hy⟩ => hinv ⟨hx.symm, by linear_combination hy⟩
    rw [add_eq_addXY (b := b) hp0 hq0 hinv, add_eq_addXY (b := b) hq0 hp0 hinv']
    by_cases hx : x₁ = x₂
    · have hsum : y₁ + y₂ ≠ 0 := fun h => hinv ⟨hx, h⟩
      have hy12 : y₁ = y₂ := by
        simp only [OnCurve] at hOp hOq
        have hsq : (y₁ - y₂) * (y₁ + y₂) = 0 := by rw [hx] at hOp; linear_combination hOp - hOq
        exact sub_eq_zero.mp ((mul_eq_zero.mp hsq).resolve_right hsum)
      subst hx; subst hy12; rfl
    · have hd1 : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
      have hd2 : x₂ - x₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
      rw [slope_of_X_ne hx, slope_of_X_ne (Ne.symm hx)]
      simp only [addX, addY, negAddY, negY, toW_a₁, toW_a₂, toW_a₃, zero_mul, sub_zero]
      rw [Prod.mk.injEq]
      refine ⟨?_, ?_⟩ <;> field_simp <;> ring

/-! ### Transport to Mathlib's `Point` group for associativity

`toPt` sends a representable point to Mathlib's `Point` (`𝒪 ↦ 0`, on-curve `(x, y) ↦ some x y`),
with `ofPt` the coordinate left-inverse. `toPt_add` is the homomorphism property; associativity is
then inherited from Mathlib's `AddCommGroup (toW a b).Point`. All of this needs `b ≠ 0` so that
the `(0, 0)` sentinel maps to `0` (i.e. `(0, 0)` is genuinely off the curve). -/

/-- The Mathlib point of a representable point: `𝒪 ↦ 0`, on-curve `(x, y) ↦ some x y`. -/
noncomputable def toPt (a b : F) [(toW a b).IsElliptic] (p : F × F) : Point (toW a b) :=
  if h : OnCurve a b p then .some p.1 p.2 (nonsingular_toW h) else 0

/-- Coordinate left-inverse of `toPt` (`0 ↦ 𝒪`, `some x y _ ↦ (x, y)`). -/
def ofPt {a b : F} (P : Point (toW a b)) : F × F :=
  match P with
  | .zero => (0, 0)
  | .some x y _ => (x, y)

lemma toPt_some {a b : F} [(toW a b).IsElliptic] {x y : F} (h : OnCurve a b (x, y)) :
    toPt a b (x, y) = .some x y (nonsingular_toW h) := dif_pos h

lemma toPt_zero {a b : F} (hb : b ≠ 0) [(toW a b).IsElliptic] : toPt a b (0, 0) = 0 :=
  dif_neg (not_onCurve_zero hb)

lemma ofPt_toPt {a b : F} (hb : b ≠ 0) [(toW a b).IsElliptic] {p : F × F} (hp : Valid a b p) :
    ofPt (toPt a b p) = p := by
  rcases hp with hOp | hp0
  · obtain ⟨x, y⟩ := p; rw [toPt_some hOp]; rfl
  · rw [hp0, toPt_zero hb]; rfl

/-- The homomorphism property: `toPt` carries our `add` to Mathlib's `Point` addition. -/
lemma toPt_add {a b : F} (hb : b ≠ 0) [(toW a b).IsElliptic] {p q : F × F}
    (hp : Valid a b p) (hq : Valid a b q) :
    toPt a b (add a p q) = toPt a b p + toPt a b q := by
  by_cases hp0 : p = (0, 0)
  · rw [hp0, zero_add, toPt_zero hb, _root_.zero_add]
  by_cases hq0 : q = (0, 0)
  · rw [hq0, add_zero, toPt_zero hb, _root_.add_zero]
  obtain ⟨x₁, y₁⟩ := p
  obtain ⟨x₂, y₂⟩ := q
  have hOp : OnCurve a b (x₁, y₁) := hp.resolve_right hp0
  have hOq : OnCurve a b (x₂, y₂) := hq.resolve_right hq0
  have hn : negY (toW a b) x₂ y₂ = -y₂ := by simp [negY]
  rw [toPt_some hOp, toPt_some hOq]
  by_cases hinv : x₁ = x₂ ∧ y₁ + y₂ = 0
  · obtain ⟨hx, hy⟩ := hinv
    have e : add a (x₁, y₁) (x₂, y₂) = (0, 0) := by
      have h : (x₂, y₂) = neg (x₁, y₁) := by
        simp only [neg, Prod.mk.injEq]; exact ⟨hx.symm, by linear_combination hy⟩
      rw [h, add_neg]
    rw [e, toPt_zero hb, Point.add_of_Y_eq hx (by rw [hn]; linear_combination hy)]
  · have hxy' : ¬(x₁ = x₂ ∧ y₁ = negY (toW a b) x₂ y₂) := by
      rintro ⟨hx, hyeq⟩; exact hinv ⟨hx, by rw [hn] at hyeq; rw [hyeq]; ring⟩
    have e : add a (x₁, y₁) (x₂, y₂)
        = (addX (toW a b) x₁ x₂ (slope (toW a b) x₁ x₂ y₁ y₂),
           addY (toW a b) x₁ x₂ y₁ (slope (toW a b) x₁ x₂ y₁ y₂)) :=
      add_eq_addXY hp0 hq0 hinv
    have hO : OnCurve a b
        (addX (toW a b) x₁ x₂ (slope (toW a b) x₁ x₂ y₁ y₂),
         addY (toW a b) x₁ x₂ y₁ (slope (toW a b) x₁ x₂ y₁ y₂)) :=
      equation_toW.mp (nonsingular_add (nonsingular_toW hOp) (nonsingular_toW hOq) hxy').left
    rw [e, Point.add_some hxy', toPt_some hO]

/-- Associativity (the hard axiom), by transport to Mathlib's `Point` `AddCommGroup`. -/
theorem add_assoc {a b : F} (hb : b ≠ 0) [(toW a b).IsElliptic] {p q r : F × F}
    (hp : Valid a b p) (hq : Valid a b q) (hr : Valid a b r) :
    add a (add a p q) r = add a p (add a q r) := by
  have key : toPt a b (add a (add a p q) r) = toPt a b (add a p (add a q r)) := by
    rw [toPt_add hb (valid_add hp hq) hr, toPt_add hb hp hq,
      toPt_add hb hp (valid_add hq hr), toPt_add hb hq hr, _root_.add_assoc]
  calc add a (add a p q) r
      = ofPt (toPt a b (add a (add a p q) r)) :=
        (ofPt_toPt hb (valid_add (valid_add hp hq) hr)).symm
    _ = ofPt (toPt a b (add a p (add a q r))) := by rw [key]
    _ = add a p (add a q r) := ofPt_toPt hb (valid_add hp (valid_add hq hr))

omit [DecidableEq F] in
/-- `neg` preserves `Valid` (on-curve since `(-y)² = y²`; the `𝒪` sentinel is fixed). -/
theorem valid_neg {a b : F} {p : F × F} (hp : Valid a b p) : Valid a b (neg p) := by
  rcases hp with h | h
  · left; simp only [OnCurve, neg] at h ⊢; linear_combination h
  · right; rw [h]; simp [neg]

/-- Closure of the spec-level `smul`: `n • p` stays `Valid`, by induction on `valid_add`. -/
theorem valid_smul {a b : F} [(toW a b).IsElliptic] {p : F × F} (hp : Valid a b p) :
    ∀ n : ℕ, Valid a b (smul a n p)
  | 0 => Or.inr rfl
  | n + 1 => valid_add (valid_smul hp n) hp

/-! ## Rich bundled types -/

/-- The discriminant of the short-Weierstrass curve `y² = x³ + A x + B`. -/
def sw_Δ (A B : F) : F := -16 * (4 * A ^ 3 + 27 * B ^ 2)

/-- A short-Weierstrass elliptic curve: coefficients `A`, `B`, bundled with nonsingularity
(`IsUnit sw_Δ`, which over a field is `sw_Δ ≠ 0` and self-excludes characteristic 2) and `B ≠ 0`
(so the `𝒪 = (0, 0)` sentinel is off the curve). -/
structure SWCurve (F : Type*) [Field F] where
  A : F
  B : F
  IsElliptic : IsUnit (sw_Δ A B)
  B_nonzero : B ≠ 0

/-- A point on `E`, correct by construction: on the curve, or the identity `𝒪 = (0, 0)`. -/
structure SWPoint (E : SWCurve F) where
  x : F
  y : F
  onCurve : Valid E.A E.B (x, y)
deriving Repr

omit [DecidableEq F] in
/-- `(0, 0)` is off the curve `E`, immediate from `E.B_nonzero`. -/
theorem origin_not_on_curve (E : SWCurve F) : ¬ OnCurve E.A E.B (0, 0) :=
  not_onCurve_zero E.B_nonzero

/-- The identity point `𝒪` on `E`. -/
def SWPoint.zero (E : SWCurve F) : SWPoint E := ⟨0, 0, Or.inr rfl⟩

omit [DecidableEq F] in
/-- For the short form, Mathlib's Weierstrass discriminant is our `sw_Δ`. -/
lemma toW_Δ (A B : F) : (toW A B).Δ = sw_Δ A B := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, toW_a₁, toW_a₂, toW_a₃, toW_a₄, toW_a₆, sw_Δ]
  ring

/-- `E`'s bundled `IsUnit (sw_Δ ..)` is exactly Mathlib's ellipticity of `toW E.A E.B`, so the raw
group-law lemmas (which require `[(toW A B).IsElliptic]`) apply to `E` by instance resolution. -/
instance instIsElliptic (E : SWCurve F) : (toW E.A E.B).IsElliptic where
  isUnit := by rw [toW_Δ]; exact E.IsElliptic

omit [DecidableEq F] in
/-- Two representable points are equal when their coordinate pairs agree (`onCurve` is a `Prop`). -/
theorem SWPoint.ext_pair {E : SWCurve F} {P Q : SWPoint E}
    (h : (P.x, P.y) = (Q.x, Q.y)) : P = Q := by
  obtain ⟨px, py, hP⟩ := P
  obtain ⟨qx, qy, hQ⟩ := Q
  injection h with hx hy
  subst hx; subst hy; rfl

/-- Points on `E` are exactly the valid coordinate pairs: the carried `onCurve` proof is a `Prop`,
so nothing is lost by passing to the subtype. This is the bridge to anything `F × F` already knows —
decidable equality, finiteness, and counting `SWPoint E` as a `Finset` of pairs. -/
def SWPoint.equivSubtype (E : SWCurve F) : SWPoint E ≃ { pr : F × F // Valid E.A E.B pr } where
  toFun P := ⟨(P.x, P.y), P.onCurve⟩
  invFun pr := ⟨pr.1.1, pr.1.2, pr.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Addition lifted to `SWPoint E`; closure from `valid_add`. -/
def sw_add {E : SWCurve F} (P Q : SWPoint E) : SWPoint E :=
  haveI := instIsElliptic E
  ⟨(add E.A (P.x, P.y) (Q.x, Q.y)).1, (add E.A (P.x, P.y) (Q.x, Q.y)).2,
   valid_add P.onCurve Q.onCurve⟩

/-- Negation lifted to `SWPoint E`; closure from `valid_neg`. -/
def sw_neg {E : SWCurve F} (P : SWPoint E) : SWPoint E :=
  ⟨(neg (P.x, P.y)).1, (neg (P.x, P.y)).2, valid_neg P.onCurve⟩

instance (E : SWCurve F) : Zero (SWPoint E) := ⟨SWPoint.zero E⟩
instance (E : SWCurve F) : Add (SWPoint E) := ⟨sw_add⟩
instance (E : SWCurve F) : Neg (SWPoint E) := ⟨sw_neg⟩

omit [DecidableEq F] in
/-- Negation fixes the `x`-coordinate. True by `rfl` (`sw_neg` is `neg` on the coordinates), but
worth naming: without it every caller re-derives it inline. -/
@[simp] theorem SWPoint.neg_x {E : SWCurve F} (P : SWPoint E) : (-P).x = P.x := rfl

omit [DecidableEq F] in
/-- Negation negates the `y`-coordinate — the one fact that makes `2 • P = 0` say `P.y = -P.y`. -/
@[simp] theorem SWPoint.neg_y {E : SWCurve F} (P : SWPoint E) : (-P).y = -P.y := rfl

/-- Addition computes its `x`-coordinate by the raw `add` on the coordinate pairs. -/
lemma SWPoint.add_x {E : SWCurve F} (P Q : SWPoint E) :
    (P + Q).x = (add E.A (P.x, P.y) (Q.x, Q.y)).1 := rfl

/-- Addition computes its `y`-coordinate by the raw `add` on the coordinate pairs. -/
lemma SWPoint.add_y {E : SWCurve F} (P Q : SWPoint E) :
    (P + Q).y = (add E.A (P.x, P.y) (Q.x, Q.y)).2 := rfl

omit [DecidableEq F] in
/-- A nonzero representable point is on the curve: its `Valid` disjunction cannot be the `(0, 0)`
sentinel. -/
theorem SWPoint.onCurve_of_ne_zero {E : SWCurve F} {P : SWPoint E} (h : P ≠ 0) :
    OnCurve E.A E.B (P.x, P.y) := by
  rcases P.onCurve with hc | h0
  · exact hc
  · exact absurd (SWPoint.ext_pair (by rw [h0]; rfl)) h

omit [DecidableEq F] in
/-- Nonzero representable points sharing an `x`-coordinate are equal up to sign: both are on the
curve (`onCurve_of_ne_zero`), so their `y`-coordinates agree up to sign
(`y_eq_pm_of_onCurve_x_eq`). -/
theorem SWPoint.eq_pm_of_x_eq {E : SWCurve F} {P Q : SWPoint E}
    (hP : P ≠ 0) (hQ : Q ≠ 0) (hx : P.x = Q.x) : P = Q ∨ P = -Q := by
  have hPC := onCurve_of_ne_zero hP
  have hQC := onCurve_of_ne_zero hQ
  rw [hx] at hPC
  rcases y_eq_pm_of_onCurve_x_eq hPC hQC with hy | hy
  · exact Or.inl (ext_pair (by rw [hx, hy]))
  · exact Or.inr (ext_pair (by rw [hx, hy]; rfl))

/-! ### Fast (logarithmic) scalar multiplication

The spec-level `smul` is linear (`n` additions), so it cannot be evaluated by `decide` or
`native_decide` for cryptographic-size scalars (`≈ 2^254`). The group action `n • _` on `SWPoint E`
(the `nsmul` field of the `AddCommGroup` instance below) is instead the generic binary
double-and-add `CompElliptic.binNsmul` over the raw `sw_add` / `SWPoint.zero`. So `n • P` computes in
`O(log n)` and is `native_decide`-friendly, while remaining the genuine scalar action: every Mathlib
`n • _` lemma still applies, since they follow from `nsmul_zero` and `nsmul_succ`. -/

/-- `SWPoint E` has decidable equality (the `onCurve` field is a `Prop`, so equality reduces to the
coordinate pair, via `SWPoint.equivSubtype`); needed for `native_decide` on `n • P = Q`. -/
instance instDecidableEqSWPoint {E : SWCurve F} : DecidableEq (SWPoint E) :=
  (SWPoint.equivSubtype E).decidableEq

/-- `SWPoint E` is computably finite whenever the base field is: it is a subtype of `F × F`
(`SWPoint.equivSubtype`) with a decidable membership predicate, so the point enumeration is a
plain filter of `F × F` — no choice. Downstream reductions that need a `Fintype` for the curve
group can therefore stay computable rather than materializing one with `Fintype.ofFinite`. -/
instance instFintypeSWPoint [Fintype F] {E : SWCurve F} : Fintype (SWPoint E) :=
  Fintype.ofEquiv _ (SWPoint.equivSubtype E).symm

/-- The abelian group of representable points on `E`: identity laws and inverses are immediate;
commutativity and associativity transport from the raw `add` lemmas, whose hypotheses are discharged
by `E`'s bundled fields (`IsElliptic` and `B_nonzero`). -/
instance (E : SWCurve F) : AddCommGroup (SWPoint E) where
  add := sw_add
  zero := SWPoint.zero E
  neg := sw_neg
  nsmul := binNsmul sw_add (SWPoint.zero E)
  nsmul_zero P := binNsmul_zero _ _ P
  nsmul_succ n P := by
    haveI := instIsElliptic E
    refine binNsmul_succ ?_ ?_ n P
    · exact fun a b c => SWPoint.ext_pair (add_assoc E.B_nonzero a.onCurve b.onCurve c.onCurve)
    · exact fun a => SWPoint.ext_pair (ShortWeierstrass.add_zero E.A (a.x, a.y))
  zsmul := zsmulRec
  add_assoc P Q R := by
    haveI := instIsElliptic E
    exact SWPoint.ext_pair (add_assoc E.B_nonzero P.onCurve Q.onCurve R.onCurve)
  zero_add P := SWPoint.ext_pair (ShortWeierstrass.zero_add E.A (P.x, P.y))
  add_zero P := SWPoint.ext_pair (ShortWeierstrass.add_zero E.A (P.x, P.y))
  add_comm P Q := SWPoint.ext_pair (add_comm P.onCurve Q.onCurve)
  neg_add_cancel P := SWPoint.ext_pair (by
    show add E.A (neg (P.x, P.y)) (P.x, P.y) = (0, 0)
    rw [add_comm (valid_neg P.onCurve) P.onCurve]
    exact add_neg E.A (P.x, P.y))

/-- The group action `n • P` on `SWPoint E` is equivalent to the spec-level `smul` on the underlying
coordinates, so the two notions of scalar multiplication agree. -/
theorem coords_nsmul {E : SWCurve F} (n : ℕ) (P : SWPoint E) :
    ((n • P).x, (n • P).y) = smul E.A n (P.x, P.y) := by
  induction n with
  | zero => rw [zero_nsmul]; rfl
  | succ k ih =>
    rw [succ_nsmul]
    show add E.A ((k • P).x, (k • P).y) (P.x, P.y) = smul E.A (k + 1) (P.x, P.y)
    rw [ih]
    rfl

/-! ### Mathlib's points

`SWPoint E` and Mathlib's affine points of `toW E.A E.B` are additively equivalent
(`SWPoint.equivPoint`): the identity `(0, 0)` goes to `0` and every other point to its coordinates.
The map is defined by cases on `P = 0`, so it is computable; it agrees with `toPt`
(`SWPoint.toPoint_eq_toPt`), whose `toPt_add` makes it additive. -/

/-- The Mathlib point of `P`: `0` for the identity, the same coordinates otherwise. -/
def SWPoint.toPoint {E : SWCurve F} (P : SWPoint E) : (toW E.A E.B).toAffine.Point :=
  if h : P = 0 then 0 else .some P.x P.y (nonsingular_toW (onCurve_of_ne_zero h))

/-- The point of `E` with the coordinates of a Mathlib point, and the identity for `0`. -/
def SWPoint.ofPoint {E : SWCurve F} : (toW E.A E.B).toAffine.Point → SWPoint E
  | .zero => 0
  | .some x y h => ⟨x, y, Or.inl (equation_toW.mp h.1)⟩

/-- `toPoint` is `toPt` on the coordinates. -/
theorem SWPoint.toPoint_eq_toPt {E : SWCurve F} (P : SWPoint E) :
    P.toPoint = toPt E.A E.B (P.x, P.y) := by
  unfold toPoint
  split_ifs with h
  · subst h; exact (toPt_zero E.B_nonzero).symm
  · exact (toPt_some (onCurve_of_ne_zero h)).symm

/-- **The additive equivalence** between `SWPoint E` and Mathlib's affine points of
`toW E.A E.B`. -/
def SWPoint.equivPoint (E : SWCurve F) : SWPoint E ≃+ (toW E.A E.B).toAffine.Point where
  toFun := toPoint
  invFun := ofPoint
  left_inv := by
    rintro ⟨x, y, hv⟩
    rw [toPoint_eq_toPt]
    rcases hv with hO | h0
    · show ofPoint (toPt E.A E.B (x, y)) = _
      rw [toPt_some hO]
      rfl
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h0
      show ofPoint (toPt E.A E.B (0, 0)) = _
      rw [toPt_zero E.B_nonzero]
      rfl
  right_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · show toPoint 0 = 0
      rw [toPoint_eq_toPt]; exact toPt_zero E.B_nonzero
    · show toPoint ⟨x, y, _⟩ = _
      rw [toPoint_eq_toPt]; exact toPt_some (equation_toW.mp h.1)
  map_add' P Q := by
    simp only [toPoint_eq_toPt]
    exact toPt_add E.B_nonzero P.onCurve Q.onCurve

omit [DecidableEq F] in
/-- `ofPoint` on an affine point keeps its coordinates. -/
theorem SWPoint.ofPoint_some {E : SWCurve F} {x y : F}
    (h : (toW E.A E.B).toAffine.Nonsingular x y) :
    (ofPoint (.some x y h) : SWPoint E) = ⟨x, y, Or.inl (equation_toW.mp h.1)⟩ := rfl

/-! ### Distinct `x`-coordinates

The curve fact behind the Distinct-`x` theorem of the Zcash Protocol Specification
[§A.3.3.4 "Affine-Montgomery
arithmetic"](https://zips.z.cash/protocol/protocol.pdf#cctmontarithmetic): multiples
`[k₁] Q`, `[k₂] Q` of a point `Q` of order `s`, with nonzero `k₁`, `k₂` of absolute value at most
`(s − 1)/2` and `k₂ ≠ ±k₁`, have distinct `x`-coordinates. The specification states it for `Q` of
odd-prime order on a Montgomery curve, as a theorem about its incomplete addition constraints;
here it is the curve fact alone, on any short Weierstrass curve, and it needs only the order of
`Q`. -/

/-- An integer multiple `[k] Q` of a point of order `s` is `0` only if `k = 0`, when `|k| < s`. -/
theorem SWPoint.zsmul_ne_zero_of_abs_lt {E : SWCurve F} {Q : SWPoint E} {s : ℕ}
    (hQ : addOrderOf Q = s) {k : ℤ} (hk : k ≠ 0) (hks : |k| < s) : k • Q ≠ 0 := by
  intro h
  rw [← hQ] at hks
  exact hk (Int.eq_zero_of_abs_lt_dvd (addOrderOf_dvd_iff_zsmul_eq_zero.mpr h) hks)

/-- **Distinct `x`.** For `Q` of order `s` and nonzero integers `k₁`, `k₂` with `|kᵢ| ≤ (s − 1)/2`
and `k₂ ≠ ±k₁`, the points `[k₁] Q` and `[k₂] Q` have distinct `x`-coordinates: points sharing an
`x` are equal up to sign (`SWPoint.eq_pm_of_x_eq`), and `[k₁] Q = ±[k₂] Q` would make `s` divide
`k₁ ∓ k₂`, which is nonzero and of absolute value less than `s`. -/
theorem SWPoint.x_ne_of_addOrderOf {E : SWCurve F} {Q : SWPoint E} {s : ℕ}
    (hQ : addOrderOf Q = s) {k₁ k₂ : ℤ} (hk₁ : k₁ ≠ 0) (hk₂ : k₂ ≠ 0)
    (hb₁ : |k₁| ≤ ((s - 1) / 2 : ℕ)) (hb₂ : |k₂| ≤ ((s - 1) / 2 : ℕ)) (hne : k₂ ≠ k₁)
    (hne' : k₂ ≠ -k₁) : (k₁ • Q).x ≠ (k₂ • Q).x := by
  -- `k₁ ≠ 0` forces `s ≥ 3`, so two elements of the range sum to less than `s` in absolute
  -- value.
  have h1 : (1 : ℤ) ≤ ((s - 1) / 2 : ℕ) := (Int.one_le_abs hk₁).trans hb₁
  have hs : (((s - 1) / 2 : ℕ) : ℤ) + ((s - 1) / 2 : ℕ) < s := by omega
  have hb₁' : |k₁| < s := by linarith
  have hb₂' : |k₂| < s := by linarith
  intro hx
  rcases eq_pm_of_x_eq (zsmul_ne_zero_of_abs_lt hQ hk₁ hb₁')
    (zsmul_ne_zero_of_abs_lt hQ hk₂ hb₂') hx with h | h
  · have hd : |k₁ - k₂| < s := (abs_sub _ _).trans_lt (by linarith)
    exact zsmul_ne_zero_of_abs_lt hQ (sub_ne_zero.mpr (Ne.symm hne)) hd
      (by rw [sub_zsmul, h, add_neg_cancel])
  · have hd : |k₁ + k₂| < s := (abs_add_le _ _).trans_lt (by linarith)
    exact zsmul_ne_zero_of_abs_lt hQ (fun e => hne' (by linarith)) hd
      (by rw [add_zsmul, h, neg_add_cancel])

/-! ### Scalar multiples from a chain of slope certificates

To prove `[n] B = R` for concrete points, supply the slope of each chord and tangent in a
double-and-add chain. `runChain` checks every slope by multiplying back,
`l * (x₂ - x₁) = y₂ - y₁` or `l * (2*y) = 3 * x^2 + A`, and computes the next point from it by
multiplication alone, so the kernel never inverts a field element. `SWPoint.runChain_sound` turns
a successful run into the scalar multiple, with no `native_decide`. -/

/-- A chord step of the raw `add`: for distinct abscissas, a slope `l` with
`l * (x₂ - x₁) = y₂ - y₁` determines the sum. -/
theorem add_of_chord_slope (a : F) {x₁ y₁ x₂ y₂ l x₃ y₃ : F}
    (h₁ : (x₁, y₁) ≠ (0, 0)) (h₂ : (x₂, y₂) ≠ (0, 0)) (hx : x₁ ≠ x₂)
    (hl : l * (x₂ - x₁) = y₂ - y₁) (hx₃ : x₃ = l^2 - x₁ - x₂) (hy₃ : y₃ = l * (x₁ - x₃) - y₁) :
    add a (x₁, y₁) (x₂, y₂) = (x₃, y₃) := by
  have hl' : (y₂ - y₁) / (x₂ - x₁) = l := by
    rw [div_eq_iff (sub_ne_zero.mpr (Ne.symm hx))]; exact hl.symm
  simp only [add, h₁, h₂, hx, if_false, hl', hx₃, hy₃]

/-- A tangent step of the raw `add`: for `y ≠ -y`, a slope `l` with `l * (2*y) = 3 * x^2 + a`
determines the double. -/
theorem add_of_tangent_slope (a : F) {x y l x₃ y₃ : F} (hy : y + y ≠ 0)
    (hl : l * (2*y) = 3 * x^2 + a) (hx₃ : x₃ = l^2 - x - x) (hy₃ : y₃ = l * (x - x₃) - y) :
    add a (x, y) (x, y) = (x₃, y₃) := by
  -- `(0, 0)` has `y + y = 0`, so `hy` already rules out the identity sentinel.
  have h : (x, y) ≠ (0, 0) := fun h => hy (by simp [(Prod.mk.inj h).2])
  have h2y : (2 : F) * y ≠ 0 := by rwa [two_mul]
  have hl' : (3 * x^2 + a) / (2*y) = l := by rw [div_eq_iff h2y]; exact hl.symm
  simp only [add, h, hy, if_true, if_false, hl', hx₃, hy₃]

/-- One step of a double-and-add chain, carrying the slope that certifies it: double the current
point, or add the base point. -/
inductive ChainStep (F : Type*)
  | double (l : F)
  | addBase (l : F)

/-- The point one step reaches from `P`, when its slope checks. A doubling needs
`l * (2*y) = 3 * x^2 + a` and `y + y ≠ 0`; an addition of `B` needs `P ≠ (0, 0)`, `x ≠ x_B` and
`l * (x_B - x) = y_B - y`. -/
def ChainStep.next (a : F) (B P : F × F) : ChainStep F → Option (F × F)
  | .double l =>
    if l * (2*P.2) = 3 * P.1^2 + a ∧ P.2 + P.2 ≠ 0 then
      some (l^2 - P.1 - P.1, l * (P.1 - (l^2 - P.1 - P.1)) - P.2)
    else none
  | .addBase l =>
    if P ≠ (0, 0) ∧ P.1 ≠ B.1 ∧ l * (B.1 - P.1) = B.2 - P.2 then
      some (l^2 - P.1 - B.1, l * (P.1 - (l^2 - P.1 - B.1)) - P.2)
    else none

/-- Run a chain from `P`, failing at the first slope that does not check. -/
def runChain (a : F) (B : F × F) : F × F → List (ChainStep F) → Option (F × F)
  | P, [] => some P
  | P, s :: ss => (s.next a B P).bind fun Q => runChain a B Q ss

/-- The scalar a chain reaches from `c`: a doubling takes `c` to `2*c`, an addition to `c + 1`. -/
def chainScalar : List (ChainStep F) → ℕ → ℕ
  | [], c => c
  | .double _ :: ss, c => chainScalar ss (2*c)
  | .addBase _ :: ss, c => chainScalar ss (c + 1)

/-- **A checked chain computes a scalar multiple.** If `c • B = P` and the chain runs from `P` to
`R`, then `R` is the point `(chainScalar steps c) • B`. -/
theorem SWPoint.runChain_sound {E : SWCurve F} {B : SWPoint E} (hB : B ≠ 0) :
    ∀ (steps : List (ChainStep F)) {c : ℕ} {P : SWPoint E} {R : F × F}, c • B = P →
      runChain E.A (B.x, B.y) (P.x, P.y) steps = some R →
      ∃ Q : SWPoint E, (chainScalar steps c) • B = Q ∧ (Q.x, Q.y) = R := by
  have hB' : (B.x, B.y) ≠ (0, 0) := fun h => hB (SWPoint.ext_pair h)
  intro steps
  induction steps with
  | nil =>
    intro c P R hP h
    exact ⟨P, hP, Option.some.inj h⟩
  | cons s ss ih =>
    intro c P R hP h
    simp only [runChain, Option.bind_eq_some_iff] at h
    obtain ⟨Q', hQ', hrun⟩ := h
    -- Each step takes the actual group sum (`P + P` or `P + B`) and shows its coordinates are the
    -- computed ones, so the computed point never needs its own on-curve proof.
    cases s with
    | double l =>
      simp only [ChainStep.next] at hQ'
      split_ifs at hQ' with hc
      obtain ⟨hl, hy⟩ := hc
      have hcoords : ((P + P).x, (P + P).y) = Q' := by
        rw [SWPoint.add_x, SWPoint.add_y, add_of_tangent_slope E.A hy hl rfl rfl]
        exact Option.some.inj hQ'
      exact ih (c := 2*c) (P := P + P) (by rw [two_mul, add_nsmul, hP]) (hcoords ▸ hrun)
    | addBase l =>
      simp only [ChainStep.next] at hQ'
      split_ifs at hQ' with hc
      obtain ⟨hP0, hx, hl⟩ := hc
      have hcoords : ((P + B).x, (P + B).y) = Q' := by
        rw [SWPoint.add_x, SWPoint.add_y, add_of_chord_slope E.A hP0 hB' hx hl rfl rfl]
        exact Option.some.inj hQ'
      exact ih (c := c + 1) (P := P + B) (by rw [add_nsmul, one_nsmul, hP]) (hcoords ▸ hrun)

/-! ## The affine coordinate system

`E` as an instance of the general `CoordinateSystem` abstraction: the injective (`Rel = Eq`) case,
built from the proven affine group law. This validates `CoordinateSystem` against a real curve. Its
`.Quot` is the affine group element (a quotient by `Eq`, hence isomorphic to `SWPoint E`). -/

/-- The affine coordinate system of a short-Weierstrass curve `E` (`Rel = Eq`). -/
def affineCoordinateSystem (E : SWCurve F) : CoordinateSystem (F × F) :=
  haveI := instIsElliptic E
  { Valid := ShortWeierstrass.Valid E.A E.B
    Rel := Eq
    zero := (0, 0)
    add := ShortWeierstrass.add E.A
    neg := ShortWeierstrass.neg
    valid_zero := Or.inr rfl
    valid_add := fun hp hq => ShortWeierstrass.valid_add hp hq
    valid_neg := fun h => ShortWeierstrass.valid_neg h
    rel_refl := fun _ => rfl
    rel_symm := Eq.symm
    rel_trans := Eq.trans
    add_congr := fun ha hb => by rw [ha, hb]
    neg_congr := fun ha => by rw [ha]
    zero_add := fun {p} _ => ShortWeierstrass.zero_add E.A p
    add_zero := fun {p} _ => ShortWeierstrass.add_zero E.A p
    add_assoc := fun hp hq hr => ShortWeierstrass.add_assoc E.B_nonzero hp hq hr
    add_comm := fun hp hq => ShortWeierstrass.add_comm hp hq
    neg_add := fun {p} h => by
      rw [ShortWeierstrass.add_comm (ShortWeierstrass.valid_neg h) h]
      exact ShortWeierstrass.add_neg E.A p }

end CompElliptic.CurveForms.ShortWeierstrass
