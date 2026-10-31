/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Julian Abraham
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import CompElliptic.CurveForms.CtEdwards
import CompElliptic.CurveForms.CtEdwardsMontgomeryCertificates
import CompElliptic.CurveForms.Montgomery

/-!
# Complete twisted Edwards curves as Montgomery curves

Every complete twisted Edwards curve `E : a·u² + v² = 1 + d·u²·v²` is birationally equivalent to
the Montgomery curve `B·y² = x³ + A·x² + x` with `A = 2·(a + d)/(a − d)` and `B = 4/(a − d)`
(Bernstein–Birkner–Joye–Lange–Peters, [Twisted Edwards
Curves](https://eprint.iacr.org/2008/013), Theorem 3.2). This module proves that the equivalence,
extended to all points, is an isomorphism of groups: `CtEdwardsPoint.montgomeryEquiv` is an
additive equivalence between the points of `E` and the affine points of the Montgomery curve's
Mathlib model `E.montgomery` (`CurveForms/Montgomery.lean`). Completeness is the only hypothesis,
with `[DecidableEq F]`, which Mathlib's addition needs.

## The map

`toMontgomeryXY` is the map `(u, v) ↦ ((1 + v)/(1 − v), (1 + v)/((1 − v)·u))`, which is
undefined at `(0, 1)` and `(0, −1)`.
`CtEdwardsPoint.toMontgomery` sends `(0, 1)` to the point at infinity and every other point to
its image, scaled by `1/B` onto the model; Lean's `0/0 = 0` sends `(0, −1)` to `(0, 0)`, the
Montgomery point of order `2`. The inverse, `CtEdwardsPoint.ofMontgomery`, is
`(x, y) ↦ (x/y, (x − 1)/(x + 1))`, which needs the facts about exceptional points of the Zcash
Protocol Specification [§A.3.3.3 "ctEdwards ↔ Montgomery
conversion"](https://zips.z.cash/protocol/protocol.pdf#cctconversion).

## Addition

`toMontgomery_add` follows the cases of Mathlib's addition: an identity, `P + (−P)`, a chord
(`P.v ≠ Q.v`), and a tangent (`Q = P`). The chord and tangent cases apply the certificates of
`CurveForms/CtEdwardsMontgomeryCertificates.lean`. They take the `y`-coordinate in the form
`u·(a − d·v²)/(1 − v)²`, equal to `toMontgomeryXY`'s on the curve (`toMontgomeryY_eq`), which
has no `u` in a denominator; so `(0, −1)` as a summand or as the sum needs no separate case.
Bernstein–Lange ([Montgomery curves and the Montgomery
ladder](https://cr.yp.to/papers/montladder-20170330.pdf), §4.3.5) note that the equivalence
extends to a group isomorphism; the proof here is ours.
-/

namespace CompElliptic.CurveForms.CtEdwards

variable {F : Type*} [Field F]

/-! ## The Montgomery model -/

/-- The Montgomery parameter `A = 2·(a + d)/(a − d)`. -/
def CtEdwardsCurve.montA (E : CtEdwardsCurve F) : F := 2 * (E.a + E.d) / (E.a - E.d)

/-- The Montgomery parameter `B = 4/(a − d)`. -/
def CtEdwardsCurve.montB (E : CtEdwardsCurve F) : F := 4 / (E.a - E.d)

/-- The Montgomery curve of `E`, as a Mathlib `WeierstrassCurve`. -/
def CtEdwardsCurve.montgomery (E : CtEdwardsCurve F) : WeierstrassCurve F :=
  Montgomery.toW E.montA E.montB

variable (E : CtEdwardsCurve F)

omit E in
/-- `4 ≠ 0`, since `2 ≠ 0`. -/
theorem CtEdwardsCurve.four_ne_zero (E : CtEdwardsCurve F) : (4 : F) ≠ 0 := by
  rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero E.F_nonbinary E.F_nonbinary

/-- `a − d ≠ 0`: `a` is a square and `d` is not. -/
theorem CtEdwardsCurve.a_sub_d_ne_zero : E.a - E.d ≠ 0 := _root_.sub_ne_zero.mpr a_ne_d

/-- `B ≠ 0`. -/
theorem CtEdwardsCurve.montB_ne_zero : E.montB ≠ 0 :=
  div_ne_zero E.four_ne_zero E.a_sub_d_ne_zero

/-- `A² − 4 = 16·a·d/(a − d)²`. -/
theorem CtEdwardsCurve.montA_sq_sub_four :
    E.montA ^ 2 - 4 = 16 * E.a * E.d / (E.a - E.d) ^ 2 := by
  have := E.a_sub_d_ne_zero
  unfold CtEdwardsCurve.montA
  field_simp
  ring

/-- `A² − 4` is a non-square, since `a·d` is: `a` is a nonzero square and `d` is not. -/
theorem CtEdwardsCurve.not_isSquare_montA_sq_sub_four : ¬ IsSquare (E.montA ^ 2 - 4) := by
  rintro ⟨r, hr⟩
  obtain ⟨s, hs⟩ := E.a_square
  have hs0 : s ≠ 0 := by rintro rfl; exact E.a_nonzero (by rw [hs]; ring)
  have had := E.a_sub_d_ne_zero
  have four := E.four_ne_zero
  rw [E.montA_sq_sub_four] at hr
  apply E.d_nonsquare
  refine ⟨r * (E.a - E.d) / (4 * s), ?_⟩
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero (mul_ne_zero four hs0) (mul_ne_zero four hs0))]
  rw [div_eq_iff (pow_ne_zero 2 had)] at hr
  linear_combination hr - 16 * E.d * hs

/-- `(A − 2)/B = d`. -/
theorem CtEdwardsCurve.montA_sub_two_div_montB : (E.montA - 2) / E.montB = E.d := by
  have := E.a_sub_d_ne_zero
  have := E.four_ne_zero
  unfold CtEdwardsCurve.montA CtEdwardsCurve.montB
  field_simp
  ring

/-- The Montgomery model is nonsingular: `B ≠ 0` and `A² − 4` is a non-square. -/
instance CtEdwardsCurve.instIsEllipticMontgomery : E.montgomery.IsElliptic :=
  Montgomery.isElliptic_toW E.F_nonbinary E.montB_ne_zero
    (fun h => E.not_isSquare_montA_sq_sub_four (by rw [h]; exact IsSquare.zero))

/-! ## The map on coordinates -/

omit E in
/-- The map to Montgomery coordinates,
`(u, v) ↦ ((1 + v)/(1 − v), (1 + v)/((1 − v)·u))`. -/
def toMontgomeryXY (p : F × F) : F × F :=
  ((1 + p.2) / (1 - p.2), (1 + p.2) / ((1 - p.2) * p.1))

/-- `a − d·v²` never vanishes: `a` is a nonzero square and `d` is not a square. -/
theorem CtEdwardsCurve.a_sub_d_mul_sq_ne_zero (v : F) : E.a - E.d * v ^ 2 ≠ 0 := by
  intro h
  by_cases hv : v = 0
  · subst hv; apply E.a_nonzero; linear_combination h
  · obtain ⟨r, hr⟩ := E.a_square
    apply E.d_nonsquare
    refine ⟨r / v, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hv hv)]
    linear_combination -h + hr

/-- On the curve, away from `(0, 1)`, the map's `y` is `u·(a − d·v²)/(1 − v)²`, which
has no `u` in its denominator. At `(0, −1)` both are `0`. -/
theorem toMontgomeryY_eq {u v : F} (h : OnCurve E.a E.d (u, v)) (hv : v ≠ 1) :
    (toMontgomeryXY (u, v)).2 = u * (E.a - E.d * v ^ 2) / (1 - v) ^ 2 := by
  simp only [toMontgomeryXY]
  by_cases hu : u = 0
  · subst hu; simp
  have hm : 1 - v ≠ 0 := _root_.sub_ne_zero.mpr (Ne.symm hv)
  unfold OnCurve at h
  rw [div_eq_div_iff (mul_ne_zero hm hu) (pow_ne_zero 2 hm)]
  linear_combination (v - 1) * h

/-- The image of a point other than `(0, 1)` lies on the Montgomery curve. -/
theorem onCurve_toMontgomeryXY {u v : F} (h : OnCurve E.a E.d (u, v)) (hv : v ≠ 1) :
    Montgomery.OnCurve E.montA E.montB (toMontgomeryXY (u, v)) := by
  have had := E.a_sub_d_ne_zero
  have hm : 1 - v ≠ 0 := _root_.sub_ne_zero.mpr (Ne.symm hv)
  by_cases hu : u = 0
  · subst hu
    have hv' : v = -1 := by
      unfold OnCurve at h
      have : (v - 1) * (v + 1) = 0 := by linear_combination h
      exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.1 this).resolve_left (_root_.sub_ne_zero.2 hv))
    subst hv'
    simp [toMontgomeryXY, Montgomery.OnCurve]
  unfold OnCurve at h
  simp only at h
  simp only [Montgomery.OnCurve, toMontgomeryXY, CtEdwardsCurve.montA, CtEdwardsCurve.montB]
  field_simp
  -- the bracket is `4·(a − d·v²)`, and `u²·(a − d·v²) = 1 − v²` on the curve
  linear_combination (-4 * (1 + v)) * h

/-! ## Chord and tangent

The four certificates of `CurveForms/CtEdwardsMontgomeryCertificates.lean`, applied: each clears
the denominators with `field_simp` and closes with a constant multiple of a certificate. The
statements are generic in `a`, `d` and the coordinates, and composite denominators are named
(`generalize`) before `field_simp`, so that its output, and with it the constant, is fixed. -/

/-- Montgomery `x` of `(u, v)`. -/
private def mX (v : F) : F := (1 + v) / (1 - v)

/-- Montgomery `y` of `(u, v)` in the form without `u` in a denominator (`toMontgomeryY_eq`). -/
private def mY (a d u v : F) : F := u * (a - d * v ^ 2) / (1 - v) ^ 2

private def mA (a d : F) : F := 2 * (a + d) / (a - d)
private def mB (a d : F) : F := 4 / (a - d)

private theorem mX_div {n m : F} (hm : m ≠ 0) : mX (n / m) = (m + n) / (m - n) := by
  unfold mX; rw [one_add_div hm, one_sub_div hm, div_div_div_cancel_right₀ hm, _root_.add_comm]

private theorem slope_mY_eq {a d u1 v1 u2 v2 : F} (h1 : 1 - v1 ≠ 0) (h2 : 1 - v2 ≠ 0)
    (h12 : v1 - v2 ≠ 0)
    (two : (2 : F) ≠ 0) :
    (mY a d u1 v1 - mY a d u2 v2) / (mX v1 - mX v2)
      = (u1 * (a - d * v1 ^ 2) * (1 - v2) ^ 2 - u2 * (a - d * v2 ^ 2) * (1 - v1) ^ 2)
          / (2 * (v1 - v2) * (1 - v1) * (1 - v2)) := by
  have e : mX v1 - mX v2 = 2 * (v1 - v2) / ((1 - v1) * (1 - v2)) := by
    unfold mX; field_simp; ring
  rw [e]; unfold mY; field_simp

private theorem mY_div {a d p q n m : F} (hq : q ≠ 0) (hm : m ≠ 0) :
    mY a d (p / q) (n / m) = p * (a * m ^ 2 - d * n ^ 2) / (q * (m - n) ^ 2) := by
  unfold mY; rw [one_sub_div hm]; field_simp

private theorem toMontgomery_chord_x {a d u1 v1 u2 v2 : F}
    (c1 : a * u1 ^ 2 + v1 ^ 2 = 1 + d * u1 ^ 2 * v1 ^ 2)
    (c2 : a * u2 ^ 2 + v2 ^ 2 = 1 + d * u2 ^ 2 * v2 ^ 2)
    (had : a - d ≠ 0) (h1 : 1 - v1 ≠ 0) (h2 : 1 - v2 ≠ 0)
    (h12 : v1 - v2 ≠ 0) (htm : 1 - d * u1 * u2 * v1 * v2 ≠ 0)
    (h3 : 1 - d * u1 * u2 * v1 * v2 - (v1 * v2 - a * u1 * u2) ≠ 0) (two : (2 : F) ≠ 0) :
    let l := (mY a d u1 v1 - mY a d u2 v2) / (mX v1 - mX v2)
    mB a d * l ^ 2 - mA a d - mX v1 - mX v2
      = mX ((v1 * v2 - a * u1 * u2) / (1 - d * u1 * u2 * v1 * v2)) := by
  intro l
  have hN := toMontgomery_chord_x_certificate a d u1 v1 u2 v2 (by linear_combination c1)
    (by linear_combination c2)
  rw [← sub_eq_zero]
  simp only [l]
  rw [slope_mY_eq h1 h2 h12 two, mX_div htm]
  simp only [mX, mA, mB]
  generalize hM : (1 - d * u1 * u2 * v1 * v2) - (v1 * v2 - a * u1 * u2) = M at h3 ⊢
  field_simp
  subst hM
  linear_combination (-1 : F) * hN

private theorem toMontgomery_chord_y {a d u1 v1 u2 v2 : F}
    (c1 : a * u1 ^ 2 + v1 ^ 2 = 1 + d * u1 ^ 2 * v1 ^ 2)
    (c2 : a * u2 ^ 2 + v2 ^ 2 = 1 + d * u2 ^ 2 * v2 ^ 2)
    (h1 : 1 - v1 ≠ 0) (h2 : 1 - v2 ≠ 0)
    (h12 : v1 - v2 ≠ 0) (htm : 1 - d * u1 * u2 * v1 * v2 ≠ 0)
    (htp : 1 + d * u1 * u2 * v1 * v2 ≠ 0)
    (h3 : 1 - d * u1 * u2 * v1 * v2 - (v1 * v2 - a * u1 * u2) ≠ 0) (two : (2 : F) ≠ 0) :
    let l := (mY a d u1 v1 - mY a d u2 v2) / (mX v1 - mX v2)
    l * (mX v1 - mX ((v1 * v2 - a * u1 * u2) / (1 - d * u1 * u2 * v1 * v2))) - mY a d u1 v1
      = mY a d ((u1 * v2 + v1 * u2) / (1 + d * u1 * u2 * v1 * v2))
          ((v1 * v2 - a * u1 * u2) / (1 - d * u1 * u2 * v1 * v2)) := by
  intro l
  have hN := toMontgomery_chord_y_certificate a d u1 v1 u2 v2 (by linear_combination c1)
    (by linear_combination c2)
  rw [← sub_eq_zero]
  simp only [l]
  rw [slope_mY_eq h1 h2 h12 two, mY_div htp htm, mX_div htm]
  simp only [mX, mY]
  generalize hM : (1 - d * u1 * u2 * v1 * v2) - (v1 * v2 - a * u1 * u2) = M at h3 ⊢
  generalize hQ : 1 + d * u1 * u2 * v1 * v2 = Q at htp ⊢
  field_simp
  subst hM hQ
  linear_combination (v1 - 1) * hN

private theorem toMontgomery_tangent_x {a d u1 v1 : F}
    (c1 : a * u1 ^ 2 + v1 ^ 2 = 1 + d * u1 ^ 2 * v1 ^ 2)
    (had : a - d ≠ 0) (hu1 : u1 ≠ 0) (h1 : 1 - v1 ≠ 0) (hav : a - d * v1 ^ 2 ≠ 0)
    (htm : 1 - d * u1 ^ 2 * v1 ^ 2 ≠ 0)
    (h3 : 1 - d * u1 ^ 2 * v1 ^ 2 - (v1 ^ 2 - a * u1 ^ 2) ≠ 0) (two : (2 : F) ≠ 0) :
    let l := (3 * mX v1 ^ 2 + 2 * mA a d * mX v1 + 1) / (2 * mB a d * mY a d u1 v1)
    mB a d * l ^ 2 - mA a d - 2 * mX v1
      = mX ((v1 ^ 2 - a * u1 ^ 2) / (1 - d * u1 ^ 2 * v1 ^ 2)) := by
  intro l
  have hN := toMontgomery_tangent_x_certificate a d u1 v1 (by linear_combination c1)
  have four : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero two two
  rw [← sub_eq_zero]
  simp only [l]
  rw [mX_div htm]
  simp only [mX, mY, mA, mB]
  generalize hK : a - d * v1 ^ 2 = K at hav ⊢
  generalize hM : (1 - d * u1 ^ 2 * v1 ^ 2) - (v1 ^ 2 - a * u1 ^ 2) = M at h3 ⊢
  field_simp
  subst hM hK
  apply mul_left_cancel₀ four
  linear_combination (-1 : F) * hN

private theorem toMontgomery_tangent_y {a d u1 v1 : F}
    (c1 : a * u1 ^ 2 + v1 ^ 2 = 1 + d * u1 ^ 2 * v1 ^ 2)
    (had : a - d ≠ 0) (hu1 : u1 ≠ 0) (h1 : 1 - v1 ≠ 0) (hav : a - d * v1 ^ 2 ≠ 0)
    (htm : 1 - d * u1 ^ 2 * v1 ^ 2 ≠ 0) (htp : 1 + d * u1 ^ 2 * v1 ^ 2 ≠ 0)
    (h3 : 1 - d * u1 ^ 2 * v1 ^ 2 - (v1 ^ 2 - a * u1 ^ 2) ≠ 0) (two : (2 : F) ≠ 0) :
    let l := (3 * mX v1 ^ 2 + 2 * mA a d * mX v1 + 1) / (2 * mB a d * mY a d u1 v1)
    l * (mX v1 - mX ((v1 ^ 2 - a * u1 ^ 2) / (1 - d * u1 ^ 2 * v1 ^ 2))) - mY a d u1 v1
      = mY a d (2 * u1 * v1 / (1 + d * u1 ^ 2 * v1 ^ 2))
          ((v1 ^ 2 - a * u1 ^ 2) / (1 - d * u1 ^ 2 * v1 ^ 2)) := by
  intro l
  have hN := toMontgomery_tangent_y_certificate a d u1 v1 (by linear_combination c1)
  have four : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]; exact mul_ne_zero two two
  rw [← sub_eq_zero]
  simp only [l]
  rw [mY_div htp htm, mX_div htm]
  simp only [mX, mY, mA, mB]
  generalize hK : a - d * v1 ^ 2 = K at hav ⊢
  generalize hM : (1 - d * u1 ^ 2 * v1 ^ 2) - (v1 ^ 2 - a * u1 ^ 2) = M at h3 ⊢
  generalize hQ : 1 + d * u1 ^ 2 * v1 ^ 2 = Q at htp ⊢
  field_simp
  subst hM hK hQ
  linear_combination hN

/-! ## The map on points -/

private theorem fst_toMontgomeryXY (u v : F) : (toMontgomeryXY (u, v)).1 = mX v := rfl

private theorem snd_toMontgomeryXY {u v : F} (h : OnCurve E.a E.d (u, v)) (hv : v ≠ 1) :
    (toMontgomeryXY (u, v)).2 = mY E.a E.d u v :=
  toMontgomeryY_eq E h hv

namespace CtEdwardsPoint

variable {E}

/-- The image of a point other than `(0, 1)`, scaled by `1/B`, is on `E.montgomery`. -/
theorem equation_toMontgomery (P : CtEdwardsPoint E) (h : P.v ≠ 1) :
    E.montgomery.toAffine.Equation ((toMontgomeryXY (P.u, P.v)).1 / E.montB)
      ((toMontgomeryXY (P.u, P.v)).2 / E.montB) :=
  (Montgomery.equation_toW E.montB_ne_zero).2 (onCurve_toMontgomeryXY E P.onCurve h)

/-- Equal `v` forces `u` equal or opposite, since `a − d·v² ≠ 0`. -/
theorem u_eq_or_eq_neg_of_v_eq {P Q : CtEdwardsPoint E} (h : P.v = Q.v) :
    Q.u = P.u ∨ Q.u = -P.u := by
  have cP : E.a * P.u ^ 2 + P.v ^ 2 = 1 + E.d * P.u ^ 2 * P.v ^ 2 := P.onCurve
  have cQ : E.a * Q.u ^ 2 + Q.v ^ 2 = 1 + E.d * Q.u ^ 2 * Q.v ^ 2 := Q.onCurve
  rw [← h] at cQ
  have e : (Q.u - P.u) * (Q.u + P.u) * (E.a - E.d * P.v ^ 2) = 0 := by linear_combination cQ - cP
  rcases mul_eq_zero.1 ((mul_eq_zero.1 e).resolve_right (E.a_sub_d_mul_sq_ne_zero P.v)) with h' | h'
  · left; linear_combination h'
  · right; linear_combination h'

variable [DecidableEq F]

/-- The map to the Montgomery model: `(0, 1)` goes to the point at infinity, and every other point
to its image under `toMontgomeryXY`, scaled by `1/B`. -/
def toMontgomery (P : CtEdwardsPoint E) : E.montgomery.toAffine.Point :=
  if h : P.v = 1 then 0 else
    .some _ _ (WeierstrassCurve.Affine.equation_iff_nonsingular.mp (equation_toMontgomery P h))

/-- The identity `(0, 1)` goes to the point at infinity. -/
theorem toMontgomery_zero : toMontgomery (0 : CtEdwardsPoint E) = 0 := by
  unfold toMontgomery; rw [dif_pos (by simp)]

/-- The map commutes with negation, `(u, v) ↦ (−u, v)` on `E`. -/
theorem toMontgomery_neg (P : CtEdwardsPoint E) : toMontgomery (-P) = -toMontgomery P := by
  unfold toMontgomery
  by_cases hP : P.v = 1
  · rw [dif_pos (by simpa using hP), dif_pos hP]; rfl
  · rw [dif_neg (by simpa using hP), dif_neg hP, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    refine ⟨rfl, ?_⟩
    simp only [neg_u, neg_v, toMontgomeryXY, WeierstrassCurve.Affine.negY,
      CtEdwardsCurve.montgomery, Montgomery.toW_a₁, Montgomery.toW_a₃, mul_neg, div_neg, neg_div]
    ring

omit [DecidableEq F] in
private theorem sum_v (P Q : CtEdwardsPoint E) :
    (P + Q).v = (P.v * Q.v - E.a * P.u * Q.u) / (1 - E.d * P.u * Q.u * P.v * Q.v) := by
  rw [add_v]; simp only [add]

omit [DecidableEq F] in
private theorem sum_u (P Q : CtEdwardsPoint E) :
    (P + Q).u = (P.u * Q.v + P.v * Q.u) / (1 + E.d * P.u * Q.u * P.v * Q.v) := by
  rw [add_u]; simp only [add]

/-- The chord case: `P`, `Q` other than `(0, 1)`, with `P.v ≠ Q.v`. -/
private theorem toMontgomery_add_chord (P Q : CtEdwardsPoint E) (hP : P.v ≠ 1) (hQ : Q.v ≠ 1)
    (hne : P.v ≠ Q.v) : toMontgomery (P + Q) = toMontgomery P + toMontgomery Q := by
  have two := E.F_nonbinary
  have had := E.a_sub_d_ne_zero
  have hB := E.montB_ne_zero
  have hS : (P + Q).v ≠ 1 := by
    intro h
    have : Q = -P := eq_neg_of_add_eq_zero_right (eq_zero_of_v_eq_one h)
    exact hne (by rw [this, neg_v])
  obtain ⟨htp, htm⟩ := den_ne_zero P.onCurve Q.onCurve
  have htm' : 1 - E.d * P.u * Q.u * P.v * Q.v ≠ 0 := by convert htm using 2
  have htp' : 1 + E.d * P.u * Q.u * P.v * Q.v ≠ 0 := by convert htp using 2
  have h1 : 1 - P.v ≠ 0 := _root_.sub_ne_zero.2 (Ne.symm hP)
  have h2 : 1 - Q.v ≠ 0 := _root_.sub_ne_zero.2 (Ne.symm hQ)
  have h12 : P.v - Q.v ≠ 0 := _root_.sub_ne_zero.2 hne
  have h3 : 1 - E.d * P.u * Q.u * P.v * Q.v - (P.v * Q.v - E.a * P.u * Q.u) ≠ 0 := by
    intro h; apply hS; rw [sum_v, div_eq_one_iff_eq htm']; linear_combination -h
  have hx : mX P.v ≠ mX Q.v := by
    unfold mX; rw [ne_eq, div_eq_div_iff h1 h2]
    intro h; apply h12; have : (2 : F) * (P.v - Q.v) = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left two
  have cP : E.a * P.u ^ 2 + P.v ^ 2 = 1 + E.d * P.u ^ 2 * P.v ^ 2 := P.onCurve
  have cQ : E.a * Q.u ^ 2 + Q.v ^ 2 = 1 + E.d * Q.u ^ 2 * Q.v ^ 2 := Q.onCurve
  have kx := toMontgomery_chord_x cP cQ had h1 h2 h12 htm' h3 two
  have ky := toMontgomery_chord_y cP cQ h1 h2 h12 htm' htp' h3 two
  simp only at kx ky
  unfold toMontgomery
  rw [dif_neg hS, dif_neg hP, dif_neg hQ, WeierstrassCurve.Affine.Point.add_of_X_ne]
  · rw [WeierstrassCurve.Affine.Point.some.injEq]
    simp only [fst_toMontgomeryXY, snd_toMontgomeryXY E P.onCurve hP,
      snd_toMontgomeryXY E Q.onCurve hQ, snd_toMontgomeryXY E (P + Q).onCurve hS,
      CtEdwardsCurve.montgomery, Montgomery.slope_toW_of_x_ne hB hx]
    have ex : Montgomery.addX E.montA E.montB (mX P.v) (mX Q.v)
        ((mY E.a E.d P.u P.v - mY E.a E.d Q.u Q.v) / (mX P.v - mX Q.v)) = mX (P + Q).v := by
      rw [sum_v]; exact kx
    refine ⟨by rw [Montgomery.addX_toW hB, ex], ?_⟩
    rw [Montgomery.addY_toW hB, Montgomery.addY, ex, sum_v, sum_u, ky]
  · intro h; exact hx (by rwa [div_left_inj' hB] at h)

/-- The tangent case: `P` other than `(0, 1)`, with `u ≠ 0`. -/
private theorem toMontgomery_add_tangent (P : CtEdwardsPoint E) (hP : P.v ≠ 1) (huP : P.u ≠ 0) :
    toMontgomery (P + P) = toMontgomery P + toMontgomery P := by
  have two := E.F_nonbinary
  have had := E.a_sub_d_ne_zero
  have hB := E.montB_ne_zero
  have hS : (P + P).v ≠ 1 := by
    intro h
    have h0 : 2 • P = 0 := by rw [two_nsmul]; exact eq_zero_of_v_eq_one h
    rcases two_nsmul_eq_zero_iff.1 h0 with h' | ⟨h', -⟩
    · exact hP (by rw [h']; rfl)
    · exact huP h'
  obtain ⟨htp, htm⟩ := den_ne_zero P.onCurve P.onCurve
  have htm' : 1 - E.d * P.u ^ 2 * P.v ^ 2 ≠ 0 := by convert htm using 2; ring
  have htp' : 1 + E.d * P.u ^ 2 * P.v ^ 2 ≠ 0 := by convert htp using 2; ring
  have h1 : 1 - P.v ≠ 0 := _root_.sub_ne_zero.2 (Ne.symm hP)
  have hSv : (P + P).v = (P.v ^ 2 - E.a * P.u ^ 2) / (1 - E.d * P.u ^ 2 * P.v ^ 2) := by
    rw [sum_v]; congr 1 <;> ring
  have hSu : (P + P).u = 2 * P.u * P.v / (1 + E.d * P.u ^ 2 * P.v ^ 2) := by
    rw [sum_u]; congr 1 <;> ring
  have h3 : 1 - E.d * P.u ^ 2 * P.v ^ 2 - (P.v ^ 2 - E.a * P.u ^ 2) ≠ 0 := by
    intro h; apply hS; rw [hSv, div_eq_one_iff_eq htm']; linear_combination -h
  have cP : E.a * P.u ^ 2 + P.v ^ 2 = 1 + E.d * P.u ^ 2 * P.v ^ 2 := P.onCurve
  have hav := E.a_sub_d_mul_sq_ne_zero P.v
  have hy : mY E.a E.d P.u P.v ≠ 0 := div_ne_zero (mul_ne_zero huP hav) (pow_ne_zero 2 h1)
  have kx := toMontgomery_tangent_x cP had huP h1 hav htm' h3 two
  have ky := toMontgomery_tangent_y cP had huP h1 hav htm' htp' h3 two
  simp only at kx ky
  have hY : mY E.a E.d P.u P.v / E.montB ≠
      E.montgomery.toAffine.negY (mX P.v / E.montB) (mY E.a E.d P.u P.v / E.montB) := by
    simp only [WeierstrassCurve.Affine.negY, CtEdwardsCurve.montgomery, Montgomery.toW_a₁,
      Montgomery.toW_a₃, zero_mul, sub_zero]
    intro h; apply hy
    have : (2 : F) * (mY E.a E.d P.u P.v / E.montB) = 0 := by linear_combination h
    exact (div_eq_zero_iff.1 ((mul_eq_zero.1 this).resolve_left two)).resolve_right hB
  unfold toMontgomery
  rw [dif_neg hS, dif_neg hP]
  simp only [fst_toMontgomeryXY, snd_toMontgomeryXY E P.onCurve hP]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne hY, WeierstrassCurve.Affine.Point.some.injEq]
  simp only [snd_toMontgomeryXY E (P + P).onCurve hS, CtEdwardsCurve.montgomery,
    Montgomery.slope_toW_self two hB hy]
  have ex : Montgomery.addX E.montA E.montB (mX P.v) (mX P.v)
      ((3 * mX P.v ^ 2 + 2 * E.montA * mX P.v + 1) / (2 * E.montB * mY E.a E.d P.u P.v))
      = mX (P + P).v := by
    rw [hSv, ← kx]; simp only [Montgomery.addX, mA, mB, CtEdwardsCurve.montA,
      CtEdwardsCurve.montB]; ring
  have ky' : (3 * mX P.v ^ 2 + 2 * E.montA * mX P.v + 1) / (2 * E.montB * mY E.a E.d P.u P.v)
        * (mX P.v - mX ((P.v ^ 2 - E.a * P.u ^ 2) / (1 - E.d * P.u ^ 2 * P.v ^ 2)))
        - mY E.a E.d P.u P.v
      = mY E.a E.d (2 * P.u * P.v / (1 + E.d * P.u ^ 2 * P.v ^ 2))
          ((P.v ^ 2 - E.a * P.u ^ 2) / (1 - E.d * P.u ^ 2 * P.v ^ 2)) := ky
  refine ⟨by rw [Montgomery.addX_toW hB, ex], ?_⟩
  rw [Montgomery.addY_toW hB, Montgomery.addY, ex, hSv, hSu, ky']

/-- **The map respects addition.** The cases are those of Mathlib's addition: an identity,
`P + (−P)`, a chord (`P.v ≠ Q.v`), and a tangent (`Q = P`). -/
theorem toMontgomery_add (P Q : CtEdwardsPoint E) :
    toMontgomery (P + Q) = toMontgomery P + toMontgomery Q := by
  by_cases hP : P.v = 1
  · rw [eq_zero_of_v_eq_one hP, _root_.zero_add, toMontgomery_zero, _root_.zero_add]
  by_cases hQ : Q.v = 1
  · rw [eq_zero_of_v_eq_one hQ, _root_.add_zero, toMontgomery_zero, _root_.add_zero]
  by_cases hv : P.v = Q.v
  · by_cases hneg : Q = -P
    · subst hneg
      rw [_root_.add_neg_cancel, toMontgomery_zero, toMontgomery_neg, _root_.add_neg_cancel]
    · have hQP : Q = P := by
        rcases u_eq_or_eq_neg_of_v_eq hv with h | h
        · exact CtEdwardsPoint.ext h hv.symm
        · exact absurd (CtEdwardsPoint.ext (by rw [h, neg_u]) (by rw [neg_v, hv])) hneg
      subst hQP
      have huP : Q.u ≠ 0 := by
        intro h0; apply hneg; exact CtEdwardsPoint.ext (by rw [neg_u, h0, neg_zero]) rfl
      exact toMontgomery_add_tangent Q hP huP
  · exact toMontgomery_add_chord P Q hP hQ hv

end CtEdwardsPoint

/-! ## The inverse -/

omit E in
/-- The map back to ctEdwards coordinates, `(x, y) ↦ (x/y, (x − 1)/(x + 1))`. -/
def ofMontgomeryXY (p : F × F) : F × F := (p.1 / p.2, (p.1 - 1) / (p.1 + 1))

/-- The preimage of a Montgomery point lies on `E`. A point with `y = 0` is `(0, 0)`, whose
preimage is `(0, −1)` by `0/0 = 0`; at any other point `x + 1 ≠ 0`, because `(A − 2)/B = d` is a
non-square. -/
theorem onCurve_ofMontgomeryXY {x y : F} (h : Montgomery.OnCurve E.montA E.montB (x, y)) :
    OnCurve E.a E.d (ofMontgomeryXY (x, y)) := by
  have had := E.a_sub_d_ne_zero
  have four := E.four_ne_zero
  unfold OnCurve ofMontgomeryXY
  by_cases hy : y = 0
  · subst hy
    have hx := Montgomery.x_eq_zero_of_y_eq_zero E.not_isSquare_montA_sq_sub_four h
    subst hx; norm_num
  have hx1 := Montgomery.x_add_one_ne_zero E.montB_ne_zero
    (by rw [E.montA_sub_two_div_montB]; exact E.d_nonsquare) h
  have hm : 4 * y ^ 2 = (E.a - E.d) * x ^ 3 + 2 * (E.a + E.d) * x ^ 2 + (E.a - E.d) * x := by
    unfold Montgomery.OnCurve CtEdwardsCurve.montA CtEdwardsCurve.montB at h
    simp only at h
    field_simp at h
    linear_combination h
  simp only
  field_simp
  linear_combination (-x) * hm

/-- A point of the model is the scaled image of a Montgomery point. -/
theorem onCurve_of_equation {X Y : F} (h : E.montgomery.toAffine.Equation X Y) :
    Montgomery.OnCurve E.montA E.montB (E.montB * X, E.montB * Y) := by
  have hB := E.montB_ne_zero
  rw [← Montgomery.equation_toW hB, mul_div_cancel_left₀ _ hB, mul_div_cancel_left₀ _ hB]
  exact h

namespace CtEdwardsPoint

variable {E} [DecidableEq F]

/-- The map back from the Montgomery model: the point at infinity goes to `(0, 1)`, and an affine
point `(X, Y)` to the preimage of `(B·X, B·Y)`. -/
def ofMontgomery : E.montgomery.toAffine.Point → CtEdwardsPoint E
  | 0 => 0
  | .some X Y h => ⟨(ofMontgomeryXY (E.montB * X, E.montB * Y)).1,
      (ofMontgomeryXY (E.montB * X, E.montB * Y)).2,
      onCurve_ofMontgomeryXY E (onCurve_of_equation E h.1)⟩

/-- `ofMontgomery` is a left inverse of `toMontgomery`. -/
theorem ofMontgomery_toMontgomery (P : CtEdwardsPoint E) : ofMontgomery (toMontgomery P) = P := by
  have two := E.F_nonbinary
  have hB := E.montB_ne_zero
  unfold toMontgomery
  by_cases hP : P.v = 1
  · rw [dif_pos hP, eq_zero_of_v_eq_one hP]; rfl
  rw [dif_neg hP]
  have h1 : 1 - P.v ≠ 0 := _root_.sub_ne_zero.2 (Ne.symm hP)
  apply CtEdwardsPoint.ext
  · show (ofMontgomeryXY (E.montB * ((toMontgomeryXY (P.u, P.v)).1 / E.montB),
      E.montB * ((toMontgomeryXY (P.u, P.v)).2 / E.montB))).1 = P.u
    rw [mul_div_cancel₀ _ hB, mul_div_cancel₀ _ hB]
    simp only [ofMontgomeryXY, toMontgomeryXY]
    by_cases hu : P.u = 0
    · simp [hu]
    have hp1 : 1 + P.v ≠ 0 := by
      intro h; apply hu
      exact (u_eq_zero_iff P.onCurve).2 (Or.inr (by linear_combination h))
    field_simp
  · show (ofMontgomeryXY (E.montB * ((toMontgomeryXY (P.u, P.v)).1 / E.montB),
      E.montB * ((toMontgomeryXY (P.u, P.v)).2 / E.montB))).2 = P.v
    rw [mul_div_cancel₀ _ hB]
    simp only [ofMontgomeryXY, toMontgomeryXY]
    rw [div_sub_one h1, div_add_one h1, div_div_div_cancel_right₀ h1,
      show 1 + P.v - (1 - P.v) = 2 * P.v by ring, show 1 + P.v + (1 - P.v) = 2 by ring,
      mul_div_cancel_left₀ _ two]

/-- `ofMontgomery` is a right inverse of `toMontgomery`. -/
theorem toMontgomery_ofMontgomery (p : E.montgomery.toAffine.Point) :
    toMontgomery (ofMontgomery p) = p := by
  have two := E.F_nonbinary
  have hB := E.montB_ne_zero
  rcases p with _ | ⟨X, Y, h⟩
  · exact toMontgomery_zero
  have hm := onCurve_of_equation E h.1
  generalize hx : E.montB * X = x at hm
  generalize hy : E.montB * Y = y at hm
  have hx1 := Montgomery.x_add_one_ne_zero E.montB_ne_zero
    (by rw [E.montA_sub_two_div_montB]; exact E.d_nonsquare) hm
  have hv : (x - 1) / (x + 1) ≠ 1 := by
    rw [ne_eq, div_eq_one_iff_eq hx1]; intro h; apply two; linear_combination -h
  show toMontgomery ⟨(ofMontgomeryXY (E.montB * X, E.montB * Y)).1,
    (ofMontgomeryXY (E.montB * X, E.montB * Y)).2, _⟩ = _
  unfold toMontgomery
  rw [dif_neg (by simpa only [ofMontgomeryXY, hx] using hv),
    WeierstrassCurve.Affine.Point.some.injEq]
  simp only [ofMontgomeryXY, toMontgomeryXY, hx, hy]
  have hX : X = x / E.montB := by rw [← hx, mul_div_cancel_left₀ _ hB]
  have hY : Y = y / E.montB := by rw [← hy, mul_div_cancel_left₀ _ hB]
  rw [hX, hY]
  have e1 : 1 + (x - 1) / (x + 1) = 2 * x / (x + 1) := by
    rw [one_add_div hx1]; ring_nf
  have e2 : 1 - (x - 1) / (x + 1) = 2 / (x + 1) := by
    rw [one_sub_div hx1]; ring_nf
  rw [e1, e2]
  refine ⟨by rw [div_div_div_cancel_right₀ hx1, mul_div_cancel_left₀ _ two], ?_⟩
  by_cases hy0 : y = 0
  · have hx0 := Montgomery.x_eq_zero_of_y_eq_zero E.not_isSquare_montA_sq_sub_four
      (by rw [hy0] at hm; exact hm)
    subst hx0 hy0; simp
  have hx0 : x ≠ 0 := by
    rintro rfl; apply hy0
    unfold Montgomery.OnCurve at hm
    simp only at hm
    have : E.montB * y ^ 2 = 0 := by linear_combination hm
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1
      ((mul_eq_zero.1 this).resolve_left hB)
  congr 1
  field_simp

/-- **The additive equivalence** between the points of a complete twisted Edwards curve and the
affine points of the Mathlib model of its Montgomery curve. -/
def montgomeryEquiv : CtEdwardsPoint E ≃+ E.montgomery.toAffine.Point where
  toFun := toMontgomery
  invFun := ofMontgomery
  left_inv := ofMontgomery_toMontgomery
  right_inv := toMontgomery_ofMontgomery
  map_add' := toMontgomery_add

end CtEdwardsPoint

/-! ### A small curve

`(a, d) = (4, 2)` over `ZMod 13` is complete: `4 = 2²` is a square and `2` is not (the nonzero
squares mod 13 are 1, 3, 4, 9, 10, 12). Building it shows that the hypotheses of this module can
all hold at once. The examples then check by kernel evaluation, independently of the proof of
`toMontgomery_add`, that the curve has 20 points and that `toMontgomery` respects addition on
all 400 pairs of them. -/

section SmallCurve

local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- The complete twisted Edwards curve `4·u² + v² = 1 + 2·u²·v²` over `ZMod 13`. -/
private def smallCurve : CtEdwardsCurve (ZMod 13) where
  a := 4
  d := 2
  a_nonzero := by decide
  a_square := ⟨2, by decide⟩
  d_nonsquare := by unfold IsSquare; decide
  F_nonbinary := by decide

example : Fintype.card (CtEdwardsPoint smallCurve) = 20 := by decide +kernel

example : ∀ P Q : CtEdwardsPoint smallCurve,
    CtEdwardsPoint.toMontgomery (P + Q) =
      CtEdwardsPoint.toMontgomery P + CtEdwardsPoint.toMontgomery Q := by
  decide +kernel

end SmallCurve

end CompElliptic.CurveForms.CtEdwards
