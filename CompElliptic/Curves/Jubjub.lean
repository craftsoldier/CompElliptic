/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Julian Abraham
-/
import CompElliptic.CurveForms.ShortWeierstrass
import CompElliptic.Fields.BLS12_381

/-!
# The Jubjub curve in short-Weierstrass form

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

The twisted Edwards and Montgomery forms, and the isomorphism between their groups and this one,
are not defined here: the facts in `Curves/JubjubOrder.lean` are about this model.

The coefficients are literals, each proved equal to its formula in the specification's
parameters, so the kernel never inverts a field element to evaluate them.
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
That curve has `B = 4/(a - d)`; relating it to `𝕄`, which has `B = 1`, is part of the
isomorphism, not defined here. -/
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

end CompElliptic.Curves.Jubjub
