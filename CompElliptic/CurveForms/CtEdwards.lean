/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood, Julian Abraham
-/
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import CompElliptic.ScalarMul
import CompElliptic.CurveForms.CtEdwardsCertificates

/-!
# Complete twisted Edwards curves

One module for the complete twisted Edwards ("ctEdwards") curve form

`a·u² + v² = 1 + d·u²·v²`, with `a` square and `d` non-square,

as defined in the Zcash Protocol Specification
[§5.4.9.3 "Jubjub"](https://zips.z.cash/protocol/protocol.pdf#jubjub), after Bernstein–Lange,
[Montgomery curves and the Montgomery ladder](https://cr.yp.to/papers/montladder-20170330.pdf),
§4.3.4. On such a curve the addition law has no exceptional cases. Layered as
`ShortWeierstrass.lean`:

1. **Raw computable kernel** — `OnCurve`, `add`, `neg`, `smul` as plain functions on `F × F`,
   and the group laws for them under `IsComplete a d`. Completeness and closure follow
   Bernstein–Lange's proofs; associativity is the certificate of `CtEdwardsCertificates.lean`.
2. **Rich bundled types** — `CtEdwardsCurve` (bundling the completeness conditions and `a ≠ 0`)
   and `CtEdwardsPoint E` (correct by construction: on the curve). The identity `(0, 1)` is an
   affine point, so no sentinel is needed.
3. **Group structure** — `AddCommGroup (CtEdwardsPoint E)`, with the fast scalar action
   `CompElliptic.binNsmul` (`ScalarMul.lean`).

The field assumption is a generic `[Field F]`; the characteristic is kept away from `2` by the
`F_nonbinary` condition.
-/

namespace CompElliptic.CurveForms.CtEdwards

variable {F : Type*} [Field F]

/-! ## Raw computable kernel -/

/-- The curve equation `a·u² + v² = 1 + d·u²·v²`. -/
def OnCurve (a d : F) (p : F × F) : Prop := a * p.1 ^ 2 + p.2 ^ 2 = 1 + d * p.1 ^ 2 * p.2 ^ 2

instance [DecidableEq F] (a d : F) (p : F × F) : Decidable (OnCurve a d p) := by
  unfold OnCurve; infer_instance

/-- The conditions that make the addition law complete: `a` is a square, `d` is not, and the
characteristic is not `2`. The raw group laws take them as `[Fact (IsComplete a d)]`. -/
structure IsComplete (a d : F) : Prop where
  a_square : IsSquare a
  d_nonsquare : ¬ IsSquare d
  F_nonbinary : (2 : F) ≠ 0

/-- The twisted Edwards addition law. -/
def add (a d : F) (p q : F × F) : F × F :=
  ((p.1 * q.2 + p.2 * q.1) / (1 + d * p.1 * q.1 * p.2 * q.2),
   (p.2 * q.2 - a * p.1 * q.1) / (1 - d * p.1 * q.1 * p.2 * q.2))

/-- Negation, `(u, v) ↦ (-u, v)`. -/
def neg (p : F × F) : F × F := (-p.1, p.2)

/-- Spec-level scalar multiplication: iterated `add`, starting from the identity `(0, 1)`. -/
def smul (a d : F) : ℕ → F × F → F × F
  | 0, _ => (0, 1)
  | n + 1, p => add a d (smul a d n p) p

/-- `a ≠ d`, the specification's "distinct": `a` is a square and `d` is not. -/
theorem a_ne_d {a d : F} [h : Fact (IsComplete a d)] : a ≠ d := fun had =>
  h.out.d_nonsquare (had ▸ h.out.a_square)

/-- Completeness: `d·u₁u₂v₁v₂ ≠ ±1` for any two points on the curve.

Bernstein–Lange, [Faster addition and doubling on
elliptic curves](https://cr.yp.to/newelliptic/newelliptic-20070906.pdf), Theorem 3.3, adapted to
twisted curves with `a = s²`. Write `ε = d·u₁u₂v₁v₂` and suppose `ε² = 1`. Then `u₁, v₁ ≠ 0`, and
for each sign `±`:

    d·u₁²v₁²·(a·u₂² + v₂²) = d·u₁²v₁²·(1 + d·u₂²v₂²)      [curve, P₂]
                           = d·u₁²v₁² + ε²                  [defn ε]
                           = 1 + d·u₁²v₁²                   [ε² = 1]
                           = a·u₁² + v₁²                    [curve, P₁]
    (s·u₁ ± ε·v₁)² = a·u₁² + v₁² ± 2·s·ε·u₁v₁
                   = d·(u₁v₁·(s·u₂ ± v₂))²

If `s·u₂ ± v₂ ≠ 0` then `d` is a square, a contradiction. So both vanish, and `v₂ = 0`
(as `2 ≠ 0`), making `ε = 0`: a contradiction. -/
theorem complete {a d : F} [h : Fact (IsComplete a d)] {p q : F × F}
    (hp : OnCurve a d p) (hq : OnCurve a d q) : (d * p.1 * q.1 * p.2 * q.2) ^ 2 ≠ 1 := by
  obtain ⟨u₁, v₁⟩ := p
  obtain ⟨u₂, v₂⟩ := q
  obtain ⟨⟨s, hs⟩, hd, h2⟩ := h.out
  simp only [OnCurve] at hp hq ⊢
  rw [hs] at hp hq
  intro hε
  have square : ∀ σ : F, σ ^ 2 = 1 →
      (s * u₁ + σ * (d * u₁ * u₂ * v₁ * v₂) * v₁) ^ 2
        = d * (u₁ * v₁ * (s * u₂ + σ * v₂)) ^ 2 := fun σ hσ => by
    linear_combination hp - d * u₁ ^ 2 * v₁ ^ 2 * hq + (v₁ ^ 2 - 1) * hε
      + ((d * u₁ * u₂ * v₁ * v₂) ^ 2 * v₁ ^ 2 - d * u₁ ^ 2 * v₁ ^ 2 * v₂ ^ 2) * hσ
  have vanish : ∀ σ : F, σ ^ 2 = 1 → u₁ * v₁ * (s * u₂ + σ * v₂) = 0 := fun σ hσ => by
    by_contra hne
    exact hd ⟨(s * u₁ + σ * (d * u₁ * u₂ * v₁ * v₂) * v₁) / (u₁ * v₁ * (s * u₂ + σ * v₂)), by
      rw [← sq, div_pow, square σ hσ, eq_div_iff (pow_ne_zero 2 hne)]⟩
  have hu₁ : u₁ ≠ 0 := by rintro rfl; simp at hε
  have hv₁ : v₁ ≠ 0 := by rintro rfl; simp at hε
  have hplus := vanish 1 (one_pow 2)
  have hminus := vanish (-1) (by rw [neg_sq, one_pow])
  simp only [mul_eq_zero, hu₁, hv₁, false_or] at hplus hminus
  have hv₂ : v₂ = 0 := by
    have h2v : (2 : F) * v₂ = 0 := by linear_combination hplus - hminus
    simpa [h2] using h2v
  rw [hv₂] at hε
  simp at hε

/-- The addition law's denominators `1 ± d·u₁u₂v₁v₂` never vanish (`complete`). -/
theorem den_ne_zero {a d : F} [Fact (IsComplete a d)] {p q : F × F}
    (hp : OnCurve a d p) (hq : OnCurve a d q) :
    1 + d * p.1 * q.1 * p.2 * q.2 ≠ 0 ∧ 1 - d * p.1 * q.1 * p.2 * q.2 ≠ 0 := by
  have h := complete hp hq
  constructor
  · intro h0; apply h; rw [show d * p.1 * q.1 * p.2 * q.2 = -1 by linear_combination h0]; ring
  · intro h0; apply h; rw [show d * p.1 * q.1 * p.2 * q.2 = 1 by linear_combination -h0]; ring

/-- Closure: `add` stays on the curve.

Bernstein–Lange, *Faster addition and doubling on elliptic curves*, proof of Theorem 3.1,
adapted to twisted curves. Write `ε = d·u₁u₂v₁v₂`, `N_u = u₁v₂ + v₁u₂` and `N_v = v₁v₂ − a·u₁u₂`.
The polynomial identity

    a·N_u²·(1 − ε)² + N_v²·(1 + ε)² − d·N_u²·N_v²
      = (a·u₁² + v₁² − (a·u₂² + v₂²)·d·u₁²v₁²)·(a·u₂² + v₂² − (a·u₁² + v₁²)·d·u₂²v₂²)

holds, and on the curve each factor is `1 − ε²`. Dividing by `(1 + ε)²·(1 − ε)²` gives the curve
equation for the sum. -/
theorem onCurve_add {a d : F} [Fact (IsComplete a d)] {p q : F × F}
    (hp : OnCurve a d p) (hq : OnCurve a d q) : OnCurve a d (add a d p q) := by
  obtain ⟨hu, hv⟩ := den_ne_zero hp hq
  obtain ⟨u₁, v₁⟩ := p
  obtain ⟨u₂, v₂⟩ := q
  simp only [OnCurve, add] at hp hq hu hv ⊢
  have key : a * (u₁ * v₂ + v₁ * u₂) ^ 2 * (1 - d * u₁ * u₂ * v₁ * v₂) ^ 2
      + (v₁ * v₂ - a * u₁ * u₂) ^ 2 * (1 + d * u₁ * u₂ * v₁ * v₂) ^ 2
      - d * (u₁ * v₂ + v₁ * u₂) ^ 2 * (v₁ * v₂ - a * u₁ * u₂) ^ 2
      = (1 - (d * u₁ * u₂ * v₁ * v₂) ^ 2) ^ 2 := by
    linear_combination
      (a * u₂ ^ 2 + v₂ ^ 2 - (a * u₁ ^ 2 + v₁ ^ 2) * d * u₂ ^ 2 * v₂ ^ 2
        - (1 - (d * u₁ * u₂ * v₁ * v₂) ^ 2) * d * u₂ ^ 2 * v₂ ^ 2) * hp
      + ((1 - (d * u₁ * u₂ * v₁ * v₂) ^ 2)
        - (a * u₂ ^ 2 + v₂ ^ 2 - (a * u₁ ^ 2 + v₁ ^ 2) * d * u₂ ^ 2 * v₂ ^ 2)
          * d * u₁ ^ 2 * v₁ ^ 2) * hq
  -- Name the sum `(U, V)` by `U·(1 + ε) = N_u` and `V·(1 − ε) = N_v`; clear the denominators.
  generalize hU : (u₁ * v₂ + v₁ * u₂) / (1 + d * u₁ * u₂ * v₁ * v₂) = U
  generalize hV : (v₁ * v₂ - a * u₁ * u₂) / (1 - d * u₁ * u₂ * v₁ * v₂) = V
  have eU : U * (1 + d * u₁ * u₂ * v₁ * v₂) = u₁ * v₂ + v₁ * u₂ := by
    rw [← hU]; exact div_mul_cancel₀ _ hu
  have eV : V * (1 - d * u₁ * u₂ * v₁ * v₂) = v₁ * v₂ - a * u₁ * u₂ := by
    rw [← hV]; exact div_mul_cancel₀ _ hv
  apply mul_left_cancel₀ (pow_ne_zero 2 (mul_ne_zero hu hv))
  linear_combination key
    + (U * (1 + d * u₁ * u₂ * v₁ * v₂) + (u₁ * v₂ + v₁ * u₂))
      * (a * (1 - d * u₁ * u₂ * v₁ * v₂) ^ 2 - d * (V * (1 - d * u₁ * u₂ * v₁ * v₂)) ^ 2) * eU
    + (V * (1 - d * u₁ * u₂ * v₁ * v₂) + (v₁ * v₂ - a * u₁ * u₂))
      * ((1 + d * u₁ * u₂ * v₁ * v₂) ^ 2 - d * (u₁ * v₂ + v₁ * u₂) ^ 2) * eV

/-- `neg` stays on the curve (`(-u)² = u²`). -/
theorem onCurve_neg {a d : F} {p : F × F} (hp : OnCurve a d p) : OnCurve a d (neg p) := by
  simp only [OnCurve, neg] at hp ⊢; linear_combination hp

/-- Closure of the spec-level `smul`, by induction on `onCurve_add`. -/
theorem onCurve_smul {a d : F} [Fact (IsComplete a d)] {p : F × F} (hp : OnCurve a d p) :
    ∀ n : ℕ, OnCurve a d (smul a d n p)
  | 0 => by simp [smul, OnCurve]
  | n + 1 => onCurve_add (onCurve_smul hp n) hp

/-- `(0, 1)` is a left identity. -/
theorem zero_add (a d : F) (p : F × F) : add a d (0, 1) p = p := by
  obtain ⟨u, v⟩ := p; simp [add]

/-- `(0, 1)` is a right identity. -/
theorem add_zero (a d : F) (p : F × F) : add a d p (0, 1) = p := by
  obtain ⟨u, v⟩ := p; simp [add]

/-- Commutativity: the addition law is symmetric in its two arguments. -/
theorem add_comm (a d : F) (p q : F × F) : add a d p q = add a d q p := by
  simp only [add, Prod.mk.injEq]; constructor <;> ring_nf

/-- `p + neg p = (0, 1)`: the `v` denominator `1 + d·u²v²` is the right-hand side of the curve
equation, and nonzero by `den_ne_zero`. -/
theorem add_neg {a d : F} [Fact (IsComplete a d)] {p : F × F} (hp : OnCurve a d p) :
    add a d p (neg p) = (0, 1) := by
  have hv := (den_ne_zero hp (onCurve_neg hp)).2
  obtain ⟨u, v⟩ := p
  simp only [OnCurve, add, neg, Prod.mk.injEq] at hp hv ⊢
  refine ⟨by ring, ?_⟩
  rw [div_eq_one_iff_eq hv]
  linear_combination hp

/-- Associativity: once the two inner sums are named and every denominator is cleared, a
polynomial identity modulo the three curve equations, `add_assoc_u_certificate` and
`add_assoc_v_certificate`. This is the elementary proof of Hales,
[The group law for Edwards curves](https://arxiv.org/abs/1610.05278), Lemma 3.3.1 (there with
the coordinates swapped). -/
theorem add_assoc {a d : F} [Fact (IsComplete a d)] {p q r : F × F}
    (hp : OnCurve a d p) (hq : OnCurve a d q) (hr : OnCurve a d r) :
    add a d (add a d p q) r = add a d p (add a d q r) := by
  have d₄ := den_ne_zero hp hq
  have d₅ := den_ne_zero hq hr
  have dL := den_ne_zero (onCurve_add hp hq) hr
  have dR := den_ne_zero hp (onCurve_add hq hr)
  generalize hPQ : add a d p q = PQ at dL ⊢
  generalize hQR : add a d q r = QR at dR ⊢
  obtain ⟨u₁, v₁⟩ := p
  obtain ⟨u₂, v₂⟩ := q
  obtain ⟨u₃, v₃⟩ := r
  obtain ⟨u₄, v₄⟩ := PQ
  obtain ⟨u₅, v₅⟩ := QR
  simp only [OnCurve] at hp hq hr
  simp only [add, Prod.mk.injEq] at hPQ hQR d₄ d₅ dL dR ⊢
  have e₄u : u₄ * (1 + d * u₁ * u₂ * v₁ * v₂) = u₁ * v₂ + v₁ * u₂ := by
    rw [← hPQ.1]; exact div_mul_cancel₀ _ d₄.1
  have e₄v : v₄ * (1 - d * u₁ * u₂ * v₁ * v₂) = v₁ * v₂ - a * u₁ * u₂ := by
    rw [← hPQ.2]; exact div_mul_cancel₀ _ d₄.2
  have e₅u : u₅ * (1 + d * u₂ * u₃ * v₂ * v₃) = u₂ * v₃ + v₂ * u₃ := by
    rw [← hQR.1]; exact div_mul_cancel₀ _ d₅.1
  have e₅v : v₅ * (1 - d * u₂ * u₃ * v₂ * v₃) = v₂ * v₃ - a * u₂ * u₃ := by
    rw [← hQR.2]; exact div_mul_cancel₀ _ d₅.2
  have hD := mul_ne_zero (mul_ne_zero (mul_ne_zero d₄.1 d₄.2) d₅.1) d₅.2
  constructor
  · rw [div_eq_div_iff dL.1 dR.1]
    apply mul_left_cancel₀ hD
    linear_combination add_assoc_u_certificate a d u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅ hp hq hr
      (by linear_combination e₄u) (by linear_combination e₄v) (by linear_combination e₅u)
      (by linear_combination e₅v)
  · rw [div_eq_div_iff dL.2 dR.2]
    apply mul_left_cancel₀ hD
    linear_combination add_assoc_v_certificate a d u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅ hp hq hr
      (by linear_combination e₄u) (by linear_combination e₄v) (by linear_combination e₅u)
      (by linear_combination e₅v)

/-! ## Exceptional points

The specification relies on these facts about points with a zero coordinate or of order `2`. -/

/-- The only points with `u = 0` are `(0, 1)` and `(0, -1)`; equivalently, `u = 0` exactly when
`v = ±1`. Zcash Protocol Specification [§A.3.3.3 "ctEdwards ↔ Montgomery
conversion"](https://zips.z.cash/protocol/protocol.pdf#cctconversion), exceptional points
(ctEdwards → Montgomery); `v = ±1` forces `u = 0` because `a ≠ d`. -/
theorem u_eq_zero_iff {a d : F} [Fact (IsComplete a d)] {u v : F} (h : OnCurve a d (u, v)) :
    u = 0 ↔ v = 1 ∨ v = -1 := by
  simp only [OnCurve] at h
  constructor
  · rintro rfl
    have hv : (v - 1) * (v + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hv with h1 | h1
    · exact Or.inl (by linear_combination h1)
    · exact Or.inr (by linear_combination h1)
  · intro hv
    have hv2 : v ^ 2 = 1 := by rcases hv with rfl | rfl <;> ring
    have hu : (a - d) * u ^ 2 = 0 := by linear_combination h + (d * u ^ 2 - 1) * hv2
    exact (pow_eq_zero_iff (by decide)).mp
      ((mul_eq_zero.mp hu).resolve_left (sub_ne_zero.mpr a_ne_d))

/-- The only points of order dividing `2` are `(0, 1)` and `(0, -1)`. Zcash Protocol Specification
[§A.3.3.6 "Affine-ctEdwards nonsmall-order
check"](https://zips.z.cash/protocol/protocol.pdf#cctednonsmallorder) relies on `(0, -1)` being the
unique point of order `2`. A doubled `u` is `2·u·v/(1 + d·u²·v²)`, so `u = 0` or `v = 0`; and
`v = 0` would make the doubled `v` equal `-a·u² = -1`. -/
theorem add_self_eq_zero_iff {a d : F} [h : Fact (IsComplete a d)] {p : F × F}
    (hp : OnCurve a d p) : add a d p p = (0, 1) ↔ p = (0, 1) ∨ p = (0, -1) := by
  have hden := den_ne_zero hp hp
  obtain ⟨u, v⟩ := p
  constructor
  · intro hpp
    simp only [OnCurve, add, Prod.mk.injEq] at hp hden hpp
    obtain ⟨h1, h2⟩ := hpp
    rw [div_eq_zero_iff, or_iff_left hden.1] at h1
    rw [div_eq_one_iff_eq hden.2] at h2
    have huv : u * v = 0 := by
      have h2uv : (2 : F) * (u * v) = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h2uv).resolve_left h.out.F_nonbinary
    rcases mul_eq_zero.mp huv with rfl | rfl
    · have hv : (v - 1) * (v + 1) = 0 := by linear_combination hp
      rcases mul_eq_zero.mp hv with h0 | h0
      · left; simp only [Prod.mk.injEq, true_and]; linear_combination h0
      · right; simp only [Prod.mk.injEq, true_and]; linear_combination h0
    · exact absurd (by linear_combination -hp - h2) h.out.F_nonbinary
  · rintro (h0 | h0) <;> simp only [Prod.mk.injEq] at h0 <;> obtain ⟨rfl, rfl⟩ := h0 <;>
      simp [add]

/-! ## Rich bundled types -/

/-- A complete twisted Edwards curve (§5.4.9.3): coefficients `a` and `d`, bundled with the
completeness conditions (`a` square, `d` non-square, characteristic not `2`) and `a ≠ 0`. No
group-law proof uses `a ≠ 0`; it is part of the specification's definition, and without it the
equation `v²·(1 - d·u²) = 1` is not an elliptic curve. The definition's other conditions,
`d ≠ 0` and `a ≠ d`, follow (`CtEdwardsCurve.d_nonzero`, `a_ne_d`). -/
structure CtEdwardsCurve (F : Type*) [Field F] where
  a : F
  d : F
  a_nonzero : a ≠ 0
  a_square : IsSquare a
  d_nonsquare : ¬ IsSquare d
  F_nonbinary : (2 : F) ≠ 0

/-- `E`'s bundled conditions are the completeness of its addition law, so the raw group laws
(which require `[Fact (IsComplete a d)]`) apply to `E` by instance resolution. -/
instance instIsComplete (E : CtEdwardsCurve F) : Fact (IsComplete E.a E.d) :=
  ⟨⟨E.a_square, E.d_nonsquare, E.F_nonbinary⟩⟩

/-- `d ≠ 0`: `0` is a square and `d` is not. -/
theorem CtEdwardsCurve.d_nonzero (E : CtEdwardsCurve F) : E.d ≠ 0 := fun h =>
  E.d_nonsquare (h ▸ IsSquare.zero)

/-- A point on `E`, correct by construction. The identity `(0, 1)` is on the curve, so no
sentinel is needed. -/
@[ext]
structure CtEdwardsPoint (E : CtEdwardsCurve F) where
  u : F
  v : F
  onCurve : OnCurve E.a E.d (u, v)

namespace CtEdwardsPoint
variable {E : CtEdwardsCurve F}

/-- Two points are equal when their coordinate pairs agree (`onCurve` is a `Prop`). -/
theorem ext_pair {P Q : CtEdwardsPoint E} (h : (P.u, P.v) = (Q.u, Q.v)) : P = Q := by
  obtain ⟨pu, pv, _⟩ := P
  obtain ⟨qu, qv, _⟩ := Q
  injection h with hu hv
  subst hu; subst hv; rfl

/-- Points on `E` are exactly the coordinate pairs on the curve. -/
def equivSubtype (E : CtEdwardsCurve F) :
    CtEdwardsPoint E ≃ { p : F × F // OnCurve E.a E.d p } where
  toFun P := ⟨(P.u, P.v), P.onCurve⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `CtEdwardsPoint E` has decidable equality, through `equivSubtype`. -/
instance instDecidableEq [DecidableEq F] : DecidableEq (CtEdwardsPoint E) :=
  (equivSubtype E).decidableEq

/-- `CtEdwardsPoint E` is computably finite whenever the base field is: the points are a filter
of `F × F` (`equivSubtype`). -/
instance instFintype [DecidableEq F] [Fintype F] : Fintype (CtEdwardsPoint E) :=
  Fintype.ofEquiv _ (equivSubtype E).symm

/-- The identity point `(0, 1)`. -/
def zero (E : CtEdwardsCurve F) : CtEdwardsPoint E := ⟨0, 1, by simp [OnCurve]⟩

/-- Addition lifted to `CtEdwardsPoint E`; closure from `onCurve_add`. -/
def ctedwards_add (P Q : CtEdwardsPoint E) : CtEdwardsPoint E :=
  ⟨(add E.a E.d (P.u, P.v) (Q.u, Q.v)).1, (add E.a E.d (P.u, P.v) (Q.u, Q.v)).2,
   onCurve_add P.onCurve Q.onCurve⟩

/-- Negation lifted to `CtEdwardsPoint E`; closure from `onCurve_neg`. -/
def ctedwards_neg (P : CtEdwardsPoint E) : CtEdwardsPoint E := ⟨-P.u, P.v, onCurve_neg P.onCurve⟩

instance : Zero (CtEdwardsPoint E) := ⟨zero E⟩
instance : Add (CtEdwardsPoint E) := ⟨ctedwards_add⟩
instance : Neg (CtEdwardsPoint E) := ⟨ctedwards_neg⟩

@[simp] theorem zero_u : (0 : CtEdwardsPoint E).u = 0 := rfl
@[simp] theorem zero_v : (0 : CtEdwardsPoint E).v = 1 := rfl
@[simp] theorem neg_u (P : CtEdwardsPoint E) : (-P).u = -P.u := rfl
@[simp] theorem neg_v (P : CtEdwardsPoint E) : (-P).v = P.v := rfl

/-- Addition computes its `u`-coordinate by the raw `add`. -/
theorem add_u (P Q : CtEdwardsPoint E) : (P + Q).u = (add E.a E.d (P.u, P.v) (Q.u, Q.v)).1 := rfl

/-- Addition computes its `v`-coordinate by the raw `add`. -/
theorem add_v (P Q : CtEdwardsPoint E) : (P + Q).v = (add E.a E.d (P.u, P.v) (Q.u, Q.v)).2 := rfl

/-- The abelian group of points on `E`. The group laws are the raw ones, whose `IsComplete`
hypothesis `E` supplies (`instIsComplete`). The scalar action `n • P` is the binary
double-and-add `binNsmul`, so it computes in `O(log n)` steps. -/
instance : AddCommGroup (CtEdwardsPoint E) where
  add := ctedwards_add
  zero := zero E
  neg := ctedwards_neg
  nsmul := binNsmul ctedwards_add (zero E)
  nsmul_zero P := binNsmul_zero _ _ P
  nsmul_succ n P := binNsmul_succ
    (fun P Q R => ext_pair (CtEdwards.add_assoc P.onCurve Q.onCurve R.onCurve))
    (fun P => ext_pair (CtEdwards.add_zero E.a E.d (P.u, P.v))) n P
  zsmul := zsmulRec
  add_assoc P Q R := ext_pair (CtEdwards.add_assoc P.onCurve Q.onCurve R.onCurve)
  zero_add P := ext_pair (CtEdwards.zero_add E.a E.d (P.u, P.v))
  add_zero P := ext_pair (CtEdwards.add_zero E.a E.d (P.u, P.v))
  add_comm P Q := ext_pair (CtEdwards.add_comm E.a E.d (P.u, P.v) (Q.u, Q.v))
  neg_add_cancel P := ext_pair (by
    show add E.a E.d (neg (P.u, P.v)) (P.u, P.v) = (0, 1)
    rw [CtEdwards.add_comm]
    exact add_neg P.onCurve)

/-- The group action `n • P` agrees with the spec-level `smul` on the coordinates. -/
theorem coords_nsmul (n : ℕ) (P : CtEdwardsPoint E) :
    ((n • P).u, (n • P).v) = smul E.a E.d n (P.u, P.v) := by
  induction n with
  | zero => rw [zero_nsmul]; rfl
  | succ k ih =>
    rw [succ_nsmul]
    show add E.a E.d ((k • P).u, (k • P).v) (P.u, P.v) = smul E.a E.d (k + 1) (P.u, P.v)
    rw [ih]; rfl

/-- The only point with `v = 1` is the identity (§A.3.3.3, `u_eq_zero_iff`). -/
theorem eq_zero_of_v_eq_one {P : CtEdwardsPoint E} (h : P.v = 1) : P = 0 :=
  ext_pair (by rw [h, (u_eq_zero_iff P.onCurve).mpr (Or.inl h)]; rfl)

/-- The only points of order dividing `2` are `0` and `(0, -1)` (§A.3.3.6,
`add_self_eq_zero_iff`). -/
theorem two_nsmul_eq_zero_iff {P : CtEdwardsPoint E} :
    2 • P = 0 ↔ P = 0 ∨ (P.u = 0 ∧ P.v = -1) := by
  have hzero : P = 0 ↔ P.u = 0 ∧ P.v = 1 :=
    ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun ⟨hu, hv⟩ => ext_pair (by rw [hu, hv]; rfl)⟩
  have hsum : P + P = 0 ↔ add E.a E.d (P.u, P.v) (P.u, P.v) = (0, 1) :=
    ⟨fun h => congrArg (fun Q : CtEdwardsPoint E => (Q.u, Q.v)) h, fun h => ext_pair h⟩
  rw [two_nsmul, hsum, add_self_eq_zero_iff P.onCurve, hzero]
  simp only [Prod.mk.injEq]

end CtEdwardsPoint

end CompElliptic.CurveForms.CtEdwards
