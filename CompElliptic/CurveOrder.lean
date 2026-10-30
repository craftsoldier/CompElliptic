/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Daira-Emma Hopwood, Gregor Mitscha-Baude
-/
import CompElliptic.CurveForms.ShortWeierstrass
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Pinning a curve group's order without point-counting

For a curve whose group is *known to have prime order* r, fixing the order to exactly r needs
no point-counting algorithm (no Schoof, no proof of a counting algorithm's correctness); the
small-cofactor case `h·r` is the last bullet below. It needs only:

1. a non-identity point P killed by r (so r ∣ #G, since r is prime); and
2. an upper bound on #G that leaves r (rather than some multiple ≥ 2r) as the only possible #G.

This module supplies both layers, and neither assumes any general theorem — in particular not
Hasse's theorem, which Mathlib lacks for `WeierstrassCurve`.

* **Layer 1 — pure finite-group theory.** `card_eq_of_prime_witness` holds for *any* finite
  additive group, with no reference to elliptic curves. A witness of r • P = 0 forces r ∣ #G,
  and #G < 2r then forces #G = r. `card_eq_of_prime_witness_of_lt_three_mul` reaches the same
  conclusion from the weaker #G < 3r, at the price of ruling out 2-torsion (which kills the extra
  candidate 2r by Cauchy's theorem).

* **Layer 2 — the fibre bound.** For a short-Weierstrass curve E over any finite field F, the
  equation y² = x³ + A x + B has at most two roots y for each fixed x; summing over #F choices of
  x and adding 𝒪 gives `#E(F) ≤ 2·#F + 1` (`card_le_two_mul_card_add_one`), with no arithmetic
  geometry. This overshoots the true count by a factor of about two where Hasse overshoots by only
  2√q, but it is unconditional, and it is enough whenever the prime r is close to the field size —
  exactly the situation for a prime-order cryptographic curve. Which of Layer 1's thresholds it
  clears is then decided by the two concrete numbers #F and r.

* **Small cofactors, via the quadratic twist.** A curve of order h·r with a small cofactor h
  has witnesses giving h·r ∣ #E, but the fibre bound can leave 2·h·r open as well. A curve and
  its twist by a non-square have exactly 2·#F + 2 points between them (`card_add_card_twist`,
  again by counting roots for each x). So a twist point not killed by 2·#F + 2 − 2·h·r rules
  out 2·h·r (`card_eq_of_twist_witness`). Once the order is pinned, `card_torsionBy_eq` and
  `eq_torsionBy_of_card_eq` make the r-torsion the unique subgroup of order r.

This is an application of the *Independently re-checkable trust* principle: no general theorem is
assumed, and all that a caller must discharge are closed numeric facts about #F and r, verifiable
by any independent tool.
-/

namespace CompElliptic.CurveOrder

open CompElliptic.CurveForms.ShortWeierstrass

/-! ## Layer 1: pin the order from a prime-order witness (any finite additive group) -/

/-- **The prime-order witness step.** A non-identity `P` killed by a prime `r` has `addOrderOf P`
exactly `r` (`addOrderOf_eq_prime`), so `r ∣ #G` by Lagrange.

This is the half of the argument that uses the witness, and the only half; everything downstream
just rules out the remaining multiples of `r` using an upper bound on `#G`. -/
theorem dvd_natCard_of_prime_witness {G : Type*} [AddGroup G] [Finite G] {r : ℕ}
    (hr : r.Prime) {P : G} (hP : P ≠ 0) (hPr : r • P = 0) : r ∣ Nat.card G := by
  haveI := Fact.mk hr
  exact addOrderOf_eq_prime hPr hP ▸ addOrderOf_dvd_natCard P

/-- If `r` is prime, the finite additive group `G` has a non-identity element `P` killed by `r`
(`r • P = 0`), and `#G < 2r`, then `#G = r`.

The witness gives `r ∣ #G` (`dvd_natCard_of_prime_witness`); with `0 < #G < 2r` the only multiple
of `r` available is `r` itself. -/
theorem card_eq_of_prime_witness {G : Type*} [AddGroup G] [Finite G] {r : ℕ}
    (hr : r.Prime) {P : G} (hP : P ≠ 0) (hPr : r • P = 0)
    (hlt2r : Nat.card G < 2 * r) : Nat.card G = r := by
  have hne0 : Nat.card G ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨P⟩, inferInstance⟩
  exact Nat.eq_of_dvd_of_lt_two_mul hne0 (dvd_natCard_of_prime_witness hr hP hPr) hlt2r

/-- The same conclusion as `card_eq_of_prime_witness` from a weaker bound `#G < 3r`, at the price
of ruling out 2-torsion (`hOdd`).

`#G < 2r` leaves `r` as the only multiple of `r` in range; `#G < 3r` also admits `2r`. That case is
excluded by parity rather than by counting: `#G = 2r` is even, so Cauchy's theorem would supply an
element of order exactly 2, which `hOdd` forbids.

The weaker bound is what an elementary point count affords when the prime sits just below the field
size, so this is the entry point for callers who cannot reach `2r` — but the argument is pure
finite-group theory and mentions no curve. -/
theorem card_eq_of_prime_witness_of_lt_three_mul {G : Type*} [AddGroup G] [Finite G] {r : ℕ}
    (hrPrime : r.Prime) {P : G} (hP : P ≠ 0) (hrP : r • P = 0)
    (hlt3r : Nat.card G < 3 * r) (hOdd : ∀ Q : G, 2 • Q = 0 → Q = 0) : Nat.card G = r := by
  obtain ⟨k, hk⟩ := dvd_natCard_of_prime_witness hrPrime hP hrP
  -- `#G = r * k` with `r * k < 3 * r`, so `k < 3`; `k = 0` contradicts `0 < #G`.
  have hklt3 : k < 3 := by
    refine Nat.lt_of_mul_lt_mul_left (a := r) ?_
    simp_all only [nsmul_zero, ne_eq, mul_comm]
  have hkne0 : k ≠ 0 := by
    rintro rfl
    exact absurd (hk.trans (Nat.mul_zero r)) Nat.card_pos.ne'
  -- `k = 2` would make `#G` even, so Cauchy would give an element of order 2 — excluded by `hOdd`.
  have hkne2 : k ≠ 2 := by
    rintro rfl
    haveI : Fintype G := Fintype.ofFinite _
    have hEven : 2 ∣ Fintype.card G := ⟨r, by rw [← Nat.card_eq_fintype_card, hk]; ring⟩
    obtain ⟨Q, hQ⟩ := exists_prime_addOrderOf_dvd_card 2 hEven
    have hQ0 : Q ≠ 0 := fun h => by simp [h, addOrderOf_zero] at hQ
    exact hQ0 (hOdd Q (hQ ▸ addOrderOf_nsmul_eq_zero Q))
  rw [hk, show k = 1 by omega, Nat.mul_one]

/-! ## The unique subgroup of prime order (finite abelian groups)

When `#G = h·r` with `r` prime and `r ∤ h`, the `r`-torsion subgroup `G[r]` has exactly `r`
elements and is the only subgroup of order `r`: for a curve, the prime-order subgroup is unique
once the order is pinned. -/

/-- If `#G = h·r` with `r` prime and `r ∤ h`, the `r`-torsion subgroup `G[r]` has exactly `r`
elements. -/
theorem card_torsionBy_eq {G : Type*} [AddCommGroup G] [Finite G] {r h : ℕ} (hr : r.Prime)
    (hcard : Nat.card G = h * r) (hh : ¬ r ∣ h) :
    Nat.card (AddSubgroup.torsionBy G (r : ℤ)) = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  set H := AddSubgroup.torsionBy G (r : ℤ)
  -- By Cauchy, `G` has an element of order `r`; it lies in `H`, so `r ∣ #H`.
  obtain ⟨P, hP⟩ := exists_prime_addOrderOf_dvd_card' r (hcard ▸ dvd_mul_left r h)
  have hPr : r • P = 0 := hP ▸ addOrderOf_nsmul_eq_zero P
  have hP0 : (⟨P, AddSubgroup.torsionBy.nsmul_iff.mpr hPr⟩ : H) ≠ 0 := fun h0 => by
    have : P = 0 := congrArg Subtype.val h0
    rw [this, addOrderOf_zero] at hP
    exact hr.one_lt.ne hP
  obtain ⟨m, hm⟩ := dvd_natCard_of_prime_witness hr hP0 (Subtype.ext hPr)
  have hHG : Nat.card H ∣ h * r := hcard ▸ AddSubgroup.card_addSubgroup_dvd_card H
  -- `m = 1`: by Cauchy, a prime `p ∣ m` is the order of some element of `H`, so `p = r`; then
  -- `r² ∣ #H ∣ h·r`, contradicting `r ∤ h`.
  have hm1 : m = 1 := by
    by_contra hne
    have hm0 : m ≠ 0 := by
      rintro rfl
      have : Nat.card H ≠ 0 := Nat.card_pos.ne'
      simp_all
    obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hne
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hy⟩ := exists_prime_addOrderOf_dvd_card' p (hm ▸ Dvd.dvd.mul_left hpm r)
    have hpr : p ∣ r := hy ▸ addOrderOf_dvd_of_nsmul_eq_zero
      (Subtype.ext (AddSubgroup.torsionBy.nsmul_iff.mp y.2))
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hp hr).mp hpr
    have : p * p ∣ h * p := (hm ▸ Nat.mul_dvd_mul_left p hpm).trans hHG
    exact hh (Nat.dvd_of_mul_dvd_mul_right hp.pos (by simpa [mul_comm] using this))
  rw [hm, hm1, mul_one]

/-- Under the hypotheses of `card_torsionBy_eq`, every subgroup of order `r` is the `r`-torsion
subgroup: its elements are killed by its order `r`, and the two have the same size. -/
theorem eq_torsionBy_of_card_eq {G : Type*} [AddCommGroup G] [Finite G] {r h : ℕ}
    (hr : r.Prime) (hcard : Nat.card G = h * r) (hh : ¬ r ∣ h) (K : AddSubgroup G)
    (hK : Nat.card K = r) : K = AddSubgroup.torsionBy G (r : ℤ) := by
  have hle : K ≤ AddSubgroup.torsionBy G (r : ℤ) := fun y hy => by
    have : Nat.card K • (⟨y, hy⟩ : K) = 0 := card_nsmul_eq_zero'
    rw [hK] at this
    exact AddSubgroup.torsionBy.nsmul_iff.mpr (congrArg Subtype.val this)
  exact AddSubgroup.eq_of_le_of_card_ge hle (by rw [card_torsionBy_eq hr hcard hh, hK])

/-! ## Layer 2: the fibre bound `#E(F) ≤ 2 · #F + 1` -/

variable {F : Type*} [Field F] [DecidableEq F]

/-- **At most two points share an x-coordinate.** Two on-curve points sharing an `x` have
`y² = x³ + A x + B` for the *same* right-hand side, so `(y₁ − y₂)(y₁ + y₂) = 0` and hence
`y₁ = y₂ ∨ y₁ = −y₂` — the short-Weierstrass form of `WeierstrassCurve.Affine.Y_eq_of_X_eq`.
The fibre for any point is therefore contained in the two-element set `{(x, y), (x, −y)}`. -/
theorem card_fibre_le_two [Fintype F] (E : SWCurve F) (x : F) :
    ((Finset.univ.filter fun R : F × F => OnCurve E.A E.B R).filter
      fun R => R.1 = x).card ≤ 2 := by
  rcases ((Finset.univ.filter fun R : F × F => OnCurve E.A E.B R).filter
      fun R => R.1 = x).eq_empty_or_nonempty with hR | ⟨P, hP⟩
  · simp [hR]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hP
    obtain ⟨hPOnCurve, hxP⟩ := hP
    refine le_trans (Finset.card_le_card ?_) ((Finset.card_insert_le P {(x, -P.2)}).trans (by simp))
    intro Q hQ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hQ
    obtain ⟨hQOnCurve, hxQ⟩ := hQ
    have hsq : Q.2 ^ 2 = P.2 ^ 2 := by
      simp only [OnCurve] at hPOnCurve hQOnCurve
      rw [hPOnCurve, hQOnCurve, hxP, hxQ]
    have hfac : (Q.2 - P.2) * (Q.2 + P.2) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h | h
    · exact Finset.mem_insert.mpr (Or.inl (Prod.ext (hxQ.trans hxP.symm) (sub_eq_zero.mp h)))
    · exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr (Prod.ext hxQ (eq_neg_of_add_eq_zero_left h))))

/-- **The unconditional cardinality bound**: at most two points per `x`-coordinate
(`card_fibre_le_two`) over `#F` choices of `x`, plus the identity `𝒪`.

This is elementary and holds for every short-Weierstrass curve over every finite field; it is
looser than Hasse (which Mathlib lacks) but needs no algebraic geometry. -/
theorem card_le_two_mul_card_add_one [Fintype F] (E : SWCurve F) :
    Nat.card (SWPoint E) ≤ 2 * Fintype.card F + 1 := by
  rw [Nat.card_congr (SWPoint.equivSubtype E), Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : (Finset.univ.filter fun R : F × F => Valid E.A E.B R) ⊆
      (Finset.univ.filter fun R : F × F => OnCurve E.A E.B R) ∪ {((0 : F), (0 : F))} := by
    intro R hR
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Finset.mem_singleton] at hR ⊢
    exact hR
  calc (Finset.univ.filter fun R : F × F => Valid E.A E.B R).card
      ≤ ((Finset.univ.filter fun R : F × F => OnCurve E.A E.B R) ∪ {0}).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter fun R : F × F => OnCurve E.A E.B R).card + 1 :=
        le_trans (Finset.card_union_le _ _) (by simp)
    _ ≤ 2 * Fintype.card F + 1 := by
        have h := Finset.card_le_mul_card_image_of_maps_to
          (f := Prod.fst) (t := (Finset.univ : Finset F))
          (fun _ _ => Finset.mem_univ _) 2 (fun x _ => card_fibre_le_two E x)
        rw [Finset.card_univ] at h
        omega

/-- The points of `E` are its affine points and `𝒪`, which is off the curve
(`not_onCurve_zero`). -/
theorem card_eq_card_onCurve_add_one [Fintype F] (E : SWCurve F) :
    Nat.card (SWPoint E) = (Finset.univ.filter fun R : F × F => OnCurve E.A E.B R).card + 1 := by
  rw [Nat.card_congr (SWPoint.equivSubtype E), Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsplit : (Finset.univ.filter fun R : F × F => Valid E.A E.B R) =
      (Finset.univ.filter fun R : F × F => OnCurve E.A E.B R) ∪ {((0 : F), (0 : F))} := by
    ext R; simp [Valid, or_comm]
  have hdisj : Disjoint (Finset.univ.filter fun R : F × F => OnCurve E.A E.B R)
      {((0 : F), (0 : F))} := by
    rw [Finset.disjoint_singleton_right]
    simpa using not_onCurve_zero E.B_nonzero
  rw [hsplit, Finset.card_union_of_disjoint hdisj, Finset.card_singleton]

/-- For a non-square `c`, the equations `y² = t` and `y² = c³·t` have exactly two solutions `y`
between them. Each has `1 + χ(·)` solutions for the quadratic character `χ`, and
`χ(c³·t) = -χ(t)`. -/
private theorem card_sqrts_add_card_sqrts [Fintype F] (h2 : (2 : F) ≠ 0) {c : F}
    (hc : ¬ IsSquare c) (t : F) :
    (Finset.univ.filter fun y : F => y^2 = t).card +
      (Finset.univ.filter fun y : F => y^2 = c^3 * t).card = 2 := by
  have hF : ringChar F ≠ 2 := fun hchar =>
    h2 (by simpa [hchar] using ringChar.Nat.cast_ringChar (R := F))
  have hs₁ := quadraticChar_card_sqrts hF t
  have hs₂ := quadraticChar_card_sqrts hF (c^3 * t)
  have hχc : quadraticChar F c = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hc
  rw [map_mul, map_pow, hχc] at hs₂
  simp only [Set.toFinset_setOf] at hs₁ hs₂
  have : (((Finset.univ.filter fun y : F => y^2 = t).card +
      (Finset.univ.filter fun y : F => y^2 = c^3 * t).card : ℕ) : ℤ) = 2 := by
    push_cast; rw [hs₁, hs₂]; ring
  exact_mod_cast this

/-- **The twist identity.** A curve `E` and its quadratic twist `E'` by a non-square `c`
(`A' = c²·A`, `B' = c³·B`) have exactly `2·#F + 2` points between them. -/
theorem card_add_card_twist [Fintype F] (h2 : (2 : F) ≠ 0) (E E' : SWCurve F) {c : F}
    (hc : ¬ IsSquare c) (hA : E'.A = c^2 * E.A) (hB : E'.B = c^3 * E.B) :
    Nat.card (SWPoint E) + Nat.card (SWPoint E') = 2 * Fintype.card F + 2 := by
  have hc0 : c ≠ 0 := fun h => hc (h ▸ IsSquare.zero)
  -- Count the affine points fibre by fibre over `x`.
  have hfib : ∀ A B : F, (Finset.univ.filter fun R : F × F => OnCurve A B R).card =
      ∑ x : F, (Finset.univ.filter fun y : F => y^2 = x^3 + A * x + B).card := by
    intro A B
    simp only [Finset.card_filter, Fintype.sum_prod_type, OnCurve]
  rw [card_eq_card_onCurve_add_one, card_eq_card_onCurve_add_one, hfib, hfib, hA, hB]
  -- Reindex the twist's sum by `X = c·x`.
  have htw : ∑ X : F, (Finset.univ.filter fun y : F => y^2 = X^3 + c^2 * E.A * X + c^3 * E.B).card =
      ∑ x : F, (Finset.univ.filter fun y : F => y^2 = c^3 * (x^3 + E.A * x + E.B)).card := by
    refine (Fintype.sum_equiv (Equiv.mulLeft₀ c hc0) _ _ fun x => ?_).symm
    simp only [Equiv.mulLeft₀_apply]
    congr 2; ext y; ring_nf
  rw [htw]
  -- For each `x`, the two fibres have two points between them (`card_sqrts_add_card_sqrts`);
  -- adding the two identities `𝒪` gives `2·#F + 2`.
  have hsum : ∑ x : F, (Finset.univ.filter fun y : F => y^2 = x^3 + E.A * x + E.B).card +
      ∑ x : F, (Finset.univ.filter fun y : F => y^2 = c^3 * (x^3 + E.A * x + E.B)).card =
      2 * Fintype.card F := by
    rw [← Finset.sum_add_distrib]
    simp only [card_sqrts_add_card_sqrts h2 hc, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  omega

/-! ## Order pinning from the fibre bound

Both results below feed `card_le_two_mul_card_add_one` into Layer 1, replacing its `#G < 2r` (resp.
`#G < 3r`) premiss by a closed numeric comparison between `#F` and `r`. -/

/-- **Order of a prime-order curve group whose prime exceeds the field size.** If the prime `r`
kills the non-identity point `P` and `2 · #F + 1 < 2r`, the curve group has exactly `r` points.

The Layer 1 core `card_eq_of_prime_witness`, with the upper bound supplied by
`card_le_two_mul_card_add_one`. -/
theorem card_eq_of_prime_witness_of_card_lt_two_mul [Fintype F] (E : SWCurve F) {r : ℕ}
    (hrPrime : r.Prime) {P : SWPoint E} (hP : P ≠ 0) (hPr : r • P = 0)
    (hBound : 2 * Fintype.card F + 1 < 2 * r) :
    Nat.card (SWPoint E) = r :=
  card_eq_of_prime_witness hrPrime hP hPr
    (lt_of_le_of_lt (card_le_two_mul_card_add_one E) hBound)

/-- No 2-torsion on a curve, in odd characteristic, no point of which has `y = 0`.

A point with `2 • Q = 0` satisfies `Q = -Q`, hence `Q.y = -Q.y` and so `2 · Q.y = 0`; with
`2 ≠ 0` that forces `Q.y = 0`. An on-curve point cannot then exist by hypothesis, leaving
only the sentinel `𝒪`. This discharges the `hOdd` side condition of
`card_eq_of_prime_witness_of_card_lt_three_mul`. -/
theorem eq_zero_of_two_nsmul_eq_zero {E : SWCurve F} (h2ne0 : (2 : F) ≠ 0)
    (hy : ∀ x : F, ¬ OnCurve E.A E.B (x, 0)) {Q : SWPoint E} (hQ : 2 • Q = 0) : Q = 0 := by
  rw [two_nsmul] at hQ
  have hNeg : Q = -Q := eq_neg_of_add_eq_zero_left hQ
  have hyy : Q.y = -Q.y := by rw [← SWPoint.neg_y Q, ← hNeg]
  have hQy : Q.y = 0 := by
    have h2y : 2 * Q.y = 0 := by linear_combination hyy
    exact (mul_eq_zero.mp h2y).resolve_left h2ne0
  rcases Q.onCurve with hc | h0
  · rw [hQy] at hc
    exact absurd hc (hy Q.x)
  · exact SWPoint.ext_pair h0

/-- **Order of a prime-order curve group whose prime is below the field size.** There the fibre
bound only yields `#E(F) < 3r`, admitting `#E(F) = 2r` alongside `#E(F) = r`. Given additionally
that the group has no 2-torsion, `2r` is impossible, and `#E(F) = r`.

The curve-free half is Layer 1's `card_eq_of_prime_witness_of_lt_three_mul`; all this adds is the
fibre bound, so that the caller supplies a comparison between `#F` and `r` rather than one against
`#E(F)`. Use `eq_zero_of_two_nsmul_eq_zero` to supply `hOdd` from the absence of curve points with
`y = 0`. -/
theorem card_eq_of_prime_witness_of_card_lt_three_mul [Fintype F] (E : SWCurve F) {r : ℕ}
    (hrPrime : r.Prime) {P : SWPoint E} (hP : P ≠ 0) (hPr : r • P = 0)
    (hBound : 2 * Fintype.card F + 1 < 3 * r)
    (hOdd : ∀ Q : SWPoint E, 2 • Q = 0 → Q = 0) :
    Nat.card (SWPoint E) = r :=
  card_eq_of_prime_witness_of_lt_three_mul hrPrime hP hPr
    (lt_of_le_of_lt (card_le_two_mul_card_add_one E) hBound) hOdd

/-- **Order from a twist witness.** If `m ∣ #E(F)`, the fibre bound leaves only `m` and `2m`
(`2·#F + 1 < 3m`), and some point `W` of a twist `E'` of `E` has `[2·#F + 2 − 2m] W ≠ 𝒪`, then
`#E(F) = m`.

`#E(F) = 2m` would make `#E'(F) = 2·#F + 2 − 2m` by `card_add_card_twist`, and the group order
kills every point of `E'`. This is the small-cofactor route: `m = h·r`, with `h·r ∣ #E(F)` from
witnesses of orders `h` and `r`. -/
theorem card_eq_of_twist_witness [Fintype F] (h2 : (2 : F) ≠ 0) (E E' : SWCurve F) {c : F}
    (hc : ¬ IsSquare c) (hA : E'.A = c^2 * E.A) (hB : E'.B = c^3 * E.B) {m : ℕ}
    (hm : m ∣ Nat.card (SWPoint E)) (hBound : 2 * Fintype.card F + 1 < 3 * m)
    {W : SWPoint E'} (hW : (2 * Fintype.card F + 2 - 2 * m) • W ≠ 0) :
    Nat.card (SWPoint E) = m := by
  obtain ⟨k, hk⟩ := hm
  have hle := card_le_two_mul_card_add_one E
  have hpos : 0 < Nat.card (SWPoint E) := Nat.card_pos
  have htw := card_add_card_twist h2 E E' hc hA hB
  rcases k with _ | _ | _ | k
  · rw [Nat.mul_zero] at hk; omega
  · simpa using hk
  · exfalso
    have hcard : Nat.card (SWPoint E') = 2 * Fintype.card F + 2 - 2 * m := by omega
    exact hW (hcard ▸ card_nsmul_eq_zero')
  · exfalso
    rw [show m * (k + 1 + 1 + 1) = m * k + 3 * m by ring] at hk
    omega

end CompElliptic.CurveOrder
