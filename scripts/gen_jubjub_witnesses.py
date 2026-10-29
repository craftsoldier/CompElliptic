#!/usr/bin/env python3
# Copyright (c) 2026 CompElliptic Contributors.
# Released under the Apache License, Version 2.0, or the MIT license, at your option,
# as described in the files LICENSE-APACHE and LICENSE-MIT.
# Authors: Julian Abraham
"""
Generate `CompElliptic/Curves/JubjubWitnesses.lean`: the three points whose orders pin the order of
the Jubjub curve group (`Curves/JubjubOrder.lean`), with each scalar multiplication given as a
double-and-add chain of slopes that `runChain` checks.

- `Gpt`: the point at the smallest square abscissa, x = 1; it has order r_J;
- `Tpt`: the point of order 8 with the smaller abscissa;
- `Wpt`: the point of the twist by 7 at the smallest square abscissa, x = 0, with
  [2q + 2 - 16 r_J] Wpt != O.

Each y is the root in [0, (q - 1)/2]. A chain is left-to-right double-and-add; the script asserts
that no step is a special case of the group law (an addition with equal abscissas, or a doubling
at y = 0), which `runChain` would reject.

Usage: run from the project root and write the result to the witness file:

    python3 scripts/gen_jubjub_witnesses.py > CompElliptic/Curves/JubjubWitnesses.lean
"""

# Zcash protocol spec §5.4.9.2 (r_S, the base field) and §5.4.9.3 (r_J, a, d).
Q = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
R_J = 0x0e7db4ea6533afa906673b0101343b00a6682093ccc81082d0970e5ed6f72cb7

inv = lambda x: pow(x, Q - 2, Q)
A_ED, D_ED = Q - 1, -10240 * inv(10241) % Q
# The Montgomery curve of §A.2 (B = 1) and its short-Weierstrass translation x ↦ x + A/3.
A_M = 40962
assert A_M == 2 * (A_ED + D_ED) * inv(A_ED - D_ED) % Q
A4 = (3 - A_M * A_M) * inv(3) % Q
A6 = (2 * A_M ** 3 - 9 * A_M) * inv(27) % Q
assert A4 == -559295147 % Q and A6 == 5091077286874
C = 7  # the twist: A' = C² A4, B' = C³ A6
assert pow(C, (Q - 1) // 2, Q) == Q - 1
TA4, TA6 = C * C * A4 % Q, C ** 3 * A6 % Q


def sqrt(x):
    """A square root of x mod Q (Tonelli–Shanks with the non-residue C), or None."""
    x %= Q
    if x == 0:
        return 0
    if pow(x, (Q - 1) // 2, Q) != 1:
        return None
    s, t = 0, Q - 1
    while t % 2 == 0:
        s, t = s + 1, t // 2
    m, c, tt, rr = s, pow(C, t, Q), pow(x, t, Q), pow(x, (t + 1) // 2, Q)
    while tt != 1:
        i, t2 = 0, tt
        while t2 != 1:
            t2, i = t2 * t2 % Q, i + 1
        b = pow(c, 1 << (m - i - 1), Q)
        m, c, tt, rr = i, b * b % Q, tt * b * b % Q, rr * b % Q
    return rr


def add(P, R, a):
    """The group law on y² = x³ + a x + b, with None for the identity."""
    if P is None:
        return R
    if R is None:
        return P
    (x1, y1), (x2, y2) = P, R
    if x1 == x2 and (y1 + y2) % Q == 0:
        return None
    if P == R:
        lam = (3 * x1 * x1 + a) * inv(2 * y1) % Q
    else:
        lam = (y2 - y1) * inv(x2 - x1) % Q
    x3 = (lam * lam - x1 - x2) % Q
    return (x3, (lam * (x1 - x3) - y1) % Q)


def mul(n, P, a):
    R = None
    while n:
        if n & 1:
            R = add(R, P, a)
        P = add(P, P, a)
        n >>= 1
    return R


def points_by_abscissa(a, b):
    """The points with y ≠ 0, by increasing abscissa, y in [0, (q - 1)/2]."""
    x = 0
    while True:
        y = sqrt(x ** 3 + a * x + b)
        if y is not None and y != 0:
            yield (x, min(y, Q - y))
        x += 1


def chain(base, a, target):
    """The slopes of the left-to-right double-and-add chain from `base` to `[target] base`, as
    `ChainStep` literals, and the point reached."""
    steps, P = [], base
    for bit in bin(target)[3:]:
        assert P[1] != 0, "doubling at y = 0"
        steps.append(f".double {(3 * P[0] * P[0] + a) * inv(2 * P[1]) % Q}")
        P = add(P, P, a)
        if bit == "1":
            assert P[0] != base[0], "addition with equal abscissas"
            steps.append(f".addBase {(base[1] - P[1]) * inv(base[0] - P[0]) % Q}")
            P = add(P, base, a)
    assert P == mul(target, base, a)
    return steps, P


HEADER = """\
/-
Copyright (c) 2026 CompElliptic Contributors.
Released under the Apache License, Version 2.0, or the MIT license, at your option,
as described in the files LICENSE-APACHE and LICENSE-MIT.
Authors: Julian Abraham
-/
import CompElliptic.Curves.Jubjub
import CompElliptic.Fields.Jubjub

/-!
# Order witnesses for the Jubjub curve

Three points of `Jubjub.curve` and its `twist`, with the scalar multiples that pin the order of
the curve group in `Curves/JubjubOrder.lean`. Here `q` is the size of the base field, and `r_𝕁` is
`JUBJUB_SCALAR_CARD`, the prime written `ℓ` in `Fields/Jubjub.lean`.

* `Gpt`, at the smallest square abscissa `x = 1`: `[r_𝕁] Gpt = 𝒪`;
* `Tpt`, the point of order `8` with the smaller abscissa: `[4] Tpt ≠ 𝒪` and `[8] Tpt = 𝒪`;
* `Wpt`, on `twist` at the smallest square abscissa `x = 0`: `[2·q + 2 - 16·r_𝕁] Wpt ≠ 𝒪`.

Each `y` is the root in `[0, (q - 1)/2]`. Each multiple is a double-and-add chain of slopes,
checked by one evaluation of `runChain` and turned into the multiple by
`SWPoint.runChain_sound`. The evaluations use `decide +kernel`: plain `decide` first evaluates
the instance in the elaborator, which exceeds its recursion depth on chains this long, and the
kernel checks the same proof either way. A wrong slope still fails, but Lean may report it as a
pretty-printing error; regenerate the file rather than editing it.

This file is generated by `scripts/gen_jubjub_witnesses.py`.
-/

namespace CompElliptic.Curves.Jubjub

open CompElliptic.CurveForms.ShortWeierstrass CompElliptic.Fields.BLS12_381
  CompElliptic.Fields.Jubjub
"""


def point(name, curve, P, doc):
    return (f"/-- {doc} -/\ndef {name} : SWPoint {curve} :=\n  ⟨{P[0]},\n"
            f"    {P[1]},\n    Or.inl (by decide)⟩\n\n"
            f"theorem {name}_ne_zero : {name} ≠ 0 := by decide\n")


def chain_def(name, steps, doc):
    return (f"/-- {doc} -/\ndef {name} : List (ChainStep BLS12381ScalarField) := [\n  "
            + ",\n  ".join(steps) + "]\n")


if __name__ == "__main__":
    G = next(P for P in points_by_abscissa(A4, A6) if mul(R_J, P, A4) is None)
    assert G[0] == 1 and sqrt(A6) is None  # x = 0 is not on the curve
    # Only four points have order 8, so search the r_J-multiples instead: as #E = 8 r_J, [r_J] P
    # has order 8 for the first P with [4 r_J] P != O, and the order-8 points are its odd multiples.
    T8 = mul(R_J, next(P for P in points_by_abscissa(A4, A6)
                       if mul(4 * R_J, P, A4) is not None), A4)
    T = min(mul(k, T8, A4) for k in (1, 3, 5, 7))
    assert mul(8, T, A4) is None and mul(4, T, A4) is not None and T[1] <= (Q - 1) // 2
    N_W = 2 * Q + 2 - 16 * R_J
    W = next(P for P in points_by_abscissa(TA4, TA6) if mul(N_W, P, TA4) is not None)
    assert W[0] == 0

    g_steps, g_end = chain(G, A4, R_J - 1)
    assert g_end == (G[0], -G[1] % Q)
    t_steps, t_end = chain(T, A4, 4)
    assert t_end == (13654, 0)
    w_steps, w_end = chain(W, TA4, N_W)

    out = [HEADER]
    out.append(point("Gpt", "curve", G, "The point at the smallest square abscissa `x = 1`."))
    out.append(point("Tpt", "curve", T, "The point of order `8` with the smaller abscissa."))
    out.append(point("Wpt", "twist", W,
                     "The point of `twist` at the smallest square abscissa `x = 0`."))
    out.append(chain_def("gptChain", g_steps,
                         "The slopes of the chain from `Gpt` to `[r_𝕁 - 1] Gpt = -Gpt`."))
    out.append(chain_def("tptChain", t_steps,
                         "The slopes of the chain from `Tpt` to `[4] Tpt = (13654, 0)`."))
    out.append(chain_def("wptChain", w_steps,
                         "The slopes of the chain from `Wpt` to `[2·q + 2 - 16·r_𝕁] Wpt`."))
    out.append(f"""/-- `[r_𝕁] Gpt = 𝒪`: the chain reaches `[r_𝕁 - 1] Gpt = -Gpt`. -/
theorem r_nsmul_Gpt : JUBJUB_SCALAR_CARD • Gpt = 0 := by
  have hrun : runChain curve.A (Gpt.x, Gpt.y) (Gpt.x, Gpt.y) gptChain = some (Gpt.x, -Gpt.y) := by
    decide +kernel
  obtain ⟨P, hP, hPxy⟩ := SWPoint.runChain_sound Gpt_ne_zero gptChain (one_nsmul Gpt) hrun
  rw [show chainScalar gptChain 1 = JUBJUB_SCALAR_CARD - 1 by decide +kernel] at hP
  rw [show JUBJUB_SCALAR_CARD = (JUBJUB_SCALAR_CARD - 1) + 1 by decide, add_nsmul, one_nsmul, hP,
    show P = -Gpt from SWPoint.ext_pair hPxy, neg_add_cancel]

/-- `[4] Tpt = (13654, 0)`, the image of `𝕄`'s point `(0, 0)`. -/
theorem four_nsmul_Tpt : ∃ P : SWPoint curve, 4 • Tpt = P ∧ (P.x, P.y) = (13654, 0) := by
  have hrun : runChain curve.A (Tpt.x, Tpt.y) (Tpt.x, Tpt.y) tptChain = some (13654, 0) := by
    decide +kernel
  obtain ⟨P, hP, hPxy⟩ := SWPoint.runChain_sound Tpt_ne_zero tptChain (one_nsmul Tpt) hrun
  exact ⟨P, by rwa [show chainScalar tptChain 1 = 4 by decide +kernel] at hP, hPxy⟩

/-- `[4] Tpt ≠ 𝒪`: it is `(13654, 0)`, and `𝒪` is `(0, 0)`. -/
theorem four_nsmul_Tpt_ne_zero : 4 • Tpt ≠ 0 := by
  obtain ⟨P, hP, hPxy⟩ := four_nsmul_Tpt
  rw [hP]
  intro h
  rw [h] at hPxy
  exact absurd hPxy (by decide)

/-- `[8] Tpt = 𝒪`: `[4] Tpt` has `y = 0`, so it is its own negative. -/
theorem eight_nsmul_Tpt : 8 • Tpt = 0 := by
  obtain ⟨P, hP, hPxy⟩ := four_nsmul_Tpt
  have hneg : P = -P := SWPoint.ext_pair (by
    rw [SWPoint.neg_x, SWPoint.neg_y, show P.y = 0 from congrArg Prod.snd hPxy, neg_zero])
  rw [show (8 : ℕ) = 4 + 4 by norm_num, add_nsmul, hP]
  nth_rewrite 2 [hneg]
  exact add_neg_cancel _

/-- `[2·q + 2 - 16·r_𝕁] Wpt ≠ 𝒪`: the chain ends at a point other than `(0, 0)`. -/
theorem Wpt_witness :
    (2 * BLS12_381_SCALAR_CARD + 2 - 2 * (8 * JUBJUB_SCALAR_CARD)) • Wpt ≠ 0 := by
  have hrun : runChain twist.A (Wpt.x, Wpt.y) (Wpt.x, Wpt.y) wptChain =
      some ({w_end[0]},
        {w_end[1]}) := by
    decide +kernel
  obtain ⟨P, hP, hPxy⟩ := SWPoint.runChain_sound Wpt_ne_zero wptChain (one_nsmul Wpt) hrun
  rw [show 2 * BLS12_381_SCALAR_CARD + 2 - 2 * (8 * JUBJUB_SCALAR_CARD) =
    chainScalar wptChain 1 by decide +kernel, hP]
  intro h
  rw [h] at hPxy
  exact absurd hPxy (by decide)

end CompElliptic.Curves.Jubjub""")
    print("\n".join(out))
