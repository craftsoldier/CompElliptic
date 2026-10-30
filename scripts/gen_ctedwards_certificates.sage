# Regenerates the generated section of CompElliptic/CurveForms/CtEdwardsCertificates.lean:
# everything below the marker line. The hand-written module doc above the marker is left
# untouched. See that module's doc-comment for the vocabulary (certificate, cofactor, atom);
# this script is the single source for the theorem statements and proofs.
#
# Method, per coordinate of the associativity identity:
#   1. Name the two inner sums by atoms (u₄, v₄ for P₁ + P₂; u₅, v₅ for P₂ + P₃), each tied to
#      its inputs by `atom·D = N`, and multiply the cross-multiplied goal by the four inner
#      denominators, so that no division remains.
#   2. Eliminate the atoms by exact substitution: each atom occurs to the first power, beside its
#      own denominator, so `B·x = (B/D)·(x·D − N) + (B/D)·N` with `D ∣ B`.
#   3. Obtain the cofactors of the atom-free remainder with Singular's `lift` over the three
#      curve equations.
#   4. Assert the emitted identity by exact polynomial expansion. No Gröbner output is trusted:
#      a wrong cofactor fails this assert, and Lean's `ring` re-checks the same identity on build.
#   5. Emit with a fixed layout, wrapped to 96 columns.
import re
import textwrap


def lw(poly, indent):
    s_ = str(poly)
    body = textwrap.wrap(s_, width=96 - indent, break_long_words=False,
                         break_on_hyphens=False)
    return ("\n" + " " * indent).join(body)


R = PolynomialRing(QQ, ["a", "d", "u1", "v1", "u2", "v2", "u3", "v3", "u4", "v4",
                        "u5", "v5"], order="degrevlex")
a, d, u1, v1, u2, v2, u3, v3, u4, v4, u5, v5 = R.gens()

curve = lambda u, v: a*u^2 + v^2 - 1 - d*u^2*v^2
Du = lambda p, q: 1 + d*p[0]*q[0]*p[1]*q[1]
Dv = lambda p, q: 1 - d*p[0]*q[0]*p[1]*q[1]
Nu = lambda p, q: p[0]*q[1] + p[1]*q[0]
Nv = lambda p, q: p[1]*q[1] - a*p[0]*q[0]
P1, P2, P3, P4, P5 = (u1, v1), (u2, v2), (u3, v3), (u4, v4), (u5, v5)


def certify(goal, curves, atoms):
    """Cofactors for `goal` over `curves + [x*D - N for (x, D, N) in atoms]` (steps 2-4)."""
    T = goal
    acof = []
    for x, D, N in atoms:
        assert T.degree(x) <= 1, x
        q, r = T.coefficient({x: 1}).quo_rem(D)
        assert r == 0, x
        acof.append(q)
        T = T - q * (x*D - N)
        assert T.degree(x) == 0, x
    ccof = T.lift(R.ideal(curves))
    hyps = curves + [x*D - N for x, D, N in atoms]
    cof = list(ccof) + acof
    assert sum(c*h for c, h in zip(cof, hyps)) == goal
    return cof


# (P₁ + P₂) + P₃ and P₁ + (P₂ + P₃), with P₄ = P₁ + P₂ and P₅ = P₂ + P₃.
curves = [curve(*P1), curve(*P2), curve(*P3)]
atoms = [(u4, Du(P1, P2), Nu(P1, P2)), (v4, Dv(P1, P2), Nv(P1, P2)),
         (u5, Du(P2, P3), Nu(P2, P3)), (v5, Dv(P2, P3), Nv(P2, P3))]
Dall = Du(P1, P2) * Dv(P1, P2) * Du(P2, P3) * Dv(P2, P3)
goal_u = Dall * (Nu(P4, P3)*Du(P1, P5) - Nu(P1, P5)*Du(P4, P3))
goal_v = Dall * (Nv(P4, P3)*Dv(P1, P5) - Nv(P1, P5)*Dv(P4, P3))
cof_u = certify(goal_u, curves, atoms)
cof_v = certify(goal_v, curves, atoms)
for nm, g, c in [("u", goal_u, cof_u), ("v", goal_v, cof_v)]:
    print(nm, "sizes: goal", len(g.monomials()), "cofs", [len(x.monomials()) for x in c])

curve_hyp = "    (h{i} : a*u{i}^2 + v{i}^2 = 1 + d*u{i}^2*v{i}^2)"
atom_hyp = "    (e{n} : {atom} * ({D}) = {N})"
names = ["h1", "h2", "h3", "e4u", "e4v", "e5u", "e5v"]


def combo(cofs):
    return "\n      + ".join(lw("({}) * {}".format(c, n), 8)
                             for c, n in zip(cofs, names) if c != 0)


def ah(n, atom, D, N):
    return atom_hyp.format(n=n, atom=atom, D=lw(D, 10), N=lw(N, 10))


tmpl = """\
/-- Associativity, `{c}`-coordinate. With `u₄`, `v₄` the coordinates of `P₁ + P₂` (`e₄u`, `e₄v`)
and `u₅`, `v₅` those of `P₂ + P₃` (`e₅u`, `e₅v`), the cross-multiplied `{c}`-coordinates of
`(P₁ + P₂) + P₃` and `P₁ + (P₂ + P₃)` agree, multiplied through by the four inner denominators. -/
theorem add_assoc_{c}_certificate {{F : Type*}} [CommRing F]
    (a d u1 v1 u2 v2 u3 v3 u4 v4 u5 v5 : F)
{h1}
{h2}
{h3}
{e4u}
{e4v}
{e5u}
{e5v} :
    ({goal}) = 0 :=
  by
    linear_combination
      {combo}"""
hyps = dict(h1=curve_hyp.format(i=1), h2=curve_hyp.format(i=2), h3=curve_hyp.format(i=3),
            e4u=ah("4u", "u4", Du(P1, P2), Nu(P1, P2)),
            e4v=ah("4v", "v4", Dv(P1, P2), Nv(P1, P2)),
            e5u=ah("5u", "u5", Du(P2, P3), Nu(P2, P3)),
            e5v=ah("5v", "v5", Dv(P2, P3), Nv(P2, P3)))
text = (tmpl.format(c="u", goal=lw(goal_u, 6), combo=combo(cof_u), **hyps) + "\n\n"
        + tmpl.format(c="v", goal=lw(goal_v, 6), combo=combo(cof_v), **hyps) + "\n")
# The Sage ring names u1 … v5 stand for the Lean identifiers u₁ … v₅; likewise h1 for h₁ and
# e4u for e₄u (whole words only).
sub = dict(zip("12345", "₁₂₃₄₅"))
text = re.sub(r"\b([uvhe])([1-5])(u|v)?\b",
              lambda m: m.group(1) + sub[m.group(2)] + (m.group(3) or ""), text)

long = [line for line in text.split("\n") if len(line) > 100]
assert not long, long[:3]
print("layout: no line over 100 characters")

module_path = "CompElliptic/CurveForms/CtEdwardsCertificates.lean"
marker = "-- The declarations below are generated by `scripts/gen_ctedwards_certificates.sage`;"
src = open(module_path).read()
assert marker in src, "marker line not found in " + module_path
head = src[:src.index(marker)]
out = (head + marker + "\n"
       + "-- edit and re-run that script rather than editing them here.\n\n"
       + text + "\nend CompElliptic.CurveForms.CtEdwards\n")
with open(module_path, "w") as f:
    f.write(out)
print("regenerated " + module_path)
