## Worker report

Stated `QuadraticSeries.field_factors` in
`Sheaf.RingTheory.QuadraticSeriesFieldFactors`. Its sole postponed proof is `sorry`.
The auxiliary `scalarConstantSubring` has real data: the inverse image under
`PowerSeries.constantCoeff` of `(algebraMap F (AdjoinRoot p)).range`.
This is the node's displayed A; the theorem explicitly identifies its elements
with the expressions C(a)+t*g. No new independent notion or dependency module is
needed, and the existing node changes only in `lean`.

Sources read: Stacks Project curves.tex, Tag 0C4A,
`lemma-2-branches-delta-1`, especially Cases I and II in the forward implication
and the final description of A by its constant coefficient; algebra.tex,
Tag 0BI0, `lemma-power-series-over-Noetherian-normal-domain` and its proof.
The current blueprint unit `sk-thm-sf-ctf-stability/_section.md` was read;
this is an auxiliary algebra calculation below that unit, not its own statement.
The existing eight-step split is preserved and transcribed into the theorem's
docstring, including the explicit evaluation inverse, norm inverse, coefficient
extension, normal-series application, basis coordinates, integral equation,
module generators, and coefficient-shift injectivity.

Hypotheses and objects:

- The field F is `(F : Type u) [Field F]`; beta and gamma are `(β γ : F)`.
- The polynomial p is `(p : Polynomial F)` fixed by
  `hp : p = Polynomial.X ^ 2 + Polynomial.C β * Polynomial.X + Polynomial.C γ`.
  This equality renders "put p=...", rather than restricting the mathematical
  inputs: for every beta,gamma the displayed polynomial supplies p and reflexivity
  supplies hp. No alternative polynomial is permitted by the equality.
- Nonzero discriminant is precisely `hdisc : β ^ 2 - 4 * γ ≠ 0`.
- L is literally `AdjoinRoot p = Polynomial F ⧸ Ideal.span {p}`, z is
  `AdjoinRoot.root p`, B is `PowerSeries (AdjoinRoot p)`, and t is
  `PowerSeries.X`. No domain or field structure is assumed on L or B.
- A is the concrete `scalarConstantSubring p` above, using the canonical scalar
  inclusion and the canonical subring algebra/module structure on B.

Clause-by-clause correspondence:

1. For every root r, the first conjunct gives `p.eval (-β-r)=0` and
   `r ≠ -β-r`. Its equivalence `e : AdjoinRoot p ≃ₐ[F] F × F` satisfies
   `e (AdjoinRoot.mk p q) = (q.eval r, q.eval (-β-r))` for every polynomial q.
   Thus this is specifically the quotient of simultaneous evaluation, not an
   arbitrary isomorphism with an unrelated product.
2. If no root exists, `IsField (AdjoinRoot p)` expresses that the existing
   commutative quotient ring is a field, and `Module.finrank F (AdjoinRoot p)=2`
   is its extension degree. The proposition-valued `IsField` does not choose
   an arbitrary ring structure or assume a field before asserting it.
3. There exist m with `m=1 ∨ m=2`, a family `K : Fin m → Type u`, field
   structures and F-algebra structures, and the coefficient equivalence phi.
   These are conclusion witnesses, not extra assumptions.
4. The series equivalence Phi has type
   `PowerSeries (AdjoinRoot p) ≃ₐ[F] (∀ i, PowerSeries (K i))`.
   `coeff n (Phi h i) = phi (coeff n h) i` for every h,i,n fixes it
   coefficientwise. The following equality sends X to the tuple of X's.
5. Each factor has `IsDomain` and `IsIntegrallyClosed`. The latter is Mathlib's
   integral closedness in `FractionRing (PowerSeries (K i))`, exactly E_i in
   the node. It means every fraction integral over D_i belongs to D_i.
6. `IsReduced (PowerSeries (AdjoinRoot p))` is reducedness of B, without the
   erroneous domain assertion in the split case.
7. The next conjunct identifies `h ∈ A` if and only if
   `h = C(algebraMap F L a)+X*g`, exactly A=F+tB. The scalar series embedding
   is `PowerSeries.map (algebraMap F (AdjoinRoot p))`; its injectivity and
   membership in A are both stated.
8. For every h there exist `u v : PowerSeries F` with
   `h = map u + C(z)*map v`. Uniqueness quantifies over *every* other pair
   satisfying this decomposition, and equates both coordinates. In particular
   uniqueness does not apply only to pairs already known to satisfy the norm
   equation.
9. For these u,v the following conjunct is exactly
   `h^2 + (C(β)*map v - 2*map u)*h +
     ((map u)^2 - C(β)*map u*map v + C(γ)*(map v)^2) = 0`.
   Every occurrence of beta,gamma is embedded as a constant series through the
   canonical F-to-L map. No factors of two are inverted.
10. `Submodule.span A {1, C(z)} = ⊤` asserts the stated two generators.
    `Module.Finite A B` is the separate finiteness conclusion, and
    `∀ h : B, IsIntegral A h` asserts integrality of every element over A.
11. `X ∈ A` identifies the same parameter as an element of the subring.
    `Function.Injective (fun h : B ↦ X*h)` is regularity on B; the final
    injective map from A to B is its restriction. Because A is a subring
    and X belongs to A, this is equivalent to injectivity of multiplication
    by t as an endomap of A; no arbitrary lift of t is selected.
12. Universes: F, L, and each field factor have universe u; all factors of
    this finite-dimensional F-algebra can be chosen in that same universe
    (L itself or F). No characteristic hypothesis or infinite-field
    hypothesis occurs.

Dependency declarations read and used:

- `Mathlib.Algebra.Polynomial.Basic`: `Polynomial`, `Polynomial.X`,
  `Polynomial.C` (def-weil-polynomial-ring).
- `Mathlib.RingTheory.MvPowerSeries.Basic`: `MvPowerSeries`, with the existing
  one-variable specialization `PowerSeries` and its coefficient, C, X, and map
  operations from `Mathlib.RingTheory.PowerSeries.Basic`
  (def-weil-pbc-multivariate-power-series).
- `Mathlib.Algebra.Algebra.Hom`: `AlgHom`; and
  `Mathlib.RingTheory.Ideal.Quotient.Operations`: `Ideal.Quotient.algebra`
  and `Ideal.Quotient.mkₐ`, the canonical quotient-algebra interface underlying
  `AdjoinRoot` (def-weil-pbc-algebra-hom-quotient).
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`
  (def-weil-finitely-generated-module).
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`, with
  `IsIntegral` from `IntegralClosure.IsIntegral.Defs`;
  `IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosedIn` and
  `IsIntegrallyClosed` (def-weil-pbc-integral-closure and the normal-domain
  proof dependency). The assertions use `IsIntegral` and `IsIntegrallyClosed`
  directly, rather than defining replacement predicates.
- `Mathlib.RingTheory.AdjoinRoot`: `AdjoinRoot`, `AdjoinRoot.mk`,
  `AdjoinRoot.root` and the proof ingredient `AdjoinRoot.powerBasis'`
  (lem-weil-pbc-monic-quotient-free).
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`
  (def-weil-pbc-noetherian-ring), imported for the proof.
- `WeilConjectures.RingTheory.PowerSeriesNormalDomain`:
  `PowerSeries.noetherian_normal_domain`
  (lem-weil-pbc-power-series-normal-domain), imported for the proof.

Searches run with the prescribed msearch wrapper:

- LeanFinder: "For a separable quadratic quotient algebra L over F, L[[t]]
  is a product of normal field power series rings and finite integral over
  F+tL[[t]]". Eight hits, including `PowerSeries.isNoetherianRing` and
  Weierstrass quotient equivalences; no statement covering this node.
- Loogle: `"PowerSeries", "AdjoinRoot"`. Zero hits.
- Mathlib grep:
  `(AdjoinRoot|QuadraticAlgebra).*(PowerSeries|norm)|PowerSeries.*(AdjoinRoot|QuadraticAlgebra)`.
  Eight hits in KummerPolynomial, QuadraticAlgebra and elliptic-curve files;
  ingredients, not the combined statement.
- LeanSearch: "Power series over a separable quadratic algebra are finite
  and integral over the subring with scalar constant coefficient and
  decompose as a product of normal field power series rings". Eight hits,
  including `PowerSeries.toSubring`, the Noetherian/DVR instances, and
  `PowerSeries.algebraPowerSeries`. `PowerSeries.toSubring` concerns *all*
  coefficients in a subring, whereas A constrains only the constant coefficient;
  it is not the displayed A.
- Direct rg searches in `lean/WeilConjectures` and `lean/Sheaf` for quadratic
  series, scalar constant subrings and their declaration names. The existing
  `Sheaf.RingTheory.QuadraticSeriesIntegralClosure` states the parent
  normalization theorem, not this node. Its polynomial and coefficient-algebra
  helpers are recorded under that parent; importing it here would obstruct
  the parent's proof import of this node. This file therefore writes no new
  polynomial or quotient definition: p is fixed by an equality and all
  constructions are directly Mathlib's. The only helper abbreviates the
  subring displayed in this node.
- `grep -rn lem-sfb-quadratic-series-field-factors lean/WeilConjectures`
  found no existing declaration. Further rg searches for
  `scalarConstantSubring`, `theorem field_factors`, and `def field_factors`
  throughout the project and Mathlib found no name collision.

Edge cases checked before writing:

- Over F_2, beta=1,gamma=0 gives distinct roots 0,1 and two factors; the
  assertion uses reducedness, not a domain condition on B.
- Over F_2, beta=gamma=1 gives the irreducible quadratic and F_4 as its
  degree-two field. The formula reduces correctly in characteristic two.
- beta=gamma=0 has repeated root and is excluded by the discriminant.
- The root s=-beta-r and (r-s)^2=beta^2-4gamma calculations do not divide by 2.
- h=0 has u=v=0 uniquely; scalar constants, z, and t satisfy the coordinates
  and equation. The generators need not belong to A; they are elements of B,
  as required for generation of the A-module B.
- m cannot be zero. For m=1 the Pi ring is one factor, for m=2 it is the
  product, and both coefficientwise and variable conditions retain meaning.
- X is regular even when L is split and has zero divisors, since its action
  shifts coefficients. Its restricted map on A uses the same ambient X.

No statement correction, disputed statement, or dependency-record fault was found.
The initial server compilation passed cleanly. The final module and delivery
are validated by scompile.py and the prescribed deliver2.py dry run.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
