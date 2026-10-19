## Worker report

The module `Sheaf.Paper.PointFibreEquivalence` states
`WeilConjectures.point_fibre_equivalence`; its proof is `sorry`. No fibre functor,
coefficient category, completed ring, localization, or common-stage category is
defined again. Two instance definitions merely project the two existing clauses of
`Scheme.proEtale_bounded_constructible_isTriangulated`, specialized to the finite
coefficient quotient, exposing the inherited torsion-source structures. They have
real term bodies and no postponed proofs. Their node is added to stmt_deps as an
already landed prerequisite.

Hypotheses and clauses, matched against the node:

- The global finite-field datum is `(D : FiniteFieldDatum.{u})`; its fields retain
  p prime, a positive, q=p^a, k0 of cardinality q, and its fixed algebraic closure k.
- The coefficient prime and characteristic exclusion are `(l : ℕ) [Fact l.Prime]`
  and `(hl : l ≠ D.p)`.
- The chosen algebraic closure is `(Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω]`
  `[IsAlgClosure ℚ_[l] Ω]`.
- The finite extension contained in that closure is
  `(E : Padic.FiniteCoefficientFields l Ω)`; its actual subfield is `E.val`.
  The inherited field, algebra and finite-dimensional structures are the recorded
  ones. Integer rings, uniformizers and quotients are precisely the Padic coefficient
  constructions in the functor definitions, without any new choice.
- The positive torsion level is `(n : ℕ) (hn : 1 ≤ n)`. The base s is `Spec (.of D.k)`
  in all four recorded fibre functors.
- The first four conjunctions assert `.IsEquivalence` of exactly `pointFiniteFibre`,
  `pointIntegralFibre`, `pointRationalFibre`, and `pointQbarFibre`, respectively.
  The first three use `E.val`, the last uses Ω and all its finite stages.
- Each subsequent existential supplies a coherent `Functor.CommShift ℤ` structure,
  followed by preservation of every distinguished source triangle under the
  corresponding `Functor.mapTriangle`. This includes negative, zero and positive
  integer shifts, with the zero/add coherence required by CommShift.
- For the first three target full subcategories, the functor is composed with its
  existing `ObjectProperty.ι` and distinguishedness is tested by `distTriang` in the
  ambient derived category. This is the definition of inherited distinguished
  triangles, and commuting with ambient shifts is precisely the inherited shift
  comparison: full faithfulness lifts the isomorphisms and their coherence uniquely.
  It imposes no target size, Tor-amplitude or perfectness restriction.
- For the fourth, the functor itself has the shift comparison and the image triangle
  satisfies `DerivedCategory.pointFdQbarDistinguished l Ω`. This is the exact recorded
  common-stage target predicate; it is not replaced by arbitrary ambient triangles.

Dependency declarations read and used (all on newtargets-dag):

| Module | Declarations |
| --- | --- |
| Sheaf.Paper.FiniteFieldFiber | WeilConjectures.FiniteFieldDatum |
| Sheaf.Paper.FiniteCoefficientPoint | WeilConjectures.pointFiniteFibre, pointIntegralFibre, pointRationalFibre, pointQbarFibre (same namespace) |
| Sheaf.Paper.IntrinsicFiniteTorsionConstructibility | AlgebraicGeometry.Scheme.intrinsicFiniteTorsionConstructible |
| Sheaf.Paper.SfIntegralConstructible | WeilConjectures.sfIntegralConstructible, sfIntegralConstructibleCategory |
| Sheaf.Paper.SfRationalizationKaroubi | WeilConjectures.sfRationalConstructibleCategory and its inherited shift/triangulation |
| Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients | WeilConjectures.generalAlgebraicallyClosedConstructibleCategory |
| Sheaf.Paper.PointFiniteCohomologyComplexes | DerivedCategory.pointFiniteCohomology |
| Sheaf.Paper.PointFgCompleteComplexes | DerivedCategory.pointFgComplete |
| Sheaf.Paper.PointFdComplexes | DerivedCategory.pointFiniteDimensional |
| Sheaf.Paper.PointFdQbarCategory | DerivedCategory.PointFdQbar, pointFdQbarHasShift, pointFdQbarDistinguished |
| Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated | AlgebraicGeometry.Scheme.proEtale_bounded_constructible_isTriangulated |

Every recorded proof-dependency module with a declaration is imported (non-public
when used only by the future proof). The two new stage-1 proof prerequisites
`lem-weil-point-completed-scalar-shift` and `lem-weil-point-sections-tensor-shift`
currently have no Lean module, so there is no module to import for them. They are
not assumptions of this theorem. The docstring preserves all fourteen proof steps
and their named dependencies, including both shift-compatibility prerequisites.

Edge cases checked: n=1 is retained; n=0 is excluded exactly as in the node.
Zero modules and the zero complex satisfy all three finiteness predicates, and
empty cohomological support and the empty direct sum in rational essential
surjectivity are retained. No semisimplicity or perfectness is imposed on the
finite torsion quotient, which can be singular for n>1. The integral target keeps
derived completeness with respect to the actual lifted uniformizer ideal.
Rationalization and the algebraically closed category remain the raw categories,
with no idempotents adjoined. The base really is the algebraically closed field
from D, not Spec k0. Universes follow the existing four fibre functors; the ULift
coefficient carriers in their first two targets are retained verbatim.

Sources opened: the node's master blueprint order 1509 and current
main-20261015/sec-six-functors-basics/sk-def-sf-admissible/
def-weil-finite-coefficient-point.md, order 1868. The main source has the same four
fibre equivalences. No statement correction or disputed statement is needed. The
resolved stage-1 repair note concerns splitting the final common-stage proof;
the current fourteen-step route is copied into the theorem docstring unchanged.

Searches performed through msearch.py (Q60, this item), plus direct rg:

- leansearch: "The fibre functor for constructible derived l-adic sheaves on a
  geometric point is an equivalence". Eight results concern Galois-category fibre
  functors, general site fibres and condensed locally constant sets; no match.
- leanfinder: "fibre functor derived constructible sheaves algebraically closed point
  equivalence". Eight results concern Grothendieck topology points and Galois fibre
  functors; no coefficient-derived equivalence.
- loogle: "CategoryTheory.Functor.IsEquivalence, CategoryTheory.Functor.CommShift,
  CategoryTheory.Functor.IsTriangulated". Zero hits.
- grep: "pointFiniteFibre|pointIntegralFibre|pointRationalFibre|pointQbarFibre".
  Zero Mathlib hits. Direct rg in slopmaster2/WeilConjectures with the same names
  and with the blueprint id found no declaration.
- Direct rg in shared lean/Sheaf found the four functors in FiniteCoefficientPoint
  and their normalization helpers, not this equivalence theorem. Reading the
  declarations confirmed that the owning definition explicitly leaves equivalence
  to this separate node. Upstream declaration-name catalogue has no matching name.

Validation: scompile.py passed on 2026-10-17 with no errors or warnings: sandbox
19.7 s, library-path confirmation 10.7 s, both within the 60-second limit.
The initial docstring-spacing warning was repaired and the complete file recompiled.
The delivery dry run performs the remaining server preflight.

## Second reading by Q60

This is the author's fresh clause-by-clause self-check, as required by direct
worker delivery; the maintainer performs the independent reading. Reopened the
node and the module together. D, l, hl, Ω, E and n/hn match the fixed global datum,
prime exclusion, closure, finite subfield and positive level. The four exact
functors are used without choosing replacement maps. Every `.IsEquivalence`
refers to the original full-subcategory target. The four CommShift existentials
cover every integer, and each is used by its own mapTriangle expression so that
the last arrow uses that same comparison. The first three ambient tests are the
inherited full-subcategory tests, while the fourth is the actual common-stage
predicate. Checked the complete integral condition, raw rationalization and common
finite stages against their recorded definitions. No missing clause, added
hypothesis, or weakening was found. The only extra declarations expose already
stated source instances, with no new theorem or arbitrary structure choice.
