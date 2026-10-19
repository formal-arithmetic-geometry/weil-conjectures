## Worker report

The new module `Sheaf.AlgebraicGeometry.Curve.FiniteMapAffineLine` states
`AlgebraicGeometry.exists_finite_genericallyEtale_curve_enlargement` with a single
`sorry` proof. It introduces no definitions and proves no theorem. The node is unchanged
except for its `lean` record. No statement correction or disputed statement is needed.
The module and theorem docstrings cite the blueprint and give all eight steps of the
node's natural-language proof, with their dependency ids.

Source read: the complete node and its proof, plus
`literature/blueprint/master/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/lem-a1-finite-map-curve.md`.
The recorded source has no `blueprint_update`. The finite-field convention is an explicit
statement dependency, not an extra assumption introduced by this delivery.

Hypotheses and conclusion, clause by clause:

| Node clause | Lean rendering |
| --- | --- |
| The global finite field k₀ and fixed algebraic closure k | `(D : FiniteFieldDatum.{u})`; its `field_base`, `finite_base`, `algebra_closure`, and `isAlgClosure` fields supply exactly the global datum. |
| C₀ is a curve over k₀ | `(C₀ : Over (Spec (.of D.k₀))) [IsCurve C₀.hom]`. `IsCurve` includes separatedness, local finite type, quasi-compactness and dimension at most one. |
| C₀ is smooth | `[Smooth C₀.hom]`. |
| C₀ is affine | `[IsAffine C₀.left]`. |
| C₀ is geometrically a connected curve | `[IsConnectedCurve (D.geometricFiber C₀).hom]`. This demands connectedness, nonemptiness and dimension exactly one after the specified algebraic closure base change. |
| There is a curve C₀' over the same k₀ | `∃ (C₀' : Over (Spec (.of D.k₀))) (hC₀' : IsCurve C₀'.hom), ...`. |
| C₀' is smooth | `Smooth C₀'.hom`. |
| C₀' is geometrically a connected curve | `IsConnectedCurve (@FiniteFieldDatum.geometricFiber D C₀' hC₀'.toLocallyOfFiniteType hC₀'.toQuasiCompact).hom`. The explicit proofs are the finite-type fields of the preceding curve witness, not additional assumptions. |
| C₀' contains C₀ as an open over k₀ | `∃ (j : C₀ ⟶ C₀'), ... IsOpenImmersion j.left`. An `Over` morphism includes commutation with the structure maps. |
| This open is dense | `DenseRange j.left`. |
| Its complement is finite | `(Set.range j.left)ᶜ.Finite`. This is the complement in C₀', not in a projective completion. |
| A morphism g to the affine line over k₀ | `g : C₀'.left ⟶ 𝔸(ULift.{u} (Fin 1); Spec (.of D.k₀))`, together with `g ≫ (𝔸(ULift.{u} (Fin 1); Spec (.of D.k₀)) ↘ Spec (.of D.k₀)) = C₀'.hom`. |
| g is finite | `IsFinite g`. |
| g is generically étale | `∃ U : C₀'.left.Opens, Dense (U : Set C₀'.left) ∧ Etale (U.ι ≫ g)`. This spells out étaleness on a dense open source; no separate predicate is defined. |

Dependency declarations used, with full signatures/docstrings read:

- `WeilConjectures.AlgebraicGeometry.Curve`: `AlgebraicGeometry.IsCurve` and
  `AlgebraicGeometry.IsConnectedCurve`. The former works over any field and specializes
  to the blueprint curve definition; the latter includes exact dimension one and
  nonempty connectedness. The node's algebraically closed geometric curve uses the
  same declaration over D.k.
- `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum` and
  `WeilConjectures.FiniteFieldDatum.geometricFiber`. The latter is the actual
  `Over.pullback` along `Spec.map (algebraMap D.k₀ D.k)`, with its second projection.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
  The recorded definition agrees with formal smoothness plus local finite presentation.
- The convention node `def-weil-pbc-scheme-conventions` has no declaration of its own;
  its existing `IsAffine`, `IsOpenImmersion`, `IsFinite`, and `Etale` meanings are used
  directly from Mathlib, with no copied notions.
- `Mathlib.AlgebraicGeometry.AffineSpace`: `AlgebraicGeometry.AffineSpace` and its
  canonical structure map. The coordinate type `ULift.{u} (Fin 1)` has exactly one
  element and the correct universe; this is the affine line in every universe u.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`; the dense-open
  clause uses this affine-local étale property without changing its definition.

Public imports expose the statement's notions. Non-public proof imports follow the
recorded proof dependencies: `WeilConjectures.AlgebraicGeometry.Regular`,
`WeilConjectures.AlgebraicGeometry.Curve.ClosedPoint`,
`Sheaf.AlgebraicGeometry.FunctionField`,
`Sheaf.AlgebraicGeometry.SectionsMorphismToProjPolynomialRing`,
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace`,
`WeilConjectures.Mathlib.Topology.KrullDimension`,
`WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite`,
`Mathlib.AlgebraicGeometry.Noetherian`, and `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
The already public finite-morphism module also supplies finite-base-change permanence.
The proof-only nodes `lem-wf-curve-normal-smooth-compactification`, `sk-thm-picard-rr`,
`lem-a1-uniformizer-differential-basis`, and
`lem-a1-nonzero-differential-generically-etale` have no recorded Lean declaration in the
read repository; no import can yet be added for them. None is needed to type this statement.

Edge cases checked:

- Empty schemes and dimension-zero points do not satisfy the geometric connected-curve
  hypothesis. This is required by the node's term “connected curve,” not an added condition.
- Arbitrary positive characteristic and finite fields of every cardinality in the global
  datum are retained. No rational boundary point, algebraically closed base field,
  infinitude of k₀, or fixed characteristic is assumed.
- The enlargement is not assumed proper or identified with the input; the finite
  complement may be empty (for example when an enlargement is unnecessary).
- Generic étaleness does not require global étaleness. The source open may be the whole
  source, and density forces it nonempty because the geometric connected-curve condition
  implies the source is nonempty.
- No separability, integral-scheme, surjectivity, fixed degree, or smooth-relative-dimension
  hypothesis is added. Those facts may be derived in the future proof where needed.
- All universes and variables are explicitly bound. There are no file-local definitions,
  local notation, local instances, hidden `let` binders, or auto-bound implicits.

Searches made on 2026-10-17 (all through the prescribed msearch wrapper where applicable):

1. LeanFinder: “A smooth affine geometrically connected curve over a finite field admits
   a dense open enlargement with finite complement and a finite generically etale morphism
   to the affine line.” Eight hits, including standard smooth polynomial charts and
   existing smooth/étale definitions; no theorem asserting this enlargement.
2. Loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.Smooth`. Zero hits.
3. Mathlib grep: `generically.?[eé]tale|finite.*map.*curve` in AlgebraicGeometry. Zero hits.
4. LeanSearch: “A smooth affine curve over a finite field embeds as a dense open with
   finite complement in a smooth curve finite and generically etale over the affine line.”
   Eight hits about smoothness, open immersions, étaleness and dense subsites; no match.
5. Direct `rg` in upstream `WeilConjectures` and project `lean/Sheaf`:
   `generically.?[eé]tale|finite.map.curve|finite.*affine.line|exists.*finite.*curve`.
   Hits include high-degree-vanishing affine opens, projective-line projections, and
   relative-line constructibility/reduction results, but no finite generically étale
   enlargement of the given affine curve. `grep -rn 'lem-a1-finite-map-curve'` in the
   upstream source returned no hit.
6. Exact proposed declaration/module search in Mathlib, upstream, project Lean and
   `dag/lean_names_upstream.json`: no collision.
7. The DAG's generic-étale occurrences refer to this result and its consumers or the
   differential criterion; no reusable separate definition is missing or duplicated.

Validation: `scompile.py Q29 lem-a1-finite-map-curve` compiled the delivered file as both
sandbox and library module cleanly (no errors or warnings). No global build was run.

## Second reading by Q29

The dispatcher explicitly forbids starting other agents and assigns the maintainer's
independent review to the delivery process. This section records my separate final reread,
not an independent-agent review.

With the node and completed module open, I rechecked every row above against the actual
signature. In particular, the geometric connected-curve condition uses the structure map
to the algebraic closure in both hypothesis and conclusion; its dimension-one requirement
has not been replaced by connectedness alone. The existential curve witness supplies the
explicit finite-type proofs for the conclusion's geometric fiber. The map j is over the
base field, the density and complement clauses use its range in C₀', and the map g has
an explicit base-field compatibility equation. The affine line has one coordinate, and
its index lift is only for universes. The dense open in the final clause is on the source,
and its morphism is exactly `U.ι ≫ g`. No missing hypothesis, extra conclusion, statement
fault, new definition or dependency repair was found. The sole theorem proof remains `sorry`.
