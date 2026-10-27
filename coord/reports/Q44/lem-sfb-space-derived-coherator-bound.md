## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceDerivedCoheratorBound` states
`AlgebraicGeometry.AlgebraicSpace.derivedCoherator_affineHypercohomology_bound`.
Its only proof is `sorry`. No definitions or new nodes are introduced and the
natural-language statement is unchanged. Source checked directly:
`literature/stacks-project/spaces-perfect.tex`, Tag 0CSS,
`lemma-boundedness-better-coherator`, including its affine and distinguished-square proof.

Hypothesis and clause correspondence:

- The size convention is explicit `universe u w`, `S : Scheme.{u}`, and
  `[HasDerivedCategory.{w} X.SmallModules]`. The module carriers retain universe u;
  w is the existing derived localization's morphism universe. No equality of
  independently sized site and coefficient universes is imposed.
- The algebraic space over S is `X : AlgebraicSpace S`, the existing full category
  of fppf sheaves with representable diagonal and surjective etale scheme atlas.
- Quasi-compactness is `hqc`: a scheme `U : Over S` and its actual Yoneda map
  `a : yoneda.obj U ⟶ X.obj.obj` with `CompactSpace U.left`, `IsEtale a`, and
  `IsSurjective a`. This is exactly the atlas formulation in the node.
- Quasi-separatedness is `hqs`: for every pair of affine etale Yoneda scheme maps
  to X, the presheaf fibre product has a representing scheme W whose underlying
  space is compact. This is verbatim the usable interface of the adjunction node.
- The small ringed model, module sheaves, and unbounded derived category are the
  existing `X.SmallModules` and `X.DerivedModules`. The quasi-coherent derived
  subcategory is `X.DerivedQCoh`, whose objects have the original Mathlib
  `SheafOfModules.IsQuasicoherent` cohomology after inverse small-model restriction.
  This is D_QCoh as a full subcategory of D(O_X), not D(QCoh(X)).
- The right adjoint is the actual functor `DQ : X.DerivedModules ⥤ X.DerivedQCoh`
  with `adj : X.derivedQCohProperty.ι ⊣ DQ`. It is not an arbitrary map or a
  hypothetical cohomology operation. Its existence is the recorded dependency
  theorem. The bound applies to any such adjunction; uniqueness of right adjoints
  makes its assertion invariant under the chosen coherator presentation.
- `∃ N : ℤ, 0 ≤ N ∧ ...` gives a nonnegative integer before all interval, input,
  resolution, chart, and degree quantifiers. No N may depend on a,b,E or U.
- `∀ (a b : ℤ), a ≤ b → ∀ (E : X.DerivedModules)` is precisely the requested
  ordered integer interval and arbitrary unbounded object.
- `I : CochainComplex X.SmallModules ℤ`, `I.IsKInjective`, and
  `Nonempty (DerivedCategory.Q.obj I ≅ E)` expose a K-injective representative
  of this same E. They only specify the computation of hypercohomology already
  required by the node. Such representatives exist by the published
  `smallModules_hasKInjectiveResolutions`; every choice is quantified, so there
  is no arbitrary replacement map or restriction to resolvable inputs.
- The antecedent quantifies `U : X.SmallEtaleModel` and all integer degrees
  `i < a ∨ b < i`. The composite `SheafOfModules.toSheaf ⋙ sheafToPresheaf ⋙
  evaluation` takes actual abelian sections on U, forgetting scalar action.
  `mapHomologicalComplex (ComplexShape.up ℤ)` applies sections termwise to I;
  `IsZero (...homology i)` says precisely H^i(U,E)=0. Every affine etale chart
  occurs up to isomorphism in this small skeleton, and section complexes are
  invariant under chart isomorphism. Thus testing its objects is equivalent to
  testing every affine etale scheme over X. No ordinary-cohomology-sheaf
  evaluation is substituted for hypercohomology.
- The conclusion is `∀ i : ℤ, (i < a ∨ b + N < i) → IsZero
  ((DerivedCategory.homologyFunctor X.SmallModules i).obj (DQ.obj E).obj)`.
  The final `.obj` is the underlying object of the existing full subcategory.
  These are cohomology SHEAVES. Equivalence with the original ringed topos
  preserves and reflects their vanishing. There is no assumption of
  quasi-coherence or boundedness on E.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsEtale`, `IsSurjective`, `EtaleSite`, `structureSheaf`, and `Modules`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme` identify the fibre products and etale charts.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel`: `AffineEtaleCharts`,
  `SmallEtaleModel`, `smallEtaleModelTopology`, `smallStructureRings`, `SmallModules`,
  `smallModuleRestriction`, and `smallModuleEquivalence` retain actual section rings
  and the equivalence with the original small etale module topos.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`;
  Mathlib `SheafOfModules`, `SheafOfModules.toSheaf`, and sectionwise evaluation.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory`, and `DerivedCategory.Q`; `DerivedCategory.homologyFunctor`
  from `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, with
  Mathlib `SheafOfModules.IsQuasicoherent` (the dependency's exact Mathlib match).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `derivedQCohProperty`, `DerivedQCoh`, `smallModules_hasKInjectiveResolutions`.
- `Sheaf.AlgebraicGeometry.SpaceDerivedCoheratorAdjunction`:
  `exists_derivedCoheratorAdjunction`, supplying the right adjoint used here.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`:
  `CochainComplex.IsKInjective`, the exact dependency Mathlib match. No duplicate
  K-injective or resolution predicate is defined.

The declared proof dependencies that already have modules are plain proof imports:
`ExactDerivedAdjunctionBounds`, `AffineEtaleDerivedModuleRealization`,
`SpaceDerivedEtaleChartCalculus`, `SpaceQcqsDistinguishedSquareInduction`, and
`RingedSheafSliceAdjunction`, plus Mathlib's derived homology sequence. The
coherator adjunction is a public statement import. The affine-coherator formula,
distinguished-square triangle, derived-pushforward upper bound, and qcqs permanence
nodes have no recorded Lean module at this reading, so supply no import yet.
All six node proof steps and their named inputs are included in the theorem docstring.

Edge cases checked before writing: the empty scheme/space is not excluded by an
inhabitedness condition; its zero module topos satisfies vanishing. The zero E and
zero K-injective representative are allowed. Arbitrary negative a,b and a=b are
allowed. The endpoints a,b,b+N are included; the inequalities are strict outside
the intervals. N=0 is allowed, matching the affine case and the empty affine
case. No separated, Noetherian, finite-type, finite-dimensional, or characteristic
hypothesis is imposed. An unbounded I is allowed even when its affine section
cohomology vanishes outside a finite interval. The adjunction hypotheses are
substantive, and no extra tautological clause is appended to the conclusion.

Searches performed through the prescribed msearch.py wrapper:

- LeanFinder: `Uniform affine etale hypercohomology bound for derived quasi
  coherator of a quasi compact quasi separated algebraic space`: eight unrelated
  affine-transition-limit hits; no matching result.
- Loogle: `DerivedCategory.homologyFunctor, CochainComplex.IsKInjective`: zero hits.
- Mathlib grep: `coherator|derivedCoherator|derivedEvaluation`: zero hits.
- LeanSearch: `For a quasi compact quasi separated algebraic space the right
  adjoint to the inclusion of complexes with quasi coherent cohomology has a
  uniform bound from affine etale hypercohomology`: eight scheme compactness,
  quasi-separatedness and Gamma-Spec adjunction hits; none states this bound.
- rg in both `lean/WeilConjectures` and `lean/Sheaf`:
  `coherator|derivedCoherator|DerivedCoherator|lem-sfb-space-derived-coherator-bound`.
  Existing results concern the coherator adjunction, affine scheme comparisons,
  stack coherators, or consumers of this bound, not this algebraic-space theorem.
  The required exact item-id search in WeilConjectures returned no hit.
- Additional local searches for `evaluation`, `hypercohomology`, and K-injective
  section computations located the Mathlib functors used directly in the signature.
  The module-evaluation/slice theorem covers ordinary derived functors on module
  sheaves, not the unbounded-object bound; it is not used to replace this notion.

Validation: scompile.py checked both its sandbox name and its intended library
module name cleanly (2.0 s each). No compiler warnings or errors were reported.
There are no statement disputes, corrections, new definition nodes, or dependency
repairs. Independent statement review is left to the maintainer as prescribed by
the dispatch brief; no worker second-reading claim is made here.

## Second reading by Q44

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
