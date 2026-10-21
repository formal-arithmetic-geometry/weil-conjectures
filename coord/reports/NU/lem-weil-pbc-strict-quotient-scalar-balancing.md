## Worker report

The module `Sheaf.Paper.StrictQuotientScalarBalancing` states
`AlgebraicGeometry.Scheme.StrictScalarBalancing.strictQuotientScalarBalancing`.
Its conclusion packages the natural balancing, its strict quotient augmentation,
and its canonical pullback equation as `Nonempty (Balancing d)`. Every functor and
comparison in that package is fixed by its ordinary normalization or universal
localization computation; the package is not an arbitrary choice of a map.
Only the final theorem has `sorry`; helper definitions have actual data.

Hypothesis and clause correspondence:

- `A : Type (u + 1)` and `[CommRing A]` give the commutative ring.
  `d : AdicCoefficientDatum A` supplies `noetherian`, `ideal`,
  `finitelyGenerated`, `quotientTorsion`, `quotientPerfect`, and `quotientFinite`.
  No completeness condition is imposed on A or on the input complex.
- `topology T` is the published `proEtaleModelTopology T`, obtained from the
  original small pro-etale site by `AsSmall`. Original site object universe u+1
  and morphism universe u are retained through this equivalent model; only Hom
  size is enlarged for the existing constant-completion interface.
- `ring T d false/true` abbreviates the existing constant/completed coefficient
  sheaves `ConstantCompletion.coefficients`. `scalar` is their projection-cone
  map `coefficientMap`. The finite coefficients are `finite`, with powers n+1
  indexed by n : Nat, so every positive power occurs once, with the actual
  quotient transitions of `reductionTower`.
- `D`, `TD`, `Q`, `TQ`, `dres`, `tdres` are the existing standard unbounded
  derived categories, localizations, and exact ordinary/tower restrictions.
  In particular `TD` is D(Natᵒᵖ ⥤ Mod), not Natᵒᵖ ⥤ D(Mod).
- `reduction` uses the existing universal `quotientPresentation.tower`.
  Its computation comparison is with strict scalar extension followed by
  scalar restriction, hence is exactly Delta(-) tensor-derived Q.
  `delta` is the exact constant-diagram functor, with `deltaFactors` its
  canonical localization comparison.
- `Balancing.ρ` is a natural isomorphism of functors on the whole ambient
  derived category. `ρ_computes` identifies its inverse on every flat-term
  K-flat representative with `reductionTowerComparisonComplex`. That existing
  comparison is identity on pure tensor classes, with all strict transitions.
  K-flatness is `IsAcyclicTensorKFlat`, equivalent to the dependency's
  `IsKFlatIndependentCoefficients` at these site/coefficient sizes.
- `augmentation` and `augmentation_computes` specify the actual quotient units
  by `reductionUnit` (x maps to 1 tensor x), rather than unspecified arrows.
  `deltaRestriction` and its computation specify the identity underlying
  restriction/constant-diagram comparison. `augmentation_equation` is the
  node's first displayed equality on every L.
- For each arbitrary edge f, `inverse` is its actual site inverse image;
  `inverseData` is the published algebraic inverse-image lift.
  `coefficient` uses `constantMap` or `completedMap`; the latter is fixed by
  every finite projection. `modulePull` is `ConstantCompletion.pull` and
  `towerPull` applies it termwise. The supplied coefficient-isomorphism
  theorem makes these exact inverse images. `PullModel` records their
  universal derived operations with their canonical computation maps.
- `PullCompatibility.a` and `.p` are the ordinary and strict-diagram scalar
  comparisons. Their computation laws identify them with the existing
  insertion-normalized `ordinaryPullComparison` and its strict whiskering.
  Right-adjoint comparisons chi and d in the node set up the context but do
  not occur in either asserted equation; no property of them is assumed.
- `ordinaryCompleted` and `ordinaryConstant` are specified by
  `PullReductionNormalized`: pull the same sections and insert 1 tensor x,
  at every level and naturally in the whole strict diagram.
  `τ` and `constantReassociation` have those precise K-flat computations by
  `PullReductionComputes`, giving the canonical pullback/tensor reassociations.
- `PullCompatibility.equation` explicitly composes restricted τ, p, and
  the constant diagram pullback of ρ on the left. The right composes ρ on
  the pulled object, reduction of a, and the constant reassociation.
  This is exactly q r(τ) = R⁰(a) ρ after the identification specified by
  the node. It is quantified over every ambient L; naturality comes from
  the recorded natural isomorphisms, not from levelwise derived evaluation.

Dependency interfaces read and used:

- `Sheaf.Paper.AdicCoefficientDatum`: `Scheme.AdicCoefficientDatum` and its
  inherited complete-coefficient fields.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`:
  `SheafOfModules.restrictScalars`, used by the published `res`/`tres`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`; the computation API uses
  its equivalent `IsAcyclicTensorKFlat` characterization.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`:
  `proEtaleModelTopology`, `proEtaleModelBaseChange`, the actual site
  pullback construction underlying `proEtaleConstantRingDerivedPullback`.
- `Sheaf.CategoryTheory.DiagramSiteRealization`:
  `CategoryTheory.exists_diagramSite_realization` (strict module diagrams).
- `Sheaf.CategoryTheory.FlatRingedDiagramRestriction`:
  `FlatRingedDiagramInput.flatRingedDiagramRestriction` (normalized scalar
  comparisons); the representative normalization is exposed by the existing
  `ConstantCompletion.ordinaryPullComparison`.
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`:
  `Scheme.proEtale_profinite_coefficient_inverse_image` (projection-defined
  coefficient isomorphisms, including all finite transitions).
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`:
  `SheafOfModules.CanonicalTensorPullbackOfUniverses.
  ringedTopoiCanonicalDerivedTensorPullback` (K-flat tensor normalization).
- `def-weil-size-convention` is a convention node, without a declaration.
- `Sheaf.Paper.ConstantCompletionEquivalence`, namespace
  `CategoryTheory.ConstantCompletion`: `coefficients`, `coefficientMap`,
  `quotientPresentation`, `reductionUnit`, `resFactors`, `tresFactors`,
  `reductionTowerComparisonComplex`, `DerivedTowerComparisonFormula`,
  `DerivedPullComparisonFormula`, `inverseImageData_exists`, `completedMap`,
  `constantMap`, `pull`, `pullInsertion`, `ordinaryPullComparison`.
  These are existing constructions, not copied notions.

The proof-dependency imports retain the plan: finite-type constant exactness,
flat common-quotient reduction, independent-coefficient K-flat resolutions,
flat scalar restriction, derived change-of-rings, inverse-image tensor
comparison, pure-section calculus, constant-left-module inverse image, and
site-derived tensor descent. The theorem docstring gives all seven proof
steps, including the strict chain-map equalities before localization.

Edge cases checked against the statement: I=0 when the datum is admissible,
I=A (all quotient coefficients zero), the zero ring, an empty scheme, the
zero complex, arbitrary unbounded L, the first positive quotient n=1,
every quotient transition, identity edges and arbitrary scheme edges.
No nonzero, boundedness, derived completeness, flatness/properness of f,
or additional equality of universes has been added.

Searches actually run via the prescribed msearch wrapper:

- LeanFinder: "Restriction of scalars of completed coefficients commutes
  with derived strict quotient reduction towers and their augmentation and
  pullback" returned eight ordinary adic-completion/presentation results,
  including `AdicCompletion.transitionMap_comp_reduceModIdeal`; no match.
- Loogle: "SheafOfModules.restrictScalars, CategoryTheory.NatIso" returned
  no hits and reported unknown identifier CategoryTheory.NatIso; this query
  was unavailable as a useful declaration search, not evidence of absence.
- Mathlib grep: "quotient.*balanc|balanc.*quotient" returned zero hits.
- LeanSearch: "Derived strict quotient towers restriction of scalars
  balancing preserves augmentation pullback" returned eight ordinary
  restriction-of-scalars results (Derivation, Submodule, AlgEquiv, etc.);
  no exact statement.
- Project rg over WeilConjectures and Sheaf for
  "strict.*[Bb]alanc|[Bb]alanc.*strict|quotient.*scalar|StrictQuotient|strictQuotient"
  found neighboring strict quotient and constant-completion APIs, but no
  theorem containing this augmentation and pullback equation. An item-id
  search found no existing implementation in WeilConjectures.

No new DAG notions, dependency repairs, statement correction, or disputed
mathematical clause is needed. Local aliases and specification structures
only assemble this node's own canonical comparisons.

## Second reading by NU

This is the dispatched worker's second reading; the maintainer performs the
independent delivery review. I reread the node and its source's second
paragraph against the final functor directions. The seven datum fields retain
all coefficient hypotheses; reindexing uses n+1 and loses no positive level.
The original unequal site universes are transported through the published
small model, without a new equality hypothesis. Both asserted equalities are
in TD, and their representative normalizations retain the transitions.
The directions are ρ: r Rᵃ to R⁰ r, a: r Lᵃ to G r, and τ: Rᵃ Lᵃ to
script-Lᵃ Rᵃ, so the displayed composite has exactly the node's endpoints.
The final constant reassociation is present explicitly. All ambient variables
are unrestricted; the flat/K-flat clauses only characterize computations.
The augmentation is pinned to reductionUnit, preventing a vacuous zero-unit
specification. Scalar pullback is pinned to ordinaryPullComparison, and
ordinary tensor reassociation is pinned to pure insertion, preventing
arbitrary comparison isomorphisms. During elaboration repair the strict
whiskering uses explicit composition isomorphisms; this changes no map.
