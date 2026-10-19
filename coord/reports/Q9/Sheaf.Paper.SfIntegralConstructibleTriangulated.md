## What changed

Completed both declarations in `Sheaf.Paper.SfIntegralConstructibleTriangulated`.
The isomorphism closure proof transports the augmented Roos triangle through a product
isomorphism. The triangulation proof now proves a generic reflective-subcategory lemma:
the completion reflection unit, its shift compatibility, and the Hom bijection identify the
complete objects with a double orthogonal, which Mathlib makes triangulated. The published
coefficient presentation comparison identifies this predicate with `IsSfDerivedComplete`.
The finite reduction and uniform interval closures remain fully proved in the item module.
At zero all reduction supports are empty; a shift by m translates [a,b] to [a-m,b-m];
and the homology exact sequence bounds middle support by [min a1 a3,max b1 b3].
The finite coefficient ring theorem supplies constructibility closure at every level,
without requiring the quotient to be flat over the completed ring.
All original public signatures are unchanged. Helper namespace opens are localized to
private declarations. The direct intrinsic finite-torsion import is retained because
it realizes a unit-route statement; no unit-route module is removed.

## Proved and sorry left

Closed both original holes:

- `WeilConjectures.sfIntegralConstructible_isClosedUnderIsomorphisms`.
- `WeilConjectures.sfIntegralConstructible_isTriangulated`.

No `sorry` remains in the item or in any new module. No split-off theorem was retained.
Holes closed: 2. Holes added: 0. All private helper proofs are complete. Reused library
statements may still depend on their own named holes, as this stage permits.

Validation: the retained full item previously compiled cleanly with `lcompile.py --all`
in 3.8 seconds, then with the single-file command in 3.2 seconds against the current
published library. Both original public signatures match the current source.
On the current resumption, the item compiled cleanly in 3.1 seconds.
A fresh consumer probe compiled in 2.1 seconds: the full subcategory has its
integer shift, pretriangulation and triangulation, and its inclusion is triangulated.
The import-direction check also confirms that the reflection module introduces no cycle.
The general reflection proof also compiled separately while developing the argument.
Zero and the empty scheme are covered: the argument is categorical and assumes no
nonempty scheme, dimension bound or Noetherian hypothesis. The same witnesses establish
intrinsic isomorphism closure; the zero cone argument uses its identity, without a choice
of an arbitrary completion object.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Paper.IntegralReductionTowerWellDefined`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Algebra.Homology.KFlat`.
- `Sheaf.Paper.CompletedIntegralCoefficientGerm`.
- `Sheaf.Paper.IntegralReductionTower`.
- `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.Paper.WeilCompletedTensorReflector`.
- `Sheaf.Paper.DerivedCompleteUnrestricted`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence`.
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitTowerTriangle`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `Mathlib.Algebra.Homology.Functor`.
- `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`.
- `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`.
- `Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck`.
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`.
- `Sheaf.CategoryTheory.RingedSiteCompleteElementsIdeal`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`.
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`.
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`.
- `Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`.
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`.
- `Sheaf.Paper.DerivedCompleteOnSlices`.
- `Sheaf.Paper.IntegralReductionTowerCanonical`.
- `Sheaf.Paper.ProEtaleConstructibleSheaf`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerTriangle`.

The following former proof-dependency nodes are not needed directly by this proof:

- `def-weil-completed-integral-coefficients`.
- `lem-weil-pbc-constant-completion-equivalence`.
- `lem-weil-proetale-countable-products-exact`.
- `lem-weil-derived-limit-existence`.
- `lem-weil-derived-limit-tower-core-property-triangle`.
- `lem-weil-pbc-ring-sheaves-grothendieck`.
- `lem-weil-pbc-small-module-diagrams-grothendieck`.
- `def-weil-triangulated-category`.
- `lem-sf-triangle-morphism-iso`.
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`.
- `lem-weil-pbc-ringed-derived-complete-elements-ideal`.
- `lem-sp-grothendieck-enough-injectives`.
- `lem-weil-pbc-kinjective-functorial-existence`.

The top-level tool-use approvals removed as obsolete are:

- `lem-weil-pbc-constant-completion-equivalence`.
- `lem-weil-derived-limit-existence`.
- `lem-weil-pbc-small-module-diagrams-grothendieck`.
- `lem-weil-pbc-ringed-internal-hom-exact-restriction`.
- `lem-weil-pbc-ringed-derived-complete-elements-ideal`.
- `lem-sp-grothendieck-enough-injectives`.
- `lem-weil-pbc-kinjective-functorial-existence`.
- `lem-weil-derived-limit-tower-core-property-triangle`.

The proof uses the published `PbcCompletedPullbackActual` completion reflection and
`CompletedCoefficientPresentationTransport` comparison instead of reconstructing strict
towers, slice internal Hom and their unit compatibilities. The unused DAG imports above
are pruned from this node's route; transitive imports of reused library interfaces may
still contain these modules, and no global closure removal is claimed.

The temporary `SfDerivedCompleteTriangulated` module and its node from the interrupted
attempt were never submitted or landed and have been removed from this sandbox. Its
completeness theorem is now proved by private helpers in the item. No existing library
module is withdrawn. The unit has no realized proof steps and its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt split the completeness component before checking the existing published
completion reflection. That split was unnecessary. The DAG proof dependencies were updated to
match the shorter reflection and coefficient-transport route; the target statements and all
existing definitions remain unchanged.

Checked the exact reflection declarations against current sources:
`pbcActualCompleteInclusion_isRightAdjoint` and
`pbcActualCompletionShift_exists` live in `PbcCompletedPullbackActual`.
Their docstrings tag the ordinary ringed-topoi adjunction node, whose main Lean
attachment remains the ordinary module adjunction in a different module.
The proof step explicitly names the published reflection specialization of
the existing approved Koszul reflector; it uses neither the ordinary adjunction
nor any pullback/pushforward assertion. No additional tool-use approval or
dependency on that unrelated ordinary-adjunction statement is claimed.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
