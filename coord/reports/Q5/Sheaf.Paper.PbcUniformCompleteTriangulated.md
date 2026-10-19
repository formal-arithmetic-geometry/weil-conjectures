## What changed

Replaced the sole hole in `pbcIntegralUniformComplete_isTriangulated` by a complete
proof, with its original signature unchanged. Two proved private categorical arguments
show that an exact pointed functor's invertible-unit locus is triangulated, and that
uniform cohomology bounds with triangulated level conditions form a triangulated locus.
Their intersection gives the original three-clause predicate.

`pbcExactCompletionData` is proved using the existing actual completion reflector and
shift stability. A proved generic double-orthogonal argument makes its reflective
subcategory triangulated, and the adjunction makes completion exact. No new completion
existence or exactness hole remains.

`pbcUniformReductionCriterion_backward` is proved: the canonical normalized reduction
tower and the existing local-effectivity theorem produce common local models. Exact
coefficient comparison transports their origins. Bounded-below full faithfulness lifts
all consecutive normalizations to the etale origins and proves compatibility.
The criterion combines this proof with the separate common-local-model cohomology lemma.

`constructibleCoefficientHomology_isTriangulated` is proved from abelian exact closure.
Zero and isomorphism closure are explicit, and universal-property isomorphisms of
kernels and cokernels supply the homology-property closure instances.

The profile module contains the actual reduction functor and its cohomology predicate.
The converse uses the existing `pbcReductionAdicTower` from `LevelwiseAdicTruncations`.
The current import-direction check permits this route. The unused duplicate canonical
coherence theorem and its new node have been removed from this delivery.
No existing module except the assigned item is changed.

The final local cohomology proof reuses `LevelwiseAdicTruncations` for the lower bound
and the canonical tower, `NoetherianStratumDetection` for upper-bound descent, and the
canonical pullback/restriction comparisons. The coefficient encoding already proved in
`ConstructibleCoefficientSerre` identifies the finite local models. All supporting
modules in this packet are fully proved.

## Proved and sorry left

Proved one of one original holes:
`AlgebraicGeometry.Scheme.pbcIntegralUniformComplete_isTriangulated`.
Holes closed: 1. Holes added: 0. No split-off hole remains. All seven delivered Lean
modules contain zero `sorry`s; the proof uses the existing declared dependencies of the
library, some of whose proofs are still pending in other items.
New fully proved public results are
`AlgebraicGeometry.Scheme.constructibleCoefficient_exactClosure`,
`AlgebraicGeometry.Scheme.pbcExactCompletionData`,
`AlgebraicGeometry.Scheme.pbcUniformReductionCriterion_backward`,
`AlgebraicGeometry.Scheme.pbcUniformReductionCriterion`, and
`AlgebraicGeometry.Scheme.constructibleCoefficientHomology_isTriangulated`.

`AlgebraicGeometry.Scheme.pbcUniformLocalModelCohomology` is also fully proved.
Its private helpers establish the upper bound, descend finite local constancy, and
transport the common local models and their normalization equations. The existing
integral levelwise truncation theorem at the common upper cutoff supplies the lower
bound. There is no sorry inside a definition or private declaration. No existing
statement or definition was changed.

## No longer needed

The following proof imports were removed from the original module:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.CategoryTheory.SitePullbackAbelianExact`
- `Sheaf.Paper.AdicCoefficientDatum`
- `Sheaf.Paper.BoundedConstructibleTower`
- `Sheaf.Paper.CompactSupportComparisonPullbackCoherence`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.ConstantModuleSectionProperties`
- `Sheaf.Paper.IntegralUniformCoefficient`
- `Sheaf.Paper.IntrinsicCompletion`
- `Sheaf.Paper.IntrinsicCompletionCompleted`
- `Sheaf.Paper.NormalizedConstructibleTowerLocalEffectivity`
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`
- `Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf`
- `Sheaf.Paper.ProEtaleConstructibleSheaf`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

The local cohomology module removes its draft proof imports
`Sheaf.CategoryTheory.SitePullbackAbelianExact`,
`Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative`,
`Sheaf.Algebra.Homology.RingedTensorCohomologicalBounds`,
`Sheaf.Paper.ConstantModuleSectionProperties`, and
`Sheaf.Paper.ConstantCompletionEquivalence`. The tensor upper-bound theorem is still
used through the public import in `LevelwiseAdicTruncations`. The direct completion
and constant-section arguments are replaced by that existing theorem's integral
truncation bound. In particular the local cohomology node no longer has direct proof
dependencies `lem-weil-pbc-site-pullback-abelian-exact`,
`lem-weil-pbc-derived-stalk-conservative`,
`lem-weil-pbc-constant-module-section-properties`, or
`lem-weil-pbc-constant-completion-equivalence`. These removals are direct-dependency
pruning; no claim is made that these modules disappear from the full import closure.
No additional proof of a quotient resolution or a new canonical tower is needed.

The exact-completion proof no longer needs the countable-products/Koszul localization
route: the already stated actual completion reflection and shift compatibility suffice.
The original module imports the three higher interfaces it uses, Mathlib's truncation
API, and the required unit-route finite-level comparison module. The latter direct
import is retained for the unit route, and its declarations are used by the compatible
origin argument through the criterion module. Most of the original analytic dependencies remain below
those interfaces; removal of a direct import is not claimed as pruning the whole node.
The homology-closure module also drops the redundant direct import of
`Sheaf.Paper.ProEtaleConstructibleSheaf`, already public through its statement import.
The criterion's proof imports are reduced to the existing levelwise tower, local effectivity,
the derived site comparison and the comparison's faithful instance. The redundant
direct finite-level comparison import is removed; that theorem remains below the
existing derived comparison.

The parent withdraws obsolete direct tool approvals for
`lem-weil-proetale-countable-products-exact`,
`lem-weil-pbc-site-pullback-abelian-exact`,
`lem-weil-pbc-derived-stalk-conservative`, and
`lem-weil-proetale-dbc-triangulated`; derived change of rings remains a direct dependency.
The new cohomology proof instead uses direct Noetherian stratum-cover detection;
it does not use geometric stalk detection or the retained etale-origin hypothesis.
The old unlifted `UniformCompleteTriangulated` interface is unused because its coefficient
universe and geometric unit hypothesis differ. The earlier sandbox's equivalent
`PbcIntegralUniformCompleteCore` was never delivered and is excluded.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox core theorem only repackaged all closure fields and supplied no
reduction. The actual categorical combination is now proved. The existing small-ring
constructible exact-closure theorem has `A : Type u` and a different constant-ring
presentation; it does not directly cover actual coefficients in `Type (u+1)`.

The earlier report claimed that importing `LevelwiseAdicTruncations` creates a cycle.
The current source graph permits the import into both the criterion and assigned item;
the import-direction check and all-module compilation confirm it. The delivery reuses
its canonical tower rather than adding another coherence obligation.

The unit's proper-base-change statement and steps remain unchanged. All new work is
inside the triangulation supplement. No target statement or existing definition changes.
The earlier draft left the local cohomology implication open. It is now proved by a
shorter route: the common upper bound makes the Tor condition for truncation automatic,
and the existing integral levelwise truncation theorem supplies the lower bound. Its
DAG dependencies have been checked to contain no path back to this item. The original
unit statement and its three proof steps are preserved. All seven modules compile
together through `lcompile.py --all`, without errors or warnings (the final cohomology proof takes 15.4 seconds; the assigned item 4.9 seconds).
The packet contains exactly zero holes. The first final dry run required LeanSearch
records in addition to LeanFinder/Loogle and grep; all six new nodes now include actual
LeanSearch results. The extra namespace opening in the assigned module was removed by
qualifying the coefficient type, preserving its original namespace commands. The direct
finite-level comparison import is retained for the unit route.

## New nodes

`lem-weil-pbc-exact-completion-data`: the proved exact pointed completion interface;
its proof uses the existing actual reflector rather than a new Koszul existence theorem.

`def-weil-pbc-uniform-reduction-profile`: the explicit constant-presentation reduction
functor and common bounded constructible cohomology predicate, with no origin condition.

`lem-weil-pbc-uniform-reduction-criterion`: the proved equivalence, including the full
construction and compatible etale normalization argument in its reverse direction.

`lem-weil-pbc-uniform-local-model-cohomology`: the proved forward cohomological
consequence of integral local models. The proof descends an upper bound, uses the
existing integral truncation bound for the lower endpoint, and composes finite local
trivializing covers to descend constructibility. It adds no quotient-resolution obligation.

`lem-weil-constructible-coefficient-homology-triangulated`: the proved derived closure
assembly from abelian kernel, cokernel and extension closure.

`lem-weil-constructible-coefficient-serre`: proved abelian exact closure in the actual
coefficient universe. Canonical constant-section encoding and slice comparisons identify
the predicate with finite-coefficient constructibility; etale origins and exact faithful
comparison transport etale constructible Serre closure. The direct finite-type locally
constant Serre import and its node dependency are no longer needed.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
