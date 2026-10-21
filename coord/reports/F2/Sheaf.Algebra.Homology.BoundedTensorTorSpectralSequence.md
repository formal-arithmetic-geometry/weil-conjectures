## What changed

Restored `Sheaf.Algebra.Homology.BoundedTensorTorSpectralSequence` from its
`coord/rework.tsv` quarantine source and proved
`DerivedCategory.bounded_tensor_tor_spectral_sequence`. Its statement, three existing
public definitions, and public imports are unchanged. No source-library module,
existing definition, target, or unit route is changed.

The proof now assembles the existing canonical filtration, localized convolution and
normalized filtered-page declarations through eight new, proved supporting modules:

- `KunnethSpectralSequenceReindex`: reindexes pages by `(p,q) ↦ (-q,p+2q)` and
  `r ↦ r-1`, including homology, cycles, differential and successor compatibility.
- `LocalizedFilteredConvergence`: transports normalized convergence to all localized
  objects and maps. It also proves the filtered step, graded-map and finiteness APIs.
- `DerivedTensorModuleTorComparison`: computes the derived tensor cohomology of two
  single modules from a projective resolution, naturally in both module variables;
  treats negative Tor indices by cohomological vanishing.
- `KunnethCanonicalTensorData`: constructs compatible canonical lift, forgetful,
  graded and convolution data from the existing localization declarations.
- `KunnethCanonicalGradedCohomology`: proves the finite-support cohomology calculation,
  independence under support enlargement, naturality on the union of two supports,
  tensor-shift naturality, and reindexing onto the diagonal coproduct.
- `KunnethCanonicalGradedTensor`: combines that calculation with the normalized
  convolution tensor comparison.
- `KunnethCanonicalFirstPage`: descends the cohomology and first-page comparisons and
  transports the filtration by an actual module isomorphism.
- `KunnethFilteredFirstPage`: identifies the canonical first page with Tor using the
  proved natural bifunctor isomorphism.

The item shifts the abutment filtration by `p-n`, constructs the graded quotient
isomorphism explicitly, and proves finite bounds, stationary vanishing, successor
coherence, step/projection compatibility, and naturality in both derived arguments.
Every new supporting result is proved; none is merely a renamed clause with a hole.

All nine submitted Lean modules were compiled together in dependency order on the
project server. The delivery runs the independent compile and preflight checks.

## Proved and sorry left

Closed the original one hole:
`DerivedCategory.bounded_tensor_tor_spectral_sequence`.

Holes closed: 1 of 1. Holes added: 0. Holes split off: 0. Every submitted Lean module
has zero `sorry`, including every private helper and every definition. The principal
new proved results are `CategoryTheory.kunnethReindex_successor`,
`CategoryTheory.localizedFilteredConvergence`,
`DerivedCategory.kunnethModuleTensorHomology_tor`,
`DerivedCategory.exists_kunnethCanonicalTensorData`,
`DerivedCategory.kunnethCanonicalGradedCohomology`,
`DerivedCategory.exists_kunnethCanonicalGradedTensor`,
`DerivedCategory.exists_kunnethCanonicalFirstPage`, and
`DerivedCategory.exists_kunnethFilteredFirstPage`.

These are proofs from the existing declared dependencies, as required at stage 3;
this report does not claim to close holes already present in those dependencies.

## No longer needed

Removed the following direct proof imports from the quarantined item:

- `Mathlib.Algebra.Homology.DerivedCategory.Fractions`
- `Sheaf.Algebra.Homology.DerivedCanonicalFiltration`
- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`
- `Sheaf.Algebra.Homology.FilteredTensorGradedComparison`
- `Sheaf.Algebra.Homology.FilteredTensorLocalization`
- `Sheaf.Algebra.Homology.FiniteFilteredKFlatReplacement`
- `Sheaf.CategoryTheory.BoundedFilteredComplexPageCore`
- `WeilConjectures.Algebra.Homology.BoundedFlatKFlat`

The item needs only its original public imports and the four private imports of
`KunnethSpectralSequenceReindex`, `LocalizedFilteredConvergence`,
`KunnethFilteredFirstPage`, and the existing `FilteredPageLocalization`.

No existing node or module is withdrawn or claimed globally prunable. The old
canonical filtration and convolution dependencies are still needed through the new
proved comparisons; their lower K-flat and filtered-page dependencies remain needed
by those declarations. The DAG now records the intermediate results the actual proof
uses, rather than importing all lower modules directly into the item.

## Where the brief, the DAG or earlier work was wrong

The item is quarantined, not withdrawn; its archive was restored with its public
interface intact. No statement was found false, and no weakening or additional
hypothesis was required.

The conceptual DAG plan needed explicit Lean glue for normalized localization
comparisons, simultaneous Tor naturality, finite-support coproducts, tensor shifts,
and coherent stationary reindexing. The new proved nodes record this glue. Choosing
supports does not define arbitrary mathematical data: the maps agree under support
enlargement, and their naturality is proved on the union of supports. The normalized
localization record is constructed from the existing declared constructions.

No forced adaptation is needed: no existing mathematical interface is changed,
and no module held by another group is edited. All new modules are under `Sheaf`.
The first server preflight identified the required `mathlib_searches` field name and
classified proof-checking commands as an interface change. The search records now
use that field. The next preflight distinguished LeanSearch from the shared
Loogle/LeanFinder search kind; all eight nodes now also record an actual successful
LeanSearch query and its inspected results. None supplies the combined result.
`coord/changes/bounded-tensor-tor-proof-scoping.md` documents the
checking commands, unchanged theorem signature and unaffected archived consumer.

## New nodes

`lem-kun-spectral-sequence-reindex`: the lattice/page reindexing with cycles, homology,
differentials and coherent successor comparison; proved in
`KunnethSpectralSequenceReindex`.

`lem-kun-localized-filtered-convergence`: coherent finite filtered convergence and its
naturality on the localized category; proved in `LocalizedFilteredConvergence`.

`lem-kun-derived-module-tor-comparison`: derived single-module tensor cohomology is
naturally the Tor bifunctor, with its negative-index zero convention; proved in
`DerivedTensorModuleTorComparison`.

`lem-kun-canonical-tensor-data`: normalized canonical lift and convolution comparisons,
including finite support and its extension equations; constructed in
`KunnethCanonicalTensorData`.

`lem-kun-canonical-graded-cohomology`: the finite graded convolution cohomology formula
and its two-variable map equation; proved in `KunnethCanonicalGradedCohomology`.

`lem-kun-canonical-graded-tensor`: the normalized convolution realization together with
the proved graded cohomology comparison; proved in `KunnethCanonicalGradedTensor`.

`lem-kun-canonical-filtered-first-page`: the filtered cohomology realization and first
page before identification with Tor; proved in `KunnethCanonicalFirstPage`.

`lem-kun-filtered-first-page`: the natural Tor first page, without duplicating
convergence or stationary identifications; proved in `KunnethFilteredFirstPage`.

All eight nodes have Lean attachments, source proof steps and three kinds of Mathlib
search. Change record: `coord/changes/bounded-tensor-tor-proof-scoping.md` (proof-checking
commands only; no mathematical interface change).

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
