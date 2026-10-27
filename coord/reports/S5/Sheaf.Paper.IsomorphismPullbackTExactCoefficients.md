## What changed

Reduced `WeilConjectures.isomorphismPullback_tExact_coefficients` to four separate
mathematical steps: a normalized exact and t-exact finite coefficient stage,
compatibility of the specified scalar comparison with the normalized shifts,
and the unit and tower equations. The target constructs its stage packages
field by field, assembles the integral natural comparison using the existing
`specifiedPullbackComparisonAlpha` naturality theorem, retains the prescribed
rational comparison, and applies the unit and tower equations to that same normalized natural-isomorphism
family. Those lemmas accept the component-normalization proof explicitly; their rational
clauses retain the prescribed maps and canonical adapters. Existing public definitions remain in the
item module and the target signature is unchanged. A definitionally equal coefficient
inclusion cache in `Sheaf.Paper.IsomorphismCoefficientInclusions` makes the
field-induced semiring structures explicit and avoids repeated structure comparison.
The item and the scalar-shift, unit-law and tower-law statements use that same
presentation consistently. The original integral unitor and associator now alias their identical shared
definitions in the cache module, so the smaller coherence statements use exactly
the same structural maps. The cache module adds no instance or axiom, and proves its
identity/composition API directly from the existing laws. Its change record lists
transitive consumers.

The finite-stage module now proves the normalized inverse-image comparison,
integral linearity and exactness, and both integral and rational standard-half
preservation. Only its rational normalized exactness is isolated as a smaller
remaining statement. The earlier full proof candidate and subsequent focused calculations are retained
in the scratchpad. Focused checks proved the integral scalar shift calculation and
the integral and rational unit/tower equations for ordinary finite coefficient fields.
Transporting the latter through the actual small-model inclusions hit kernel timeouts;
the delivered unit and tower statements retain those transport steps as remaining work.
The remaining rational shift and small-model coherence calculations were not
completed. A direct rational-exactness experiment still exceeded kernel-checking
time and is retained only in the scratchpad; it is not counted as a proof. The delivery is a
mathematical decomposition, not a claim of net hole reduction. The remaining statements
include complete proof plans and edge-case checks in their docstrings and nodes.
Transparency checks remain enabled.

The complete item assembly compiled successfully in 45.6 seconds, within the
60-second limit. Its named existence proof avoids generated proof declarations
from a private data definition. Profiler commands and diagnostic markers have
been removed. All seven cleaned modules compiled in the required delivery run. Its preflight
returned three recorded-signature mismatches, now corrected using the project
declaration parser; the Lean sources did not change. The additional LeanSearch
query also completes the three search categories in the new-node records. Final
preflight and push are pending. The generic coherence calculations are not counted as closed
packet holes: the actual small-model unit and tower theorems still contain `sorry`.

## Proved and sorry left

Replaced the one original hole, in
`WeilConjectures.isomorphismPullback_tExact_coefficients`, by a complete Lean
assembly from the four smaller statements (compiled successfully).

Four holes remain, one named public theorem per module:

- `WeilConjectures.isomorphismPullbackRationalExact`
  (`lem-pod-isomorphism-pullback-rational-exact`).
- `WeilConjectures.isomorphismPullbackScalarShift`
  (`lem-pod-isomorphism-pullback-scalar-shift`).
- `WeilConjectures.isomorphismPullbackUnitLaws`
  (`lem-pod-isomorphism-pullback-unit-laws`).
- `WeilConjectures.isomorphismPullbackTowerLaws`
  (`lem-pod-isomorphism-pullback-tower-laws`).

Also proved the new `WeilConjectures.isomorphismPullbackRawStage` from its integral
construction, standard-half arguments and `isomorphismPullbackRationalExact`
(the two modules compiled together). The item itself has zero `sorry`; the packet has four. This is a decomposition
of one upper hole into four strictly smaller argument steps, net minus three.
No definition contains a hole and no arbitrary data is defined by choosing an
unproved existence witness. Stage witnesses are eliminated inside the target's
existence proof.

## No longer needed

The target directly imports the finite-stage, scalar-shift, unit-law and tower-law
modules and
`Sheaf.Paper.SpecifiedPullbackComparisonAlpha`. Removed its old proof-only direct
imports of `IsomorphismDerivedPullback`, `IsoSectionwiseInverseImage`,
`ScalarExtensionRingIso`, `IsomorphismDerivedPullbackComparisonNormalization`,
`IntegralTStructure`, `LocalizedTStructure`, `IntegralOperationsScalarComparisons`,
`IntegralPullbackComparisonRealization`, `FiniteFreeCompletedScalarComparison`,
`SemilinearScalarLocalization`, and `ExtensionIntegersDvr`.

The proved raw-stage node uses exact inverse image, reconstruction comparison,
standard-half preservation and the separate rational-exactness step; that remaining
step retains semilinear localization. The scalar-shift node
retains the normalized inverse-image scalar square. The unit and tower nodes
retain simultaneous comparison realization and its agreement with the specified
alpha. Thus these are direct import removals, not a claim that all corresponding
mathematics is globally unnecessary. No module is withdrawn.
The new supporting modules omit the copied legacy `PbcScalarExtension` and
`IntegralScalarExtensionUniverses` imports. Only the finite-stage statement imports
`SfConstructibleHeart`; only that statement and the scalar-shift statement import
`InverseImagePullbackComparisonDerived`. The shared cache imports
`GeneralAlgebraicallyClosedCoefficients`, whose public closure already contains
`SfScalarExtensionComposition`.

Removed obsolete parent `tool_uses` entries for
`lem-weil-sheaf-scalar-extension-ring-iso`, `lem-weil-isomorphism-derived-pullback`,
`lem-weil-pbc-exact-functor-derived-factorization`, `prop-weil-pbc-integral-tstructure`,
`lem-trf-integral-pullback-comparison-realization`, `prop-weil-pbc-scalar-extension`,
`prop-weil-localized-tstructure`, and `lem-weil-l-adic-extension-integers-dvr`.
The finite-stage proof records the inverse-image, realization and derived-factorization
work in its own node. The canonical scalar laws retain the realization and completion
work in their nodes. The obsolete t-structure and fresh DVR reconstruction routes
are not used.


The prescribed rational comparison already supplies rational naturality and its
integral components. Reconstructing that comparison using a fresh uniformizer
inversion argument is unnecessary; the old direct DVR dependency is omitted.
The older etale-origin t-structure interfaces are not used: the statements use
the intrinsic standard-half predicates already present in the parent.

## Where the brief, the DAG or earlier work was wrong

No statement dispute. The current blueprint locates the cited truncation proof at
`sec-poincare-duality/sk-thm-frobenius/prop-constructible-truncations.proof.md`;
new-node sources and proof origins use that current path. The parent historical
source record and target statement are retained. The restored earlier candidate was not a validated proof:
its zero textual holes did not imply it compiled. The remaining issues involved
rational localization transport and expensive comparisons of coefficient-model
instances. The original public names and types remain in the item module. The identical
integral adapters are factored into shared definitions, with the original names
aliasing them as described in the change record; no mathematical data changes. The unit route is
unchanged (`sk-lem-finite` has no realized nodes).

## New nodes

`lem-pod-isomorphism-pullback-raw-stage` gives only one finite coefficient stage,
without scalar comparisons or their coherence. Its raw statement is independent
of the item module and constructs no arbitrary public data.

`lem-pod-isomorphism-pullback-rational-exact` supplies only the normalized rational
shift and triangulation, assuming the integral shift, linearity and triangulation.
It neither constructs an integral comparison nor proves any standard-half preservation.
The finite-stage module proves the remaining clauses.

`lem-pod-isomorphism-pullback-scalar-shift` gives only shift compatibility for a
specified scalar comparison and specified normalized endpoint shifts. It neither
constructs endpoint stages nor proves their exactness or t-exactness.

`lem-pod-isomorphism-pullback-unit-laws` gives the integral and rational unit
equations for the prescribed maps at the actual small coefficient models.
Its integral unit is explicitly transported through the inclusion identity, and its
rational unit is the existing canonical unitor. It has no stage or shift existence conclusion.

`lem-pod-isomorphism-pullback-tower-laws` gives the corresponding two tower
equations for three finite subextensions and their actual small coefficient inclusions.
Its integral associator includes the coefficient composition equality and its rational
associator is the prescribed canonical one. It has no stage,
comparison or shift existence conclusion. Both coherence lemmas accept an integral
natural-isomorphism family and its prescribed component normalizations. This is the
family the target constructs; the additional parameters avoid a costly component
conversion in the target, without adding a hypothesis to the target statement.
The definitionally equal interface repair is recorded at
`coord/changes/isomorphism-coefficient-inclusion-cache.md`.

`def-pod-isomorphism-coefficient-inclusions` records the definitionally equal shared
presentation of the existing small coefficient inclusions and the proved identity and
composition API, and the existing normalized integral unitor and associator.
The item retains the original public adapter names as aliases. It contains no hole. It keeps the same field-induced algebra structures
through the scalar-shift and coherence statements and the target assembly.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
