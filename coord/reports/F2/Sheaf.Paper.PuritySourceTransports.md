## What changed

Proved `WeilConjectures.RationalSmoothPurityCanonical.tensorAugmentation_existsUnique`
from the existing normalized tensor operation unit. Whiskering the natural quotient
completion unit by ordinary total tensor and applying the normalized tensor tower
isomorphism constructs the augmentation. Its prescribed coordinates follow from the
existing quotient-unit and tensor-generator formulas. Pure tensor generation, product
extensionality and the mapping-cocone identity decomposition prove uniqueness.

Added `Sheaf.Paper.StrictTensorAugmentationConstruction` for the construction,
`Sheaf.Paper.StrictTensorAugmentation` for coordinate and extensionality lemmas, and
`Sheaf.Paper.StrictTensorAugmentationNormalization` for the literal coordinate
predicate and fully proved existence-and-uniqueness assembly. The files partition
the complete proof to meet the per-file compile-time limit. The assigned module
imports this support privately. All existing statements and public imports are
preserved, together with every existing definition body.

The existing `commonSource_obj` proof now checks the two recorded object formulas
with `with_reducible_and_instances`, avoiding unnecessary expansion of the common-stage
operation constructions. Local reducibility settings and applying the paired
coordinate theorem directly keep the new proof's elaboration and kernel check small.
The delivered modules contain no profiling or diagnostic commands.

Validation: all four delivered modules pass the server's artifact-producing compile
with the 60-second per-file limit and no diagnostic options. The checked unchanged
consumers QbarCurveDuality, OrientationIntegralCoefficientTwists and
RationalScalarComparisonData also pass.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.RationalSmoothPurityCanonical.tensorAugmentation_existsUnique`.

The original hole
`WeilConjectures.RationalSmoothPurityCanonical.tensorAugmentation_isIso` remains
unchanged, owned by `def-pur-canonical-purity-source-transports`. Its docstring retains
the stratified bounded-flat-model and completeness argument. The completed tensor
comparison lemmas examined require additional geometric hypotheses, so they were not
used to assert this theorem on an arbitrary scheme.

Added zero holes. Every declaration in the new support modules is proved; no remaining
obligation has been renamed or repackaged. This is one hole closed, zero holes split off.

## No longer needed

None of the original imports, modules or node dependencies can be removed: the other
source transports and the existing localization descent still use them. The proof
uses the existing ambient tensor quotient unit and needs no new finite-level tensor
construction. The unit route is preserved. No adopted source-library file is changed.

## Where the brief, the DAG or earlier work was wrong

No statement was changed or disputed. The existing ambient operation models already
construct the required strict tensor unit, so constructing it again from individual
quotient maps is unnecessary. The updated node records that shorter construction and
its uniqueness proof. The isomorphism obligation is independent of the all-complex
construction and uniqueness proved here.

An optional consumer check found a pre-existing time-limit issue in
`Sheaf.Paper.RationalSmoothPurityCanonical`, held by N4. The unchanged consumer
completed without Lean errors but took 90 seconds against this proof-only delivery.
For comparison, the same unchanged file took 81 seconds against the original
published PuritySourceTransports: the sandbox item source was temporarily removed,
so the compile tool ignored its sandbox artifact and used the published dependency.
The consumer was not adapted because the original dependency also exceeds the limit.
All temporary consumer copies were removed from the delivery. No existing statement,
definition body or public import is changed by this delivery.

## New nodes

`lem-pur-strict-tensor-augmentation-construction` records the explicitly constructed
natural transformation and the equation identifying its components with the existing
ambient tensor unit.

`lem-pur-strict-tensor-augmentation-coordinates` records the pure-tensor product
coordinates, vanishing shifted coordinate, and proved pure-tensor and mapping-cocone
extensionality lemmas.

`lem-pur-strict-tensor-augmentation-normalization` records the literal coordinate
predicate and its fully proved existence-and-uniqueness theorem. All new declarations
are proved; the partition adds no hole. The existing node records the complete
argument. Existing statements and definitions are unchanged, so no change record
is needed.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
