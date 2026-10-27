## What changed

Proved the categorical part of reconstructionCommonStageCoherence from the actual
inverse-unit equation. Private proved helpers establish the scalar associator and
unit equations by cancellation, use StageSystem.Morphism.tr_mapAt for arbitrary
representative transport, and descend the actual unit and its inverse using the
proved upstream StageSystem.Morphism API. Chose actual finite-stage realizations
from reconstructionRawRationalNaturality and obtained IdentitySupport from
reconstruction_identityCompactSupport. The original theorem assembles these pieces.

Moved the definitions to PodReconstructionCommonStageData and publicly
reexported them to prevent a dependency cycle with the new scalar normalization
step. Change record: coord/changes/D4-pod-reconstruction-comparison-interface.md.
No existing theorem signature changes. Factored object, representative and Coherence
through the same formulas for an abstract stage system. This avoids expensive
kernel conversion when specializing the generic categorical proof; their meanings
and all original signatures remain definitionally identical. Other definitions
are moved verbatim.

Validation: all three sandbox modules compile together through lcompile.py --all.
The original theorem signature was compared byte-for-byte with the current source.
The generic proof checks without postponed private lemmas or data holes.

## Proved and sorry left

Closed the original hole in
WeilConjectures.PodCommonStageReconstruction.reconstructionCommonStageCoherence
(node lem-pod-reconstruction-common-stage-coherence), by decomposition.
Added one named hole:
WeilConjectures.PodCommonStageReconstruction.reconstructionScalarRealizations
(node lem-pod-reconstruction-scalar-realizations). It only gives the actual
quotient-cone integral/rational scalar comparisons for an already fixed family;
it asserts none of the unit/associator coherence, representative transport,
common-stage functor or natural-isomorphism conclusions.

Thus one original hole closed, one hole added: net zero, a decomposition, not a
complete proof of the whole mathematical result. All existing dependency holes
are untouched. All private categorical helpers contain complete proofs. The data module
has zero holes and introduces no data choices.

## No longer needed

No mathematical dependency or module is withdrawn. All twelve old public imports
are retained by the public data reexport because the existing signatures use their
declarations. Direct proof use of lem-pod-completion-unit-scalar-intertwining moves
to the new scalar normalization step. No source-library declaration is changed.

## Where the brief, the DAG or earlier work was wrong

Step 1 needs a normalization transport omitted by the original plan's assembly:
reconstructionRawRationalNaturality existentially chooses two reconstructions for
one inclusion, while the goal needs one family fixed before all inclusions;
completionUnitScalarIntertwining also existentially chooses its coefficient
calculi instead of taking the supplied family A. The new sublemma isolates exactly
the fixed-family quotient-cone transport and raw localization still needed.

The actual upstream StageSystem.Morphism API already proves representative
transport and functor/natural-transformation descent without strict identity
transitions. It is directly applicable after the associator equation is proved.
Edge cases reviewed: repeated fields, zero objects, arbitrary rational arrows,
ramified inclusions, distinct common-stage representatives and further extension.
Cancellation only uses actual isomorphism components; finite-projection
conservativity and integral lifts of rational arrows are never used.

## New nodes

`def-pod-reconstruction-common-stage-data` attaches the relocated realization
records, actual comparison predicates and common-stage formulas in the new data
module. It also records the generic stageObject, stageRepresentative and
stageCoherence formulas through which their coefficient specializations factor;
it asserts no existence.

`lem-pod-reconstruction-scalar-realizations` states the remaining fixed-family
quotient-cone normalization and localized inverse-unit equations, with a full
proof in words and exact Lean statement. Its two steps retain the dependencies
on actual normalized quotient constructions and raw localization. The original
node's proof now cites it in Step 1; Steps 2–7 keep the same argument and unit route.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
