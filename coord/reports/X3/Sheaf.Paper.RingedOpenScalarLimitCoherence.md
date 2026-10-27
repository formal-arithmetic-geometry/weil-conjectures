## What changed

Repair of returned commit `edea5e8e621` (global-build return of 2026-10-24):
recovered the packet from that commit because the dispatcher sandbox held only metadata.
Compared its parent with current main: the item source and DAG node are identical.
The independent change to `NormalizedLimitSquare.Coherence` replaced its record by
`∃ d : SquareData, SquareLaws d e`. The helper `coherent_normalizations` now eliminates
that existential within its proposition-valued proof, takes comparisons from `d`, and
uses the normalized-square conjunct of its laws. A compatibility tactic branch handles
the preceding record API still exposed by the published compile build. No witness is
selected in a definition. Optional lint re-analysis is disabled to keep the complete
file within the compile bound; elaboration and kernel checks stay enabled. This repairs the invalid `c.comparisonF` projection reported
in `coord/build-errors/Sheaf.Paper.RingedOpenScalarLimitCoherence.txt`.

Proved `AlgebraicGeometry.Scheme.ringedOpenScalarLimitCoherence` in
`Sheaf.Paper.RingedOpenScalarLimitCoherence`. The proof uses the existing ringed scalar/open
adjunction comparison and normalized-limit-square theorem. Private proved calculations transport
the unit/counit equations to complexes and derived towers, establish scalar product preservation
and exact countable products, and recover each individual limit/augmentation equation from the
signed Roos coordinate formula and K-injective normalization.

`CbcLimitNormalized` and `CbcAugmentationCompatible` are now Prop structures with a single
`equation` field equal to their former predicates. Added `cbcComplexSquare`, whose body is the
same `NatIso.mapHomologicalComplex` used before but whose declared type displays composition of
the mapped functors. The theorem uses this wrapper in its two complex equations. The derived
squares, tower adjunction, slice scalar functor, and sheafified generator now refer to the
existing definitionally equal canonical constructions. These API changes avoid repeated large
conversions during elaboration; the full proof first compiled in 49.8 seconds. No theorem of
`lean/Challenge.lean`, source-library declaration, mathematical assumption, or conclusion changed.

Added public imports of `Sheaf.CategoryTheory.RingedOpenScalarAdjunction` and
`Sheaf.Paper.NormalizedLimitSquareCoherence` for the canonical construction aliases. Added proof
imports for exact localization of inverse mates, the reduced closed complement, module-sheaf
Grothendieckness, K-injective resolutions with injective terms, evaluation adjunctions, functor
category exactness, the strict Roos model, and preservation of limits by underlying sheaf functors.
The four temporarily disabled public scalar-exactness instances are restored before the file ends.

Original delivery validation: `lcompile.py --all` compiled the item (52.4 s) and the unchanged
`CompletedOpenEndpointLimitTransport`, `CompletedSupportIntermediateTower`,
`PurStrictIntegralExchangeNormalization`, and `SemilinearOpenClosedComplexSequence` against it,
with no errors or warnings. Consumer copies were removed after this check.

Repair validation: the complete repaired item compiled without errors (51.2 s).
A scratch test copying the new `SquareData`, `SquareLaws`, and `Coherence` interface
verified the existential elimination, comparison projections, and exact sixth law
(19.6 s). Attempts to compile the unchanged full dependency or to serialize the full
item for consumer tests hit the 60-second bound; they are not claimed as passes.
The public interface and all definitions are unchanged from the original packet,
whose four unchanged consumer checks are recorded above. Diagnostic files are excluded.

Definition and consumer review: `coord/changes/X3-ringed-open-scalar-limit-coherence.md`.
Updated the existing DAG node's proof, proof dependencies, proof origin, and Lean attachment to
match this implementation. The unit's route is retained. No source-library file is edited.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.ringedOpenScalarLimitCoherence`
(node `lem-cbc-ringed-open-scalar-limit-coherence`).

Holes closed against current main: 1 of 1. Holes added: 0. Split off: 0.
The returned packet already had zero holes; this repair preserves that actual count of zero.
No `sorry` remains in the delivered Lean file.
Every new private helper is proved. Existing declared dependencies, including
`CategoryTheory.NormalizedLimitSquare.normalizedLimitSquareCoherence`, are used as the stage-3
brief requires; their remaining proofs are not duplicated or moved into this delivery.

## No longer needed

No module is withdrawn and no library declaration is deleted. No original public import is
removed. The proof does not call `CategoryTheory.exactProductFunctorStrictLimit` separately:
the existing normalized-square theorem already supplies its comparisons and signed normalization;
that module remains needed through the normalized-square dependency and the existing public API.
The weakly-etale localization lemma is not separately applied because the theorem already uses
the literal slice presentation; its statement dependency and import remain. The sectionwise-limit
node is replaced as a direct proof dependency by the stronger existing underlying-sheaf
preservation theorem `CategoryTheory.moduleSheaves_colimits_forgetful`; Mathlib's actual
module-sheaf limit instances remain in use. Thus there is no claim that any of these modules
has become globally unnecessary.

No new intermediate statements or modules are left for other workers. Temporary diagnostic files
and unchanged consumer copies are excluded from the delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier proof assumed that `Coherence` remained a record. The dependency's
landed representation repair made that assumption invalid; its mathematical existence
statement and the four comparisons are preserved. The repair unpacks the existential
and uses the sixth `SquareLaws` conjunct rather than a record projection.

The normalized-square theorem gives a corner's unit normalization on degreewise-injective
K-injective complexes, whereas this item's predicate asks for every complex. The missing glue
is naturality along a functorial K-injective resolution and cancellation of its invertible Roos
image. The individual augmentation equations then follow from these unit equations and the
ordinary-limit universal property; they do not require an additional theorem or hypothesis.

The original direct `NatIso.mapHomologicalComplex e` expressions in the concrete theorem force
Lean to compare a mapped composite with a composite of mapped functors. Profiling exposed this
conversion as the single-file time-limit bottleneck. `cbcComplexSquare` supplies the same map
with the intended type already checked in abstract categories. The previous large normalization
predicate definitions also unfolded repeatedly; their one-field structures expose exactly the
same equations through a small API.

For exact countable products on the slice, the Lean argument uses the existing ringed
open/closed adjunction and the reduced closed complement to transfer the ambient result; it
does not assume that the slice category has already been identified with a different scheme's
pro-etale module category. The DAG now records these actual dependencies.

The original node cites a legacy `lem-cbc-completed-extension-zero-comparison.proof.md` path
that is absent from `literature/blueprint/latest`. The current unit and its exact-functor/derived-
limit proof were read. The assigned scalar/open statement is retained, and the implementation
is supported by its existing Stacks sources and declared normalized-square dependency. No
withdrawal is inferred from the missing legacy path.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
