## What changed

Reduced `AlgebraicGeometry.Etale.FiniteRingSectionDeformation.bundleOrientation_frames`
by ambient frame normalization of the integration adjunct followed by a proved formal
restriction of an ambient coefficient square along compatible sections. The item
imports the two new modules privately. Its assembly supplies the actual bundle zero
sections, the proved `bundleFrame_zero` identity, and the actual integration adjunct.
The ambient square uses the compositor indexed by its Cartesian-square equality.
Unfolding the bundle adjoint gives the coefficient-square hypothesis; unfolding the
section maps gives the original conclusion. Existing declarations and definitions keep
their signatures and data. No existing module besides the assigned item is changed.

The three delivery modules compiled in import order. The main assembly subsequently
compiled in 42.1 seconds; both new modules were also below the 60-second per-file limit.
The final delivery reruns compilation after removing the profiling options.

## Proved and sorry left

The item originally contained two holes. The frame hole is reduced, while
`AlgebraicGeometry.Etale.FiniteRingSectionDeformation.coordinate_normalization`
remains unchanged (node `lem-trf-finite-ring-section-deformation`).

The delivery adds one named hole:

- `AlgebraicGeometry.Etale.vectorIntegration_frameAdjoint`
  (`lem-trf-vector-integration-frame-adjoint`): the equality on the ambient frame,
  before restricting to zero.

The new theorem `AlgebraicGeometry.Etale.sectionPullback_coefficient_naturality`
is proved from the source-library section-pasting law, compositor naturality, and
inverse cancellation. Its three private helpers are fully proved. The axiom check reports
exactly
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The item hole
`AlgebraicGeometry.Etale.FiniteRingSectionDeformation.bundleOrientation_frames`
is closed by applying the ambient normalization and this formal theorem.

Thus one upper hole is closed syntactically and one lower hole is added. This is a
decomposition with a proved formal step, not a claimed net hole reduction. There is no
new data definition or arbitrary witness choice. Both new statements have proofs in
words in their docstrings and nodes. Rank zero, empty opens and the zero coefficient
ring satisfy both statements;
the formal section statement needs no invertibility of its coefficient maps.

## No longer needed

The frame proof does not use the existence/uniqueness theorem
`finiteRingBundleSectionOrientation` (`lem-trf-finite-ring-bundle-section-orientation`):
it works on the ambient chart directly from integration normalization. That theorem is
removed from this item's proof dependencies. The original public import remains, so
this delivery does not withdraw its module or alter what importers see. No module is
pruned and no existing import is removed. The coordinate-normalization dependency and
all other original proof inputs remain needed by the untouched obligations and proofs.

## Where the brief, the DAG or earlier work was wrong

The existing bundle-section normalization interface quantifies affine base opens;
`bundleOrientation_frames` quantifies arbitrary Noetherian opens. Its exact equation
also uses the fixed standard zero section. Rather than silently add an affine
hypothesis, the reduction uses the actual integration normalization, which is stated
on every frame, and the already proved identity carrying the standard zero to the
bundle zero. No false statement or target change is proposed.

The source-library adjunction and pullback laws exist and are proved. Directly
specializing their concrete constant-complex and section-compositor definitions caused
expensive conversion checks. The reduction separates ambient normalization from the
proved formal step, rather than duplicating of the original frame statement. The first contains no zero
section, while the second is a formal pullback assertion with no integration map.

## New nodes

`lem-trf-vector-integration-frame-adjoint` is realized by
`Sheaf.AlgebraicGeometry.VectorIntegrationFrameAdjoint`. It extracts the transpose of
integration normalization on the ambient frame, including the actual coefficient-unit
comparison and normalized ordered affine counit. It is strictly the first part of
orientation-charts Step 4.

`lem-trf-section-pullback-coefficient-naturality` is realized by
`Sheaf.AlgebraicGeometry.SectionPullbackCoefficientNaturality`. It extracts the
section-compositor calculation from the second part of Step 4. Its hypotheses give a
square before section restriction, and its conclusion gives the induced square after
restriction. It applies to arbitrary coefficient maps and commuting sections.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
