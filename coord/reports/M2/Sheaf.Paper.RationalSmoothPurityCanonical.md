## What changed

Restored `Sheaf.Paper.RationalSmoothPurityCanonical` from its recorded quarantine
source. Repaired elaboration of the existing finite integration, ordinary unitor,
trace transpose, rationalization, and small coefficient-model composites, preserving
their canonical factors. Added a proof import of `Sheaf.Paper.IntegralResidueTor`.
The changes are recorded in `coord/changes/M2-rational-smooth-purity-elaboration.md`.

## Proved and sorry left

Closed eight of the archived sixteen holes, with no new holes or split statements:
`finiteDualizingPlus`, `orientation_eq_adic`, `pullFiniteTor`, `integralSource_mem`,
`integralMap_eq_adicTraceTranspose`, `representativeTor`, `representative_eq`,
and `modelComposite`, all in
`WeilConjectures.RationalSmoothPurityCanonical`.

Eight original holes remain: `finiteIntegration_smoothPurityMap`,
`orientation_existsUnique`, `smoothPullAugmentation_isIso`,
`smoothPullToOrdinary_existsUnique`, `projection_isIso`, `integralMap_isIso`,
`rationalIntegralSource_eq`, and `rationalIso_scalar`. Each retains its source, proof
in words, and attachment to
`def-pur-canonical-rational-purity-realization`; `rationalIso_scalar` is also attached
to `thm-pur-rational-and-qbar-purity`.

## No longer needed

Removed the unused proof imports
`WeilConjectures.EtaleCohomology.Purity.Smooth.Adic` and
`WeilConjectures.EtaleCohomology.Purity.Smooth.Rational`. No module withdrawn. Both existing node attachments and the unit route are retained.
The proof of `finiteDualizingPlus` uses the existing bounded-below exceptional-image
lemma directly, so it does not require the proposed diagonal-orientation argument.
The finite-Tor membership proofs use the existing integral residue-Tor equality and
operation-preservation theorem; they require no new local Tor-bound construction.

## Where the brief, the DAG or earlier work was wrong

The item is a quarantined restoration, not an unused module. Its six direct consumers
are also quarantined, so a search restricted to live Lean imports would miss them.
The ready-node dependency list contains `lem-pur-common-stage-smooth-operation-identification`
with no Lean attachment. No replacement statement has been introduced for it.

The earlier disk-space failure is no longer present. Focused checks established
that the two rational-stage category structures must be unfolded explicitly once;
otherwise the inclusion tries to compare their full inherited presentations. The
scalar equation also needs the scalar-localization category kept abstract during
elaboration. The complete repaired file compiled successfully in 36.5 seconds.
A subsequent delivery compile exceeded the time limit; caching the tensor
equality separately and pruning two unused imports then passed in 45.4 seconds. No downstream edit is required: all existing interfaces remain definitionally equal, and the
canonical composites retain their original factors.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
