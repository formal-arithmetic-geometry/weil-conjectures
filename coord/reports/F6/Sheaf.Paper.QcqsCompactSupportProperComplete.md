## What changed

Proved `WeilConjectures.sfQcqsCompactSupport_proper_complete` in
`Sheaf.Paper.QcqsCompactSupportProperComplete`. The defining coefficient
adjunction identifies its ringed module pushforward with
`sfCompletedModuleDirectImage`. The existing proved `completed_image_complete`
helper in `SfCompleteDirectImageReduction` then applies to the normalized
`CompletedCoefficientPushforward.ComparisonData` for the proper factor.
An auxiliary prime distinct from l supplies the comparison package and imposes
no new hypothesis on the theorem. Added only private proof imports of
`SfCompleteDirectImageReduction`, `CompletedCoefficientPushforwardComparison`
and `Mathlib.Data.Nat.Prime.Infinite`. The existing `complete_iso` helper
transports completeness across `Functor.rightDerivedFunctorNatIso` of the
ordinary functor equality. Updated the item's proof plan and dependencies.
The two broad comparison-model
instances are disabled only while elaborating this theorem, using a scoped
`attribute ... in` command; no imported instance declaration is changed. The
unused-section-variable linter is disabled only for this theorem to retain its
original geometric binders while using the arbitrary-morphism argument.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.sfQcqsCompactSupport_proper_complete`
(node `lem-qcqs-compact-support-image-complete-proper`).
No holes remain in the item; no holes or split-off statements were added.
All theorem binders and its conclusion are unchanged. Remote single-file
compilation passed in 3.1 seconds. The delivery compile also checks the proof
with the axiom probe. The preserved geometric section hypotheses are unused by
this general argument; its warning is locally suppressed without omitting any binder.

## No longer needed

No modules or nodes are withdrawn, and no original public imports are removed.
The original standalone Roos-triangle transport argument need not be rebuilt:
the existing arbitrary-morphism completed-image completeness proof already
supplies it. The original node had no declared proof dependencies to prune.
The blueprint unit has no realized statement or steps affected by this reuse.

## Where the brief, the DAG or earlier work was wrong

The original node's empty dependency list missed the already proved
completed-image completeness helper in `SfCompleteDirectImageReduction`.
The proper factor requires no additional geometric argument: the existing
completeness proof applies to every scheme morphism.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
