## What changed

Filled five theorem proofs in `Sheaf.Paper.PuritySourceTransports`, preserving every
mathematical statement, comparison value and public import. Added the public
predicate `TensorAugmentationNormalized` for the identical two Roos-coordinate
conditions already present in `tensorAugmentation_existsUnique`; attached it to
the existing definition node. Added explicit unchanged return types for
`tensorAugmentation` and `ordinaryModel`. Local instance priorities,
transparency settings and generation/linter options keep large constructions
folded during elaboration. These settings do not change downstream behavior. The proofs follow the existing
docstrings; the definition node has no alternative proof route to update.

- `lineScalarIntegral_existsUnique` uses the object clause of
  `sfRationalScalarExtension_existsUnique`, lifts `lineScalarAmbient` into the
  intrinsic full subcategory, and proves uniqueness by faithfulness.
- `base_le` is the bottom intermediate-field inequality.
- `commonSource_obj` combines the prescribed object clauses of
  `commonStageDerivedPullback_existsUnique` and
  `commonStageDerivedTensor_existsUnique`.
- `commonSource_stage` is the supremum inequality for bottom and the input stage.
- `goodOrdinary` uses the definitional agreement of the two K-flat predicates
  and their identical flat-term conjuncts.

Read the current rational-purity proof and the unit record `sk-lem-finite`.
The unit route and the actual comparison maps remain intact. Searches used
Lean Finder, Loogle (`bot_le`), the launcher grep service, and direct source
searches. No specialized replacement for the remaining completion construction
was found.

## Proved and sorry left

Five of ten original holes closed, no holes added, no split-off statements.
The five declarations proved are listed above, all in namespace
`WeilConjectures.RationalSmoothPurityCanonical`.

Five original named theorem holes remain unchanged, all attached to
`def-pur-canonical-purity-source-transports`:

- `WeilConjectures.RationalSmoothPurityCanonical.scalarShift_existsUnique`
- `WeilConjectures.RationalSmoothPurityCanonical.tensorAugmentation_existsUnique`
- `WeilConjectures.RationalSmoothPurityCanonical.ordinaryModel_existsUnique`
- `WeilConjectures.RationalSmoothPurityCanonical.tensorAugmentation_isIso`
- `WeilConjectures.RationalSmoothPurityCanonical.tensorToOrdinary_existsUnique`

The common-source proof uses the existing named object specifications even
though their proofs remain work in their owning modules. The line comparison
still depends on the recorded scalar-completion isomorphism. This delivery does
not assert that the complete transitive axiom closure is already sorry-free.

## No longer needed

None. Both public imports still supply statements and constructions of the
module. No module or DAG dependency is withdrawn, and no proof imports are added.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The item node is a definition
node with an empty proof plan; the theorem docstrings supply the local arguments
implemented here. Profiling exposed expensive repeated checking of inline
normalization and selected-witness types. Naming the identical normalization
predicate and annotating return types repaired the timeout without changing
any object or comparison map. The remaining five construction and descent obligations are
left as their existing named theorems with source and proof docstrings.

Change records:

- `coord/changes/T3-purity-source-augmentation-normalization.md`
- `coord/changes/T3-purity-source-tensorAugmentation-return-type.md`
- `coord/changes/T3-purity-source-ordinaryModel-return-type.md`

Validation: the full module compiled through the prescribed launcher in 56.8
seconds; its sole whitespace warning was then corrected. The final delivery
runs the independent server compilation and preflight.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
