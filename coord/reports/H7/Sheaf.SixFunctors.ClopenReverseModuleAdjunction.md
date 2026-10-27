## What changed

Proved `SheafOfModules.ClopenComparisonTensorSquare.clopen_reverse_module_adjunction`
in `Sheaf.SixFunctors.ClopenReverseModuleAdjunction`, with its statement unchanged.
The extension is the actual sectionwise direct image. Its additional left adjunction
is constructed by inverting the two-component restriction map and inserting zero
on the complementary open. Naturality is proved for both site morphisms and module
morphisms. The vertical-site case restricts the given ring and module to each
vertical slice; it retains arbitrary semilinear coefficient transitions.

Added only proved private helpers and private proof imports of
`Sheaf.SixFunctors.OpenOperationModels`,
`Sheaf.SixFunctors.OpenTensorNormalizationData`, and
`Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing`.
Updated the item's DAG proof, proof dependencies, and proof origin to describe the
explicit section construction and the two adjunction triangle calculations.
No other existing module or node is changed. No shared definition, statement,
attribute, instance, or public import is changed.

The additional generic tools are `lem-sf-open-operation-models` (the concrete
restriction/direct-image adjunction) and `def-sf-open-normalization-data` (the
ordinary and vertical sites and their topology). They are the existing interfaces
for the same operations, not replacement routes for a blueprint unit.

## Proved and sorry left

Closed the one original hole in
`SheafOfModules.ClopenComparisonTensorSquare.clopen_reverse_module_adjunction`
(node `lem-sf-clopen-reverse-module-adjunction`).
Holes closed: 1. Holes added: 0. Holes left in the item: 0.
No statements were split off. All added private helpers are completely proved.
Server compilation passed in 23.8 seconds, without warnings. A temporary
`#print axioms` reported exactly `propext`, `Classical.choice`, and `Quot.sound`;
the diagnostic command was removed from the delivery.

## No longer needed

None: no module or node is withdrawn and no original dependency is pruned.
Both original proof dependencies, `lem-pur-clopen-ringed-module-gluing` and
`def-coef-semilinear-system-models`, remain used. The proof uses the proved
section-bijection part of clopen gluing rather than reconstructing its entire
product equivalence. Every added proof import supplies declarations used by the
proof; the original public import is retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The planned gluing argument works on
the vertical site by continuous restriction to its slices. The existing
`clopenScalarRestrictionReverseAdjunction` cannot be reused here: its proof
already calls this item, so that route would be circular. The explicit section
construction avoids that cycle. Empty selected components and empty complementary
components are covered by the sheaf empty-section argument, with no nonemptiness
assumptions.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
