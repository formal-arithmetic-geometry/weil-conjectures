## What changed

Filled the six supporting instance proofs in
`Sheaf.CategoryTheory.InternalSectionTensorComparison`, preserving every declaration
signature and public import. No definitions or statements changed.

Essential smallness follows by projecting the supplied universe bound to the
object and Hom universes. Tensor-left colimit preservation specializes the
existing sheaf-tensor properties theorem; tensor-right preservation follows by
braiding. Colimits of internal modules transfer through the existing section
module equivalence. That equivalence is additive because it preserves binary
products. Finally, the colimit instance supplies each coproduct in the total
tensor directly, avoiding a large typeclass search over the expanded bifunctor.

The compile server verified these proofs. A larger attempted adaptation of the
private tensor construction in `InternalSectionModuleFlat` was removed; none of
its experimental helpers or imports is delivered.

## Proved and sorry left

Closed six of the seven existing holes:

- `CategoryTheory.InternalAbelianSheafModule.comparison_essentiallySmall`.
- `CategoryTheory.InternalAbelianSheafModule.comparison_sheafTensorLeft`.
- `CategoryTheory.InternalAbelianSheafModule.comparison_sheafTensorRight`.
- `CategoryTheory.InternalAbelianSheafModule.comparison_internalColimits`.
- `CategoryTheory.InternalAbelianSheafModule.comparison_additive`.
- `CategoryTheory.InternalAbelianSheafModule.comparison_internalTotalExists`.

One existing hole remains unchanged:
`CategoryTheory.InternalAbelianSheafModule.internal_section_tensor_comparison`
(node `lem-pe-internal-section-tensor-comparison`). Its original source and complete
proof plan remain in its docstring. No holes were added or split off. This is a
partial proof delivery of the module, not a proof of its main comparison theorem.

## No longer needed

None. The original imports and the main theorem's dependency plan are retained.
No module is withdrawn and no dependency node is declared obsolete. Removing all
private imports together made instance elaboration exceed the file gate, so that
attempted pruning is not included.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The supporting additivity proof can use the general
Mathlib theorem about functors preserving binary products, without a sectionwise
calculation. Colimits similarly transfer along the equivalence directly, without
an explicit new coproduct construction.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
