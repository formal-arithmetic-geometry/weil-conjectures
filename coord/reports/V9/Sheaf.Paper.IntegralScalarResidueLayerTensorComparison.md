## What changed

Proved `WeilConjectures.integralScalarResidueLayerTensorComparison` with its
statement unchanged. The proof constructs an actual cochain-complex isomorphism
and applies `DerivedCategory.Q.mapIso`.

The existing proved `integralScalarResidueCoefficientIso` supplies the coefficient
layer, and `integralScalarResidue_triangle` supplies the coefficient square.
Natural sheaf tensor cancellation, symmetry and the tensor unitor identify the
filtered tensor with residue extension followed by restriction. Composition of
scalar restrictions and uniqueness of left adjoints compare the two paths in the
coefficient square. The ordinary source-reduction adjunction identifies the
prescribed reduction functor. Naturality on differentials completes the complex
isomorphism. All new helpers are private and proved.

Updated the item's DAG proof and proof dependencies to record this route.
No existing statement, definition, or consumer was changed.
The existing public imports are retained. Added proof imports expose the already
proved coefficient comparison, tensor cancellation, tensor presentation, and
ordinary scalar-extension adjunction interface.

Validation: the remote single-file compile passed in 22.1 seconds. The public
theorem statement is byte-for-byte unchanged, and the module contains no `sorry`.

## Proved and sorry left

Closed 1 existing hole:
`WeilConjectures.integralScalarResidueLayerTensorComparison`
(node `lem-sf-integral-scalar-residue-layer-tensor-comparison`).

Added 0 holes; split off 0 statements. The item's module has 0 remaining holes.
There are no new modules or new nodes.

## No longer needed

No existing import is removed. The public scalar-extension import is retained
for the statement's coefficient and reduction interface and its instances.

The arithmetic computation is reused from
`Sheaf.Paper.IntegralScalarResidueCoefficientIso`; it is not repeated or split.
Thus `lem-weil-l-adic-extension-integers-dvr` and
`lem-weil-integral-scalar-extension-well-defined` are no longer direct proof
obligations of this node. They remain dependencies of the reused coefficient
comparison; no claim is made that their modules leave the targets' closure.

The proof does not use a derived change-of-rings computation, a K-flat resolution,
or constructibility bounds. The old direct edge to
`lem-pur-derived-change-of-rings` is replaced by the ordinary adjunction and
natural tensor-cancellation edges. The definitions from
`lem-sf-filtered-coefficient-tensor-bounds` remain necessary to identify the exact
complex in the statement. No library module is withdrawn.
`def-weil-integral-scalar-extension` remains a statement dependency, rather than
a separate proof obligation; its public import and definitions are retained.

## Where the brief, the DAG or earlier work was wrong

The proposed arithmetic and coefficient compatibility steps had already been
proved in `Sheaf.Paper.IntegralScalarResidueCoefficientIso`, which the item's
original proof dependencies did not list. They apply with exactly the recorded
finite quotient action. No additional arithmetic statement is necessary.
The tensor assembly requires only ordinary scalar-extension adjunctions and
naturality, so it can be performed before passage to the derived category.
The unit route is unchanged (`sk-def-sf-operations` has no realized step carried
by this item).

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
