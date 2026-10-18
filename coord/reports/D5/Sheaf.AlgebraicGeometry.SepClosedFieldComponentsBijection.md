## What changed

Proved `AlgebraicGeometry.bijective_connectedComponentsMap_pullback_fst_of_isSepClosed`.
The proof obtains geometric connectedness of `Spec L → Spec k` from the existing
separably-closed theorem, then applies Mathlib's
`Scheme.Hom.connectedComponentsHomeomorph` to the pullback first projection. Its
`connectedComponentsHomeomorph_apply` lemma identifies the homeomorphism with the
required `connectedComponentsMap`. The item node was updated to record this shorter route.

## Proved and sorry left

The item's sole theorem,
`AlgebraicGeometry.bijective_connectedComponentsMap_pullback_fst_of_isSepClosed`, is proved.
No `sorry` remains and no new `sorry` was added.

## No longer needed

The proof does not need the planned factor swap, explicit singleton connectedness argument,
or any separate fibre-product morphisms. The corresponding planned proof dependencies
`def-pc-field-extension`, `def-weil-affine-spectrum`, `def-weil-connected-scheme`, and
`def-pc-fibre-product` are not imported for the proof; the statement's public imports remain
because its signature uses the relevant scheme and field notions. The direct Mathlib component
homeomorphism makes the factor-swap argument unnecessary.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof plan was substantially longer than necessary. Mathlib already provides
the component homeomorphism for a geometrically connected open morphism, and its pullback
instances apply directly to the first projection. No statement was changed.

## New nodes

None.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
