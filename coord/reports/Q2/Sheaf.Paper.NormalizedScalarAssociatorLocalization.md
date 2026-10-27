## What changed

The item theorem now composes the canonical rational associator component specification
with a new localization transport theorem.  The proof-only import
`Sheaf.Paper.NormalizedScalarAssociatorLocalizationTransport` supplies the transport
step and publicly imports the intrinsic scalar composition declarations.  The item
node's proof dependencies were updated to record the transport node and the canonical
scalar-composition node.

## Proved and sorry left

The `normalized_scalar_associator_localization` theorem is proved; its original one
`sorry` is closed.  The delivery adds one strictly lower intermediate theorem,
`normalized_scalar_associator_localization_transport`, whose proof remains `sorry` and
is recorded by node `lem-sf-normalized-scalar-associator-localization-transport`.

## No longer needed

None.  The existing public statement import remains required, and the new proof-only
transport import is used by the item proof.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the formal transport interface needed to connect an
arbitrary normalized `ScalarComposition` component with the canonical integral
associator before applying the rational associator's component specification.  This
was isolated as the strictly simpler transport node; the target statement and all
its hypotheses are unchanged.

## New nodes

`lem-sf-normalized-scalar-associator-localization-transport` is stated in
`lean/Sheaf/Paper/NormalizedScalarAssociatorLocalizationTransport.lean` and records the
forward localization transport equality used by the target proof.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
