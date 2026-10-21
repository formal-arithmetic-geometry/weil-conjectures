## What changed

`SystemTensorMateArrows` constructs the ordinary operations from the existing
semilinear calculus and canonical varying-ring adjoints. For each map it obtains
the normalized tensor comparison from `VaryingRingTensorComparison` and assembles
the full package. Equality of the two direct-image presentations acts by casts between
definitionally equal section carriers; proof irrelevance removes those casts.

The open unit descends from the ordinary category. The specified `deltaInv` is
proved invertible by expressing its transpose as extension of an invertible
adjunct followed by the counit. The counit is invertible because the tensor
target is supported on the open. Adjoint uniqueness transports support from
canonical varying-ring extension to the supplied extension.

All three modules compile through `lcompile.py --all`; the profiled complete
item compiled in 47.7 seconds without errors or warnings. Profiling options
were then removed.

All existing public signatures, definitions and public imports are preserved.
Two new proof imports supply separate geometric construction results.
The local transparency commands are recorded in
`coord/changes/R3-system-tensor-mate-proof-scopes.md`; they affect proof
elaboration only and require no consumer adaptation.

## Proved and sorry left

The two original holes have complete assembly proofs:
`WeilConjectures.SystemTensorMate.tensorOperations_nonempty` and
`WeilConjectures.SystemTensorMate.TensorOperations.deltaInv_isIso`.
The item module contains zero `sorry`.

Two holes are added, each in its own module and DAG node:

- `AlgebraicGeometry.ProEtale.VaryingRing.tensorComparison_exists`
  (`lem-pur-varying-ring-tensor-comparison`): the ordinary-unit-normalized
  comparison and its signed-total K-flat model for one fixed inverse image.
- `AlgebraicGeometry.ProEtale.VaryingRing.tensor_openSupported`
  (`lem-pur-varying-ring-tensor-support`): essential-image membership for an
  ambient tensor, without a tensor projection morphism or its normalization.

This is a decomposition: two original holes closed, two separate holes added,
net zero. The tensor comparison result supplies no ordinary operation family or
open extension; those are constructed in the item. The support result supplies
no projection morphism; its relation to the specified transpose is proved in the
item. Neither lemma assumes the conclusion of the item. The empty and identity
opens and arbitrary, potentially nonflat coefficient transitions satisfy both
statements.

## No longer needed

None. No existing import, node, module, declaration or unit step is withdrawn.
The original open-normalization module remains needed for the public exact
derived adjunction. Both new modules are private proof imports of the item.

## Where the brief, the DAG or earlier work was wrong

The existing open-support interface uses the literal restricted coefficient
ring and a simultaneous geometric operation record. The item instead uses
canonical constant-ring towers and arbitrary universal adjoints. A bridge
between these presentations is needed before applying that interface.
The one-map tensor bridge similarly retains the ordinary unit equation and
actual signed-total representative normalization; an abstract tensor isomorphism
alone would not fill the package fields.

A read-only dependency audit found the pre-existing cycle
`lem-weil-pbc-derived-exchange-termwise` →
`lem-weil-pbc-derived-exchange-bounded-comparison` →
`lemma-weil-pbc-derived-exchange-replacement` → the first node, and a reference
to missing `def-weil-pbc-ideal-module-product-stalk`. These records are outside
this delivery. Neither new node depends back on the item.

## New nodes

`lem-pur-varying-ring-tensor-comparison` isolates the normalized comparison for
one specified ordinary inverse-image adjunction and two specified tensor models.
Its natural-language proof uses the existing ringed-topos tensor construction
on the vertical site and transports it by adjoint uniqueness.

`lem-pur-varying-ring-tensor-support` isolates tensor support for canonical
varying-ring extension, independently of any chosen pullback tensor comparison.
Its node records transport from the restricted-ring open-support interface.
The comparison plan uses `lem-pur-independent-ringed-tensorator-existence`
as a generic tool: its independent site sizes are needed on the vertical site;
it does not replace any geometric step of this unit. The parent route is kept.
No existing statement or definition is changed. The local proof settings have
the change record identified above.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
