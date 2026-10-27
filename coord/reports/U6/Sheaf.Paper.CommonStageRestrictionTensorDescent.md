## What changed

Constructed the tensor comparison from an explicit isomorphism at the input
compositum. Proved its naturality by representing arbitrary arrows at a common
field and applying finite-stage naturality. Constructed the unit comparison from
the base field and proved its representative formula by cancellation in the mixed
unit square. Proved preservation of path equations by functoriality.

The main module privately imports RestrictionTensorRepresentativeTransport for
fixed-component enlargement. Canonical pair wrappers and typed coordinate comparisons
avoid expensive elaboration of the nested coefficient categories. All comparison
data and the public descent statement retain their original mathematical meaning.
The definition changes are recorded in the change record below.

## Proved and sorry left

The original hole in
`WeilConjectures.CommonStageRestrictionTensor.descent` is replaced by a complete
proof from the named component-enlargement theorem. The main module has zero
written sorries and compiles cleanly (39.9 seconds). The new module compiles
cleanly in 36.4 seconds. One new hole remains:
`WeilConjectures.restrictionTensorRepresentativeTransport`
(node `lem-pur-restriction-tensor-representative-transport`).

This is a decomposition: one original hole closed conditional on one strictly
smaller component lemma, one hole added, and no claimed net hole reduction.
The naturality, invertibility, unit descent and path-equation arguments are proved
in the main module rather than included in that component lemma.

## No longer needed

Removed the unused private import
`Sheaf.Paper.IntegralDerivedOperationsOnSlices`.
No modules or declarations are withdrawn. The scalar-operation tower and
scalar-composition tools remain needed in the component enlargement lemma;
they have not been pruned from the overall argument. Path preservation uses only
the existing inclusion functor laws and induction on paths.

## Where the brief, the DAG or earlier work was wrong

The available scalar-operation tower is an ordinary integral equation. Applying it
at the rational small coefficient models also requires compatibility with
completion, localization and the stage-transition identifications. The specialized
rational restriction coherence module uses actual intermediate fields in the
scheme universe, whereas this item uses small coefficient models and an independent
closure universe. It does not directly instantiate here.

The original comparison definitions triggered large definitional-equality
calculations. The explicit coordinate presentation fixes their endpoint types at
construction time. No target signature or adopted source-library file changes.

## New nodes

`lem-pur-restriction-tensor-representative-transport` is the fixed-component
enlargement calculation from original proof steps 3–5. It asserts equality of two
morphism representatives. It does not assert naturality, existence of a descended
comparison, a unit comparison, or preservation of equations. Edge cases checked:
L=H, repeated fields, zero objects and empty schemes. Equality is in the common-stage
quotient and requires no faithful scalar extension.

Change record: `coord/changes/U6-common-stage-restriction-coordinate-interface.md`.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
