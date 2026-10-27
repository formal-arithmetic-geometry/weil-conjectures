## What changed

Added the two strictly smaller interface modules
`Sheaf.Paper.FieldPuritySystemTransposeBase` and
`Sheaf.Paper.FieldPuritySystemTransposeCompatibility`. The assigned theorem now
combines their conclusions by ordinary conjunction elimination and introduction.
The base and compatibility modules retain the existing dependency imports.

## Proved and sorry left

The assigned declaration `field_purity_system_transpose` is proved by composing the
two split interface statements. The two split declarations remain sorry:
`field_purity_system_transpose_base` (node
`lem-sp-field-purity-system-transpose-base`) and
`field_purity_system_transpose_compatibility` (node
`lem-sp-field-purity-system-transpose-compatibility`). No sorry occurs in a
definition.

## No longer needed

No imports or declared proof dependencies were removed. The target's original
proof-dependency route is retained in the two split statements.

## Where the brief, the DAG or earlier work was wrong

The original item is a long assembly theorem whose stated dependencies do not
provide a single Lean declaration packaging the finite-level and compatibility
assemblies. The proof was therefore split into two strict conjunctive interface
lemmas, each strictly weaker than the assigned theorem, and the assigned theorem
is now a real Lean proof from those interfaces.

## New nodes

`lem-sp-field-purity-system-transpose-base` records the finite tensor, unit, and
finite purity part. `lem-sp-field-purity-system-transpose-compatibility` records
the final scalar and diagonal compatibility part. Their node files are in
`dag/nodes/sec-smooth-purity/`, and their Lean declarations are in the two new
modules under `lean/Sheaf/Paper/`.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
