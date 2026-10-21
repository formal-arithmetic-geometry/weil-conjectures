# AlgebraicGeometry.ProEtale.integralIndConstructibleHeartClosure

## Reason

Restore the quarantined item from the archive in `coord/rework.tsv` and repair
its public statement's missing Mathlib closure classes. The archived proof is
complete, but the original single-file compile fails with invalid fields
`IsClosedUnderKernels`, `IsClosedUnderCokernels` and `IsClosedUnderExtensions`.
The defining modules must be public imports because these classes occur in the
public theorem's type.

## Old

The complete baseline is
`quarantine/Sheaf/Paper/IntegralIndConstructibleHeartClosure.lean`.
Immediately after `module`, its first import is exactly:

```lean
public import Mathlib.CategoryTheory.ObjectProperty.Ind
```

There are no direct public imports of the kernel/cokernel or extension classes.
The archived file contains no `sorry`.

## New

The same header now begins:

```lean
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
```

These are the only changes relative to the archive. All declarations, signatures,
proofs, attributes, definitions and previous imports remain verbatim. The repaired
file compiles without warnings in 18.6 seconds. No target meaning changes, and no
new hole, node or arbitrary data choice is introduced.

## Users

A search of live and quarantined Lean sources found three direct importing
modules, all quarantined. None requires adaptation: their previous theorem and
private-helper interfaces are retained, and the defining closure-class modules
are additionally exported. No other group's file is changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralIndConstructibleHeartClosure | Q6 | Restored and repaired with two public imports. |
| Sheaf.Paper.IntegralIndConstructibleStability | unclaimed | Quarantined direct consumer; identical theorem interface, no adaptation. |
| Sheaf.Paper.IntegralProperCohomologicalBounds | unclaimed | Quarantined direct consumer; identical public and private interfaces, no adaptation. |
| Sheaf.Paper.IntegralProperConstructibleHeartBound | unclaimed | Quarantined direct consumer; identical public and private interfaces, no adaptation. |

All transitive consumers likewise retain the same declarations and definitions.

## Status

landed 20261021T162125-L-287894 2026-10-21 (merge of deliver/Q6/Sheaf.Paper.IntegralIndConstructibleHeartClosure)
