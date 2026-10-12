# DerivedRHomAlgebraModule type elaboration

## Reason

The stage-3 checker classifies a new file-level option as a command/interface change.
This option controls elaboration inside the item only and is not exported to importers.
The original full module timed out locally after 60 seconds. With the explicit universe-u
finite-(co)limit proofs and the option below, the current-baseline module plus the completed
descent proof compiles cleanly in 41.8 seconds. No declaration signature, visibility,
definition body, instance registration, target statement, or public import changes.

## Old

```lean
set_option backward.isDefEq.respectTransparency false
```

## New

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The additional option allows the existing type expressions to reduce during elaboration.
It does not select data, change a mathematical construction, or alter an importer's options.
The finite-limit and finite-colimit changes are proof-only. The new Mathlib KInjective import
is private and only supports the proved private generic helper and descent theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineDerivedHomEvaluationCounit | unclaimed | Unchanged signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.DerivedAlgebraQCohOfUnderlying | unclaimed | Unchanged signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAffineDerivedEquivalence | unclaimed | Unchanged signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAffineDerivedFactorization | unclaimed | Unchanged signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteAlgebraHomExact | unclaimed | Unchanged signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteExactHomDegreeZeroLift | U3 | Unchanged signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.FinitePushforwardDerivedHomQCoherent | unclaimed | Unchanged signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.FiniteRestrictionDerivedRightAdjoint | unclaimed | Unchanged signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.PseudoCoherentRHomQuasiCoherent | unclaimed | Unchanged signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.SheafAlgebraDerivedHomAdjunction | unclaimed | Unchanged signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.SheafAlgebraHomAdjunction | unclaimed | Unchanged signatures and definitions; no adaptation. |
| Sheaf.AlgebraicGeometry.SheafAlgebraMapDerivedAdjunction | unclaimed | Unchanged signatures and definitions; no adaptation. |

These are the twelve direct importers of the current baseline. None is adapted or delivered.
No target uses a changed definition, because every definition body is unchanged.
The independent reader and global build verify the elaborated signatures and downstream files.

## Status

landed 20261012T165516-L-2934396 2026-10-12 (merge of deliver/J1/Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule)
