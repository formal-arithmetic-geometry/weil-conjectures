# AlgebraicGeometry.Scheme.GaloisCover.equivariantModulePresheaf_isSheaf

## Reason

The canonical implementation retained for upstream review #1428 compiles with
Lean's default transparency setting. Remove its unnecessary file-wide override.
Preflight treats a command removal as a change to what importers see, so this
record documents the change explicitly. All declarations and imports stay
identical; no statement or definition changes.

## Old

```lean
set_option backward.isDefEq.respectTransparency false
```

## New

The command is removed. The default setting applies throughout the module.
The theorem signature and its proof body are unchanged. Compilation succeeds
without warnings; its axioms are propext, Classical.choice, Quot.sound only.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.ConstructibleSheaf.TorsorAssociatedModuleFull | unclaimed | Same theorem signature; no adaptation. |
| Sheaf.ConstructibleSheaf.TorsorEquivariantPresheafSheaf | repair listed | Same public compatibility import; no adaptation. |
| Sheaf.ConstructibleSheaf.TorsorInvariantSections | unclaimed | Same theorem reference; no adaptation. |
| Sheaf.ConstructibleSheaf.TorsorSectionEvaluationBijective | unclaimed | Same theorem reference; no adaptation. |

No adapted modules are delivered. No target statement or definition changes.

## Status

landed 20261014T022540-L-4043525 2026-10-14 (merge of deliver/A3/Sheaf.ConstructibleSheaf.TorsorEquivariantModuleIsSheaf)
