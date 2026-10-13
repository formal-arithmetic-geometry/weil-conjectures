# picardExternalCechCupDegreeMaps_comm_ι

## Reason

The missing differential proof needs local transparency options during elaboration.
These are declaration-local and apply only to private helpers and the proved theorem.
This record documents conservative static interface-checker flags; no public statement,
definition, visibility or public import changes.

## Old

The baseline has no helper option commands, and the target proof body is:

```lean
  sorry
```

## New

Private helper declarations and the target theorem each use the following prefix:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

There is no section-wide option command. The target has a kernel-checked proof, and a
proof-only `import all Sheaf.Paper.CechCupProduct` reuses its existing private arithmetic
lemmas instead of duplicating them. Existing signatures and definitions are unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferential | unclaimed | Unchanged direct importer compiled against the delivered proof. |

There is no interface change and no forced adaptation. All other downstream modules see
exactly the original public declarations and definitions. Neither of the unrelated modules
named in the first worker's batch-collision report is edited or newly imported.

## Status

landed 20261013T172654-L-2099157 2026-10-13 (merge of deliver/J2/Sheaf.AlgebraicGeometry.PicardExternalCechCupDifferentialCoordinate)
