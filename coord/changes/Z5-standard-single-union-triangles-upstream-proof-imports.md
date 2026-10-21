# AlgebraicGeometry.standardSingleFlatCounitUnionTriangles

## Reason

Restore the module quarantined after the 2026-10-20 cluster restore. Compiling the
archived source against the current library fails at line 75 with:

```text
Unknown identifier `SingleComplexBaseChange.counit_isIso_kFlat`
```

The old Sheaf counit module is now an empty withdrawn module. The adopted source
module provides that theorem with the current `IsKFlatTensor` hypothesis. The
archived bounded-flat proof import instead produces `IsAcyclicTensorKFlat`.
Replace both private imports with the matching source-library providers. This
repairs the failed proof without changing any declaration, proof body, public
import, definition, or target statement.

## Old

```lean
import Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit
import Sheaf.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
```

## New

```lean
import WeilConjectures.AlgebraicGeometry.IsomorphismPullbackCounit
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
```

The complete archived theorem signature and proof are preserved verbatim.
The source bounded-flat theorem produces precisely the K-flat predicate needed
by the source counit theorem. Both new imports pass `import_direction.py may`.
No file under `lean/WeilConjectures/` is modified.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionTriangles | Z5 | Restored with matching private proof imports. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionEquation | unclaimed, quarantined | Sole archived direct importer and caller; the restored theorem has exactly its archived signature and public imports. No adaptation. |

`tools/downstream.py` with `--allow-missing --uses
standardSingleFlatCounitUnionTriangles` reports no live downstream module.
Searching both `lean/` and `quarantine/` finds the archived caller above. Its
own obsolete private imports remain its separate rework assignment; this
restoration introduces no new consumer error.

The node `new-pc-standard-single-flat-counit-union-triangles`, its Lean
attachment, and every mathematical dependency are preserved. The proof still
uses the same bounded-flat, counit, short-exact-presentation and Mathlib
triangle lemmas. No node statement or unit route changes, and no target
semantic review is reopened. No consumer is adapted in this packet.

## Status

landed 20261021T154757-L-3173378 2026-10-21 (merge of deliver/Z5/Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionTriangles)
