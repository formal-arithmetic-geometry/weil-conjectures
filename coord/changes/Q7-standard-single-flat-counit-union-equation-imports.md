# AlgebraicGeometry.standardSingleFlatCounitUnionEquation

## Reason

Restore the module listed in `coord/rework.tsv`, preserved at
`quarantine/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitUnionEquation.lean`.
The archived file fails to compile against the current published library:

```text
StandardSingleFlatCounitUnionEquation.lean:118:13:
Unknown identifier `SingleComplexBaseChange.counit_isIso_kFlat`
```

The Sheaf counit module was withdrawn. Its adopted source-library replacement
provides the required theorem, with hypothesis `CochainComplex.IsKFlatTensor`.
The archived bounded-flat import instead proves `IsAcyclicTensorKFlat`.
Replace both private proof imports by the matching adopted source providers.
The repaired module compiles without warnings in 13.5 seconds.

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

Every declaration, signature, proof body, public import and docstring is
preserved verbatim from the quarantined source. No adopted source file is
modified. Both replacement imports pass `tools/import_direction.py may`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionEquation | Q7 | Restored with the two corrected private proof imports. |
| Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionPresentation | unclaimed, quarantined | Sole archived direct caller; the called theorem's signature and public imports are identical. No adaptation. |

`tools/downstream.py` with `--allow-missing --uses
standardSingleFlatCounitUnionEquation` reports no live downstream modules.
Searching `lean/` and `quarantine/` also finds the archived caller above.
It is retained as a caller, not treated as evidence that the item is unused.
In a scratch sandbox, `lcompile.py --all` compiled the repaired equation
module in 14.8 seconds and the unchanged archived caller in 5.9 seconds,
without warnings. Neither scratch copy is part of the delivery.

The item node `new-pc-standard-single-flat-counit-union-equation`, its Lean
attachment, and its three proof dependencies remain intact. The proof still
uses the union-triangle theorem, Mathlib triangle two-out-of-three, the
bounded-flat K-flatness theorem, the pinned counit theorem and inverse
cancellation. No definition or target meaning changes, and no unit route or
node statement changes. There are no forced consumer adaptations.

## Status

landed 20261021T170803-L-2760652 2026-10-21 (merge of deliver/Q7/Sheaf.AlgebraicGeometry.StandardSingleFlatCounitUnionEquation)
