# AlgebraicGeometry.rectangle_ordinary_pasting_comparisons

## Reason

Keep expensive derived functor definitions folded while elaborating the rectangle
statement and proof. These two file-local options affect elaboration in this file;
they do not export an attribute, instance or option to importing modules. The generic
adjunction transport calculation and geometric comparison statements compile as written.
The delivery checker conservatively records changed commands as an interface change.
The theorem's name, universe parameters, binders, visibility and conclusion are identical.

## Old

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## New

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
```

## Users

The declaration-use scan from tools/downstream.py reports the following two modules.
There are 337 transitive downstream modules, but only these two mention this declaration.
The options are file-local and every user's imported declaration has the same type.
No adaptation is forced or included.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RectangleOrdinaryPastingComparisons | B3 | Own proof elaborates with folded definitions; signature unchanged. |
| Sheaf.AlgebraicGeometry.RectangleInverseBaseChangeMateTransport | unclaimed | Imported theorem type is unchanged; no exported option or attribute changes. |

## Status

landed 20261013T151131-L-876167 2026-10-13 (merge of deliver/B3/Sheaf.AlgebraicGeometry.RectangleOrdinaryPastingComparisons)
