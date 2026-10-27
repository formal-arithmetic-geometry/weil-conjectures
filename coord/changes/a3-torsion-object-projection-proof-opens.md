# AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_constant_of_torsion_object

## Reason

The completed proof uses coproducts and derived-functor notation. Add namespace openings
for `CategoryTheory.Limits` and scoped notation `CategoryTheory.Functor`. The static checker
classifies additions of `open` commands as a possible visible change. This record documents
those commands; no declaration signature, definition, instance, attribute or public import
changes. All added imports are private proof imports.

## Old

```lean
open CategoryTheory
```

## New

```lean
open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Functor
```

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.TorsionObjectConstantProjection --uses
AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_constant_of_torsion_object`
reported zero downstream modules and only the item itself as a textual user. The unfinished
DAG parent `lem-sf-direct-image-tor-amplitude-noetherian` retains this item's statement and
attachment unchanged; it needs no adaptation. Namespace opening changes local name resolution
inside this module and does not change the elaborated exported theorem type.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.TorsionObjectConstantProjection | A3 | Same signature; complete proof, local proof notation available. |

## Status

landed 20261023T134733-L-2743943 2026-10-23 (merge of deliver/A3/Sheaf.AlgebraicGeometry.TorsionObjectConstantProjection)
