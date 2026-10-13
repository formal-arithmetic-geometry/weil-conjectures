# AlgebraicGeometry.directImageSquare_unit_transport

## Reason

The proof needs local irreducibility attributes to prevent expensive unfolding of
chosen right-derived functors and the localization. These attributes are enclosed
in `section EqualityTransport` and revert at its end. The static command comparison
flags the added section and attributes, so this record documents their scope.
There is no definition, statement, visibility, or exported attribute change.

## Old

```lean
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
```

## New

```lean
section EqualityTransport
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  DerivedCategory.Qh
```

The existing variable command remains inside that section, followed by the
unchanged public theorem signature. `end EqualityTransport` restores the local
attributes. The two added private helpers are fully proved and export no interface.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DirectImageSquareUnitTransport | F3 | Proof elaboration only. |
| Sheaf.AlgebraicGeometry.DerivedPushforwardSquareMateUnit | unclaimed | No change; signatures and the square definition are identical. |

`tools/downstream.py` lists 344 transitively downstream modules, with the sole
external textual user of `directImageSquareIso` being the module above. All
transitive users have the same imported signatures, definitions, instances and
attributes; no adaptation is required. No target uses a changed definition.

## Status

landed 20261013T234508-L-2161819 2026-10-13 (merge of deliver/F3/Sheaf.AlgebraicGeometry.DirectImageSquareUnitTransport)
