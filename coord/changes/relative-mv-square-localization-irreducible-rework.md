# AlgebraicGeometry.relativeMV_direct_image_square_localization

## Reason

Restore the module archived by the upstream sync at
`quarantine/Sheaf/AlgebraicGeometry/RelativeMVDirectImageSquareLocalization.lean`.
The rework entry reports failure of the local reducibility command because
`AlgebraicGeometry.derivedPullback` is already irreducible in the current upstream source.
Remove only its redundant entry from that local command. The local attributes on
`Functor.rightDerivedFunctor` and `Functor.rightDerivedFunctorUnit` remain in place.

This is a compilation repair with zero holes, with no definition, theorem signature,
proof body, import, public attribute, or target meaning changed. The archived source
and its blueprint tag are preserved. No downstream adaptation is required.

## Old

```lean
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  derivedPullback
```

## New

```lean
attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RelativeMVDirectImageSquareLocalization | G1 | Restore the existing complete proof with the redundant local attribute entry removed. |
| Sheaf.AlgebraicGeometry.RelativeMVNormalizedCoefficientRoof | unclaimed in shared snapshot | Sole direct importer, currently quarantined; unchanged signature and public imports preserve its call to relativeMV_direct_image_square_localization. |

`tools/downstream.py` reports the item as unknown because it is currently outside
`lean/`. Searching imports in both library roots and `quarantine/` finds only the
consumer listed above. The rework cluster's other modules are transitive consumers.
The restored module and the unmodified archived consumer compiled in dependency
order through `lcompile.py`, taking 30.6 and 17.4 seconds respectively.
The consumer was used only for verification and is not delivered.

## Status

landed 20261020T145510-L-2403028 2026-10-20 (merge of deliver/G1/Sheaf.AlgebraicGeometry.RelativeMVDirectImageSquareLocalization)
