# FiniteNormalTraitPurity Noetherian import visibility

## Reason

Mathlib.AlgebraicGeometry.Noetherian is needed only to infer local Noetherianity
of L in the proof, not to state the existing declaration. Make it a plain import.
The existing theorem signature is byte for byte unchanged. No target definition changes.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Noetherian
```

## New

```lean
import Mathlib.AlgebraicGeometry.Noetherian
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Morphisms.StalkNormalizationFibrePurity | unclaimed | It is the only direct importer, and already publicly imports Mathlib.AlgebraicGeometry.Noetherian itself. Its statements and all transitive users therefore retain the same Noetherian declarations. No adaptation is needed. |

The other public imports of FiniteNormalTraitPurity already supply the ring-level
IsNoetherianRing used in its signature. New modules have no existing users.

## Status

landed 20261012T235558-L-2202589 2026-10-12 (merge of deliver/U1/Sheaf.AlgebraicGeometry.Morphisms.FiniteNormalTraitPurity)
