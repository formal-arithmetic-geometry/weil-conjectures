# AlgebraicGeometry.Etale.hasTorAmplitudeIn_rightDerivedLowerStar_of_relative_bound

## Reason

The item repeatedly checks expressions involving chosen unbounded derived models and the
canonical finite-constant projection map. These models have proved interfaces; unfolding
those constructions is unnecessary for checking the finite interval argument. Local
irreducibility keeps those checks at the functor interface. Local braiding priorities
also align with the existing derived tensor and residue criterion. Removing the local
category aliases from the helper avoids repeated kernel reductions of their inferred
structures; the complete file then compiles in 41.7 seconds. The attribute is scoped to this
file and exports no changed definition, instance, theorem type or public import.

## Old

```lean
attribute [local instance 20000] CommRing.toRing
```

No local irreducibility declaration for the derived models was present.

## New

```lean
attribute [local instance 20000] CommRing.toRing
attribute [local instance 20000] SymmetricCategory.toBraidedCategory sheafBraidedCategory

-- Use the published functor interfaces without unfolding their chosen models.
attribute [local irreducible] Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor lowerStar finiteConstantProjectionMap
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleResidueDirectImageTorWindow | K2 | Local proof checking only. |
| Sheaf.Paper.EtaleFiniteTorDirectImageCoefficients | unclaimed | Identical public theorem signature and visibility; no adaptation required. |

The users are the union of downstream.py's importers and declaration uses. The consumer
applies the theorem at its htF binding and receives the identical Tor interval conclusion.

## Status

landed 20261023T123804-L-1252860 2026-10-23 (merge of deliver/K2/Sheaf.AlgebraicGeometry.EtaleResidueDirectImageTorWindow)
