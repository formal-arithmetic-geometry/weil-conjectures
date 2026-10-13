# AlgebraicGeometry.Scheme.Modules field-linear comparison elaboration

## Reason

The original file repeatedly approached the 60-second compiler limit. Resolving the new
resolution-comparison proof requires reducing unnecessary unfolding of existing comparison
constructions. The static check conservatively classifies the local transparency commands and
the definition reformulation as interface changes. No target statement, exported visibility,
or exported reducibility changes. There are no forced adaptations.

## Old

No early local irreducibility attributes for moduleExtEquiv, constantScalarUnitIso,
scalarUnitMorphism, scalarExtMap, scalarCohomologyExtMap, or scalarPullbackSquareIso.
The global irreducibility commands retain exactly their old declarations and placement.

```lean
  AddEquiv.ofBijective
    (AddMonoidHom.mk' (scalarCohomologyExtMap f F n) (scalarCohomologyExtMap_add f F n))
    (scalarCohomologyExtMap_bijective f F n)
```

## New

Local irreducibility commands keep these definitions folded during subsequent elaboration.
The first five are confined to a nested section which ends before the existing global
irreducibility command. The square comparison is locally irreducible before externalCupPullbackIso.
The scalar Ext definitions use local respectTransparency settings. Existing public signatures
are identical.

The scalarCohomologyExtEquiv constructor is written directly:

```lean
  { Equiv.ofBijective (scalarCohomologyExtMap f F n)
      (scalarCohomologyExtMap_bijective f F n) with
    map_add' := scalarCohomologyExtMap_add f F n }
```

This is definitionally the same equivalence: AddEquiv.ofBijective is the constructor above
with map_add supplied by the additive homomorphism. A diagnostic equality is checked by rfl.
Its function and chosen inverse are unchanged. No target meaning changes, so no target statement
review is reopened. The private finite-colimit helper and the additive theorem only change proofs.

## Users

Read-only textual searches over both library roots identify the following users of the affected
names (equivalently tools/downstream.py --uses for each name). Local attributes do not escape
the section. All direct importers see the same signatures, global attributes and comparison data.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ExternalCupScalarBalance | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations | U3 | Same signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.PicardExternalCupCochain | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyExtCoefficientNaturality | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackComposition | see current claim | Same signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCohomologyPullbackSquare | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupCoefficientNaturality | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupPullbackCoefficientNaturality | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupPullbackNaturality | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarCupUnitIdentities | see current claim | Same signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitClassPullback | see current claim | Same signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitCohomologyComparisonFamily | unclaimed | Same signatures and data; no adaptation. |
| Sheaf.AlgebraicGeometry.ScalarUnitCohomologyPullbackNaturality | see current claim | Same signatures and data; no adaptation. |

## Status

landed 20261013T100148-L-2493399 2026-10-13 (merge of deliver/U3/Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations)
