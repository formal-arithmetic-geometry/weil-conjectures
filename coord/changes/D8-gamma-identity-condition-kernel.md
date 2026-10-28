# WeilConjectures.CompactSupportCondensedRealization.GammaIdentityCondition

## Reason

The direct proof by `SemilinearProperOpen.gamma_identities` elaborates in milliseconds,
but kernel checking the old definition takes over 110 seconds and exhausts its
heartbeat budget. Inspection of the elaborated definition identifies auxiliary
proof declarations for proper identity maps, quasi-compactness and site smallness.
Comparing those proof arguments causes the kernel to unfold the large mate data.

Use a proposition structure with exactly the original equation as its sole field,
with `backward.proofsInPublic true` scoped to that structure. This retains the
proof arguments in the field type and avoids the expensive conversion. The old
condition implies the new one by `fun h => ⟨h⟩`; the new one implies the old by
`fun h => h.identity`. No equation, object, morphism, domain or coefficient changes. This condition is a
proof helper declared after `ComparisonFamily`; it is absent from that structure
and from the target statement definitions.
The condition is inhabited from the existing generic identity, not from a new hole.

The option controls auxiliary proof abstraction; it does not disable kernel checking.
See the option declaration in Lean's elaborator:
https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/SyntheticMVars.lean

## Old

```lean
def GammaIdentityCondition {X Y : CondensedERealization.Base k}
    (f : X.scheme ⟶ Y.scheme) (c : Compactification f) : Prop :=
  ∀ N, ((AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma
      (quotientRings l E) (quotientMaps l E) c.i (𝟙 X.scheme) (𝟙 c.Z) c.i (by simp)).app N ≫
      (AlgebraicGeometry.ProEtale.SemilinearProperOpen.sId
        (quotientRings l E) (quotientMaps l E) c.Z).hom.app
        ((AlgebraicGeometry.ProEtale.SemilinearProperOpen.J
          (quotientRings l E) (quotientMaps l E) c.i).obj N)) =
    (AlgebraicGeometry.ProEtale.SemilinearProperOpen.J
      (quotientRings l E) (quotientMaps l E) c.i).map
      ((AlgebraicGeometry.ProEtale.SemilinearProperOpen.sId
        (quotientRings l E) (quotientMaps l E) X.scheme).hom.app N)
```

## New

The following declaration is under `set_option backward.proofsInPublic true in`.

```lean
structure GammaIdentityCondition {X Y : CondensedERealization.Base k}
    (f : X.scheme ⟶ Y.scheme) (c : Compactification f) : Prop where
  identity : ∀ N, ((AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma
      (quotientRings l E) (quotientMaps l E) c.i (𝟙 X.scheme) (𝟙 c.Z) c.i (by simp)).app N ≫
      (AlgebraicGeometry.ProEtale.SemilinearProperOpen.sId
        (quotientRings l E) (quotientMaps l E) c.Z).hom.app
        ((AlgebraicGeometry.ProEtale.SemilinearProperOpen.J
          (quotientRings l E) (quotientMaps l E) c.i).obj N)) =
    (AlgebraicGeometry.ProEtale.SemilinearProperOpen.J
      (quotientRings l E) (quotientMaps l E) c.i).map
      ((AlgebraicGeometry.ProEtale.SemilinearProperOpen.sId
        (quotientRings l E) (quotientMaps l E) X.scheme).hom.app N)
```

## Users

`tools/downstream.py Sheaf.Paper.CompactSupportCondensedRealization --uses
GammaIdentityCondition` finds 61 downstream modules and exactly one textual user
of this declaration: the item itself. The structure constructor proves the same
condition, and the remaining component theorem accepts the same named proposition.
None of the 61 downstream module statements mentions the changed declaration.
No module outside the item is adapted. The direct importers are included below
for compilation with this delivery; holder entries describe the shared snapshot.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompactSupportCondensedRealization | D8 | Package the identical equation; construct its witness from the existing generic theorem. |
| Sheaf.Paper.CompactSupportRealizationCoordinates | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.CompactSupportRealizationFactorNormalization | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.CompactSupportRealizationFactorization | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.CompactSupportRealizationSquareExistence | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.CondensedCompositorRealizationData | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.CondensedExceptionalReconstructionData | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.CondensedOpenCounitComparisons | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.CondensedOpenCounitRealization | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.CondensedOpenCounitUnits | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.ExceptionalRealizationNormalization | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.ExceptionalReconstructionComparison | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.ExceptionalReconstructionContext | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.FilteredCondensedRepresentingPairData | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.GeneralCondensedWeilRealization | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.MixedCupRingedNormalization | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.PurIntegralRepresentingPair | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.PurIntegralSupportComparison | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |
| Sheaf.Paper.PurIntegralSupportComparisonData | unclaimed in snapshot | No declaration use or source edit; compile as a direct importer. |

## Status

landed 20261028T072356-L-1939193 2026-10-28 (merge of deliver/D8/Sheaf.Paper.CompactSupportCondensedRealization)
