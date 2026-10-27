# AlgebraicGeometry.Etale.RawModuleScalarComparison.pullback_unit

## Reason

The current assigned item is already fully proved. Its only private proof import,
`import all Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition`, is needed only
for that module's private `scalar_unit` helper. The canonical comparison is already
defined upstream as the adjunction mate of the forgotten module unit. Applying the
adjunction Hom equivalence therefore proves the required unit equation directly,
without importing a theorem about composition of two inverse images.

This removes a proof dependency, including access to another module's private
implementation. All definitions, theorem signatures, visibility, instances and public
imports are preserved. No source-library file is changed.

## Old

The proof-only import is:

```lean
import all Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition
```

The theorem, verbatim:

```lean
theorem pullback_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((forget Λ Y).obj F) ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map (pullback Λ f F) =
      (forget Λ Y).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F) := by
  exact AlgebraicGeometry.Etale.scalar_unit Λ f F
```

## New

The proof-only import above is removed. The theorem is:

```lean
theorem pullback_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((forget Λ Y).obj F) ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map (pullback Λ f F) =
      (forget Λ Y).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F) := by
  change (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
    ((moduleAbelianUpperStarComparison Λ f).app F) = _
  exact Equiv.apply_symm_apply _ _
```

The proof docstring and construction node's second proof step are updated to describe
the direct adjunction argument. The node's statement, dependencies, unit route and
upstream Lean attachment remain unchanged. The existing uniqueness and explicit
Kan-extension/sheafification equality proofs continue to compile.

## Users

`tools/downstream.py --direct --uses pullback_unit eq_pullback_of_unit
kanSheafification_eq_pullback` and a textual search identify the current direct
consumers. Neither uses the removed module's public composition theorem or private
helper through this proof-only import. Since no public import changes, their public
interfaces and instance environments are unchanged. No adaptations are needed.
The full downstream closure is unaffected for the same reason: the removed import
was private, and every public signature remains identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison | C2 | Directly proves its unit equation and removes one private proof import. |
| Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer | unclaimed | Same canonical scalar-forgetting and comparison API; no adaptation. |
| Sheaf.Paper.CartierRelativeBoundaryRealization | unclaimed | Same scalar-forgetting and comparison API; no adaptation. |
| Sheaf.AlgebraicGeometry.RawModuleScalarSheafComposition | unclaimed | Its implementation is no longer imported by this item; the module and all declarations remain. |

The composition node still has other DAG consumers, so it is not withdrawn. No
quarantined module, dependency or attachment is removed. No target meaning changes.

## Status

landed 20261024T184653-L-3097688 2026-10-24 (merge of deliver/C2/Sheaf.AlgebraicGeometry.RawModuleScalarPullbackComparison)
