# AlgebraicGeometry.Scheme.Modules.exteriorPresheaf_open_pullback_data

## Reason

Retire the duplicate Sheaf module under the human-approved retirement hand-off in
coord/changes/retire-sheaf-twins-20261020.md. The upstream theorem is already fully
proved but uses PresheafOfModules.exteriorPower rather than exteriorSheafPresheaf.
The sole direct consumer now proves these presheaves equal, using the defining
pure-wedge formula and uniqueness of the old restriction map. Its public theorem
keeps its exact original signature. No upstream file or target statement changes.

## Old

The retired module was lean/Sheaf/AlgebraicGeometry/Modules/ExteriorPresheafOpenPullbackData.lean and declared:

```lean
theorem exteriorPresheaf_open_pullback_data {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    ∃ (app : ∀ V : U.toScheme.Opensᵒᵖ,
      ((PresheafOfModules.pullback.{v} U.ι.toRingCatSheafHom.hom).obj
        (exteriorSheafPresheaf M n)).obj V ≅
        (exteriorSheafPresheaf (M.restrict U.ι) n).obj V),
      ∀ {V W : U.toScheme.Opensᵒᵖ} (f : V ⟶ W),
        ((PresheafOfModules.pullback.{v} U.ι.toRingCatSheafHom.hom).obj
          (exteriorSheafPresheaf M n)).map f ≫
            (ModuleCat.restrictScalars
              ((U.toScheme.ringCatSheaf.obj.map f).hom)).map (app W).hom =
          (app V).hom ≫ (exteriorSheafPresheaf (M.restrict U.ι) n).map f
```

## New

The node points at lean/WeilConjectures/AlgebraicGeometry/Modules/ExteriorPresheafOpenPullbackData.lean, whose existing theorem is:

```lean
theorem exteriorPresheaf_open_pullback_data {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    ∃ (app : ∀ V : U.toScheme.Opensᵒᵖ,
      ((PresheafOfModules.pullback.{v} U.ι.toRingCatSheafHom.hom).obj
        (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)).obj V ≅
        (_root_.PresheafOfModules.exteriorPower (R := _) (M.restrict U.ι).val n).obj V),
      ∀ {V W : U.toScheme.Opensᵒᵖ} (f : V ⟶ W),
        ((PresheafOfModules.pullback.{v} U.ι.toRingCatSheafHom.hom).obj
          (_root_.PresheafOfModules.exteriorPower (R := _) M.val n)).map f ≫
            (ModuleCat.restrictScalars
              ((U.toScheme.ringCatSheaf.obj.map f).hom)).map (app W).hom =
          (app V).hom ≫
            (_root_.PresheafOfModules.exteriorPower (R := _) (M.restrict U.ι).val n).map f
```

The old file is withdrawn through deleted.txt. The consumer privately proves
exteriorSheafPresheaf M n = PresheafOfModules.exteriorPower M.val n and rewrites
its goal before applying the upstream theorem. Section modules agree definitionally;
map equality follows from the wedge characterization, including degree zero.
No definition or surviving public theorem changes. The mathematical statement is
identical, so no target statement or definition requires renewed semantic review.

## Users

The downstream.py --uses scan finds only the direct consumer calling the retired
theorem. All 16 transitive consumers are listed below; the original item itself is
withdrawn. No module is held by another group at the time of this check.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstantRankExteriorDerivedComparison | unclaimed | Transitive consumer; uses the unchanged consumer interface; no edit needed. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Transitive consumer; uses the unchanged consumer interface; no edit needed. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Transitive consumer; uses the unchanged consumer interface; no edit needed. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullback | unclaimed | Private comparison lemma and proof import changed; public theorem signature unchanged. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafFullOpenIso | unclaimed | Transitive consumer; uses the unchanged consumer interface; no edit needed. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictHomData | unclaimed | Transitive consumer; uses the unchanged consumer interface; no edit needed. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso | unclaimed | Transitive consumer; uses the unchanged consumer interface; no edit needed. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafTopInvertible | unclaimed | Transitive consumer; uses the unchanged consumer interface; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorBasicIdealWedgeCoordinates | unclaimed | Transitive consumer; uses the unchanged consumer interface; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorCompatibleAffineMaps | unclaimed | Transitive consumer; uses the unchanged consumer interface; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart | unclaimed | Transitive consumer; uses the unchanged consumer interface; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartFromSections | unclaimed | Transitive consumer; uses the unchanged consumer interface; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorIdealWedgeCoordinates | unclaimed | Transitive consumer; uses the unchanged consumer interface; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates | unclaimed | Transitive consumer; uses the unchanged consumer interface; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorNestedAffineCoordinates | unclaimed | Transitive consumer; uses the unchanged consumer interface; no edit needed. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Transitive consumer; uses the unchanged consumer interface; no edit needed. |

## Status

landed 20261020T141310-L-2033880 2026-10-20 (merge of deliver/H6/Sheaf.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullbackData)
