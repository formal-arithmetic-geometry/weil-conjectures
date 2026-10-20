# AlgebraicGeometry.Scheme.Modules.exteriorPresheaf_open_pullback

## Reason

Retire the Sheaf duplicate listed in coord/retire-items.tsv, under the human-approved
hand-off in coord/changes/retire-sheaf-twins-20261020.md. Its upstream twin is fully
proved. The APIs differ only in their sectionwise exterior-power presheaf construction.
The already-proved private equality bridge is moved to the sole direct consumer,
Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictHomData. That consumer imports
the upstream theorem, rewrites its result with the bridge, and continues its existing
sheafification argument. No source-library file is changed.

## Old

The retired module lean/Sheaf/AlgebraicGeometry/Modules/ExteriorPresheafOpenPullback.lean
exported:

```lean
theorem exteriorPresheaf_open_pullback {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    Nonempty ((PresheafOfModules.pullback.{v} U.ι.toRingCatSheafHom.hom).obj
      (exteriorSheafPresheaf M n) ≅ exteriorSheafPresheaf (M.restrict U.ι) n)
```

## New

The node now points at the existing upstream theorem in
lean/WeilConjectures/AlgebraicGeometry/Modules/ExteriorPresheafOpenPullback.lean:

```lean
theorem exteriorPresheaf_open_pullback {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    Nonempty ((PresheafOfModules.pullback.{v} U.ι.toRingCatSheafHom.hom).obj
      (_root_.PresheafOfModules.exteriorPower (R := _) M.val n) ≅
        _root_.PresheafOfModules.exteriorPower (R := _) (M.restrict U.ι).val n)
```

The old module is withdrawn through deleted.txt. The sole consumer proves the equality
exteriorSheafPresheaf M n = PresheafOfModules.exteriorPower M.val n: objects agree
by definition and maps agree by uniqueness on pure wedges. It rewrites the upstream
comparison at M and M.restrict U.ι, then sheafifies exactly as before. The public
consumer signature and public imports stay byte-for-byte identical. This includes
degree zero, empty opens and empty schemes, since no positivity or nonemptiness
hypothesis enters the equality proof. All target statements and definitions are
unchanged, and the node's mathematical statement is unchanged.

## Users

The downstream.py --uses scan finds the retired module and its sole direct consumer
as the two occurrences of the theorem name. The full list of 15 downstream modules
is below. Current claim records show each as unclaimed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstantRankExteriorDerivedComparison | unclaimed | Transitive user; consumer signature unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Transitive user; consumer signature unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Transitive user; consumer signature unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafFullOpenIso | unclaimed | Transitive user; consumer signature unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictHomData | unclaimed | Private bridge moved here; proof import and four proof lines adapted; signature unchanged. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso | unclaimed | Transitive user; consumer signature unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafTopInvertible | unclaimed | Transitive user; consumer signature unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorBasicIdealWedgeCoordinates | unclaimed | Transitive user; consumer signature unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorCompatibleAffineMaps | unclaimed | Transitive user; consumer signature unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart | unclaimed | Transitive user; consumer signature unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartFromSections | unclaimed | Transitive user; consumer signature unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorIdealWedgeCoordinates | unclaimed | Transitive user; consumer signature unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates | unclaimed | Transitive user; consumer signature unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.SelfTorNestedAffineCoordinates | unclaimed | Transitive user; consumer signature unchanged; no edit needed. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Transitive user; consumer signature unchanged; no edit needed. |

## Status

landed 20261020T154036-L-3031447 2026-10-20 (merge of deliver/B3/Sheaf.AlgebraicGeometry.Modules.ExteriorPresheafOpenPullback)
