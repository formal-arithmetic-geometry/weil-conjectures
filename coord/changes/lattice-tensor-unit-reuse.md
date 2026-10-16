# latticeTensorUnit and latticeExtension_unit

## Reason

The returned delivery duplicated the existing private theorem `latticeExtension_unit`
and its private tensor-unit definition in `LatticeGluedRationalizationIso`. Expose the
existing declarations in the unclaimed module `LatticeSheafBasic`, and remove both
copies from the new module. Its proof now uses the imported existing theorem.
The tensor-unit definition must also be public because it occurs in the theorem's
signature. Neither the mathematical statements nor the construction or proof bodies
change. All pre-existing public signatures and all target meanings are unchanged.

## Old

```lean
private noncomputable def latticeTensorUnit
    (M : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U))) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (S.over U)).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (latticeScalarMap a U) M)

private theorem latticeExtension_unit
    (M N : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)))
    (f : M ⟶ N) (T : (Over U)ᵒᵖ) (m : M.val.obj T) :
    (SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
      (latticeScalarMap a U) M f).val.app T ((latticeTensorUnit a U M).app T
      ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
        ((latticeScalarMap a U).hom.app T).hom] m)) =
      (latticeTensorUnit a U N).app T
        ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
          ((latticeScalarMap a U).hom.app T).hom] (f.val.app T m))
```

## New

```lean
noncomputable def latticeTensorUnit
    (M : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U))) :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (S.over U)).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (latticeScalarMap a U) M)

theorem latticeExtension_unit
    (M N : SheafOfModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (R.over U)))
    (f : M ⟶ N) (T : (Over U)ᵒᵖ) (m : M.val.obj T) :
    (SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
      (latticeScalarMap a U) M f).val.app T ((latticeTensorUnit a U M).app T
      ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
        ((latticeScalarMap a U).hom.app T).hom] m)) =
      (latticeTensorUnit a U N).app T
        ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
          ((latticeScalarMap a U).hom.app T).hom] (f.val.app T m))
```

The same local binders as in `LatticeSheafBasic` apply to both versions: the implicit
scheme X, implicit ring sheaves R and S, the explicit morphism a : R ⟶ S, and the
explicit slice object U. Neither declaration depends on L. The theorem proof is
unchanged. The new module uses the existing public import chain to Basic.

## Users

Ran `tools/downstream.py Sheaf.Paper.LatticeSheafBasic --uses latticeExtension_unit`
and the analogous command for `latticeTensorUnit` on 2026-10-16. Both find only Basic
itself (three and ten occurrences respectively); there are 28 downstream modules.
The table includes those consumers, Basic, and all six new supporting modules.
Only the new isomorphism module replaces its copies; no existing consumer needs an
adaptation. Current claim holders were read from `coord/claims`.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.IntegralLatticeCoefficientTransport | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.AlgebraicGeometry.LisseLatticeClassSheaf | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.AlgebraicGeometry.LisseLatticeCoefficientNormalization | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.AlgebraicGeometry.LisseLatticePresentationTransport | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.AlgebraicGeometry.LisseLatticeSliceTransport | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.LatticeClassDescent | B4 | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.LatticeClassPresheaf | B4, new | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.LatticeCosetLocalSurjectivity | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.LatticeCosetMap | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.LatticeGluedRationalization | B4, new | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.LatticeGluedRationalizationIso | B4, new | Remove both duplicate private declarations; use the existing Basic API. |
| Sheaf.Paper.LatticeMatrixNeighborhoods | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.LatticePairDescentData | B4, new | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.LatticePairEffectiveDescent | B4, new | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.LatticePairLocalMatrix | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.LatticePairMatrixAtBasis | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.LatticePairRestriction | B4, new | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.LatticeSectionMatrix | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.LatticeSheafBasic | unclaimed | Expose the existing tensor unit and naturality theorem; statements and bodies unchanged. |
| Sheaf.Paper.LatticeSheafLocallyConstant | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.Paper.LocalFreeTensorUnit | unclaimed | No use of either private name; no adaptation or mathematical change. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No use of either private name; no adaptation or mathematical change. |
| TargetsCheck | unclaimed | No use of either private name; no adaptation or mathematical change. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No use of either private name; no adaptation or mathematical change. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No use of either private name; no adaptation or mathematical change. |

## Status

landed 20261016T134405-L-3314760 2026-10-16 (merge of deliver/B4/Sheaf.Paper.LatticeClassDescent)
