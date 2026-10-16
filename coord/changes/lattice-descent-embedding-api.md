# pairEmbedding and pairTensorMap

## Reason

The existing integral embedding and tensor map are needed by the explicit compatible-tuple descent construction. They were private. Make these unchanged constructions public and expose proved locality APIs; no mathematical definition or old public signature changes. LatticeSheafBasic is unclaimed. The second reading also caches the already available additive slice sheafification and local-bijectivity instances as two named local instances; this avoids repeated instance searches after both the unchanged baseline and the delivery timed out under machine load. Their attributes are local, and no old signature or data body changes.

## Old

```lean
private noncomputable def pairTensorMap (P : IntegralLatticePair a L U) :
    SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (latticeScalarMap a U) P.module ⟶ (L.over U).val :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (S.over U)).obj)) P.rationalization.hom
```

```lean
private noncomputable def pairEmbedding (P : IntegralLatticePair a L U) :
    P.module ⟶ (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (latticeScalarMap a U))).obj (L.over U) where
  val :=
    { app T := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{u + 1, u + 1, u + 1}
        ((latticeScalarMap a U).hom.app T).hom ((pairTensorMap a L U P).app T)
      naturality := by
        intro T T' f
        ext m
        change (pairTensorMap a L U P).app T'
          ((1 : (S.over U).obj.obj T') ⊗ₜ[(R.over U).obj.obj T',
            ((latticeScalarMap a U).hom.app T').hom] P.module.val.map f m) =
            (L.over U).val.map f ((pairTensorMap a L U P).app T
              ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
                ((latticeScalarMap a U).hom.app T).hom] m))
        have hn := PresheafOfModules.naturality_apply (pairTensorMap a L U P) f
          ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
            ((latticeScalarMap a U).hom.app T).hom] m)
        have hm := Classical.choose_spec
          (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1}
            (latticeScalarMap a U) P.module f) (1 : (S.over U).obj.obj T) m
        change (pairTensorMap a L U P).app T'
          (SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
            (latticeScalarMap a U) P.module f _) = _ at hn
        change SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
          (latticeScalarMap a U) P.module f
            ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
              ((latticeScalarMap a U).hom.app T).hom] m) = _ at hm
        rw [hm, map_one] at hn
        exact hn }
```

## New

```lean
noncomputable def pairTensorMap (P : IntegralLatticePair a L U) :
    SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
      (latticeScalarMap a U) P.module ⟶ (L.over U).val :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (S.over U)).obj)) P.rationalization.hom
```

```lean
noncomputable def pairEmbedding (P : IntegralLatticePair a L U) :
    P.module ⟶ (SheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (latticeScalarMap a U))).obj (L.over U) where
  val :=
    { app T := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{u + 1, u + 1, u + 1}
        ((latticeScalarMap a U).hom.app T).hom ((pairTensorMap a L U P).app T)
      naturality := by
        intro T T' f
        ext m
        change (pairTensorMap a L U P).app T'
          ((1 : (S.over U).obj.obj T') ⊗ₜ[(R.over U).obj.obj T',
            ((latticeScalarMap a U).hom.app T').hom] P.module.val.map f m) =
            (L.over U).val.map f ((pairTensorMap a L U P).app T
              ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
                ((latticeScalarMap a U).hom.app T).hom] m))
        have hn := PresheafOfModules.naturality_apply (pairTensorMap a L U P) f
          ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
            ((latticeScalarMap a U).hom.app T).hom] m)
        have hm := Classical.choose_spec
          (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1}
            (latticeScalarMap a U) P.module f) (1 : (S.over U).obj.obj T) m
        change (pairTensorMap a L U P).app T'
          (SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
            (latticeScalarMap a U) P.module f _) = _ at hn
        change SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1}
          (latticeScalarMap a U) P.module f
            ((1 : (S.over U).obj.obj T) ⊗ₜ[(R.over U).obj.obj T,
              ((latticeScalarMap a U).hom.app T).hom] m) = _ at hm
        rw [hm, map_one] at hn
        exact hn }
```

The new proved APIs are `IntegralLatticePair.embedding_injective`, `map_mem_image`, and `mem_image_of_locally_mem`. They expose consequences of the unchanged embedding. `latticeWeakSheafifyOver` and `latticeWEqualsOver` cache existing Mathlib instances, both proved by `infer_instance`; they introduce no mathematical assumption and are not registered as instances outside this module.

## Users

`tools/downstream.py Sheaf.Paper.LatticeSheafBasic --uses pairEmbedding` and the analogous command for `pairTensorMap` each found only LatticeSheafBasic itself (22 and 6 occurrences respectively). Its 28 downstream modules have no textual uses of either formerly private name. All original consumers retain exactly the same statements and definitions.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.LatticeSheafBasic | unclaimed | Two private definitions become public with identical bodies; three proved APIs and two local instance caches added. |
| Sheaf.AlgebraicGeometry.IntegralLatticeCoefficientTransport | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.LisseLatticeClassSheaf | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.LisseLatticeCoefficientNormalization | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.LisseLatticeEtaleLocal | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.LisseLatticePresentationTransport | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.LisseLatticeSliceTransport | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.ContinuousAffineEtaleLattice | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.ContinuousEtaleLocalLattices | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.ContinuousLisseStratifiedLattices | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingLattices | E4 | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.ContinuousModuleEncodingLocalFreeness | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.LatticeClassDescent | B4 | Original theorem signature unchanged; proof uses the new descent route. |
| Sheaf.Paper.LatticeCosetLocalSurjectivity | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.LatticeCosetMap | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.LatticeMatrixNeighborhoods | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.LatticePairLocalMatrix | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.LatticePairMatrixAtBasis | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.LatticeSectionMatrix | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.LatticeSheafLocallyConstant | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.LocalFreeTensorUnit | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| TargetsCheck | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | No use of either formerly private name; original interface and data meanings unchanged; no adaptation. |
| Sheaf.Paper.LatticeClassPresheaf | B4, new | Uses the unchanged lattice API in the concrete descent construction. |
| Sheaf.Paper.LatticeGluedRationalization | B4, new | Uses the unchanged lattice API in the concrete descent construction. |
| Sheaf.Paper.LatticeGluedRationalizationIso | B4, new | Uses the unchanged lattice API in the concrete descent construction. |
| Sheaf.Paper.LatticePairDescentData | B4, new | Uses the unchanged lattice API in the concrete descent construction. |
| Sheaf.Paper.LatticePairEffectiveDescent | B4, new | Uses the unchanged lattice API in the concrete descent construction. |
| Sheaf.Paper.LatticePairRestriction | B4, new | Uses the unchanged lattice API in the concrete descent construction. |

No target meaning changes: the only existing data definitions touched retain their bodies verbatim.

## Status

landed 20261016T134405-L-3314760 2026-10-16 (merge of deliver/B4/Sheaf.Paper.LatticeClassDescent)
