# Integral residue tensor comparison API

## Reason

Prove the tensor route using the canonical tensor counit and proved defining/projection
equations. Every existing declaration signature, declaration kind and mathematical
construction is retained. In particular the original comparison interface, coefficient,
pullback, derived monoidal structure, tensor presentation, tensor model target and tensor
model map are unchanged. The target theorem has its original signature byte for byte.

The new IntegralResidueTensorCounit module gives the explicit ordinary coefficient and its canonical counit
names. The counit property and all comparison equations are proved. Data are explicit
constructions, with no arbitrary witness of unproved existence. The generic model uses
DerivedCategory.braidedCategory, the upstream alias for the same derived braiding;
its public import is needed by the new normalization theorem's statement. Local
transparency annotations and elaboration options affect no exported instance.

The new generic tensor-route theorem and ordinary braiding specialization are fully proved
in IntegralResidueTensorRouteGeneric with their own node. The proved counit API has its
own module and node; IntegralResidueTensorPresentation is unchanged. No hole is split off. The generic braiding alias is definitionally the same construction, but any target definition
review affected by the model's instance alias or the generic monoidal constructor
is reopened for maintainer verification.

## Old

The existing generic model braiding was

```lean
local instance : BraidedCategory (DerivedCategory D) :=
  DerivedMonoidal.braidedCategory (DerivedCategory.Qh (C := D))
    (HomotopyCategory.quasiIso D (.up ℤ))
```

All concrete definitions retain their original bodies. The generic
`CategoryTheory.Functor.residueDerivedMonoidal` formerly ended with the direct
`(CoreMonoidal.ofOplaxMonoidal _).toMonoidal` constructor after installing its oplax
structure and the two comparison isomorphisms. The APIs below were absent.

## New

The generic model uses the canonical upstream alias for that same structure:

```lean
local instance : BraidedCategory (DerivedCategory D) := DerivedCategory.braidedCategory D
```

It publicly imports WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
for the normalization statement. The generic monoidal constructor additionally uses `Monoidal.copy` to expose the
canonical tensor field and avoid expensive normalization of concrete internal modules.
Its four field equalities are all `rfl`, so the data are unchanged:

```lean
@[instance_reducible] noncomputable def residueDerivedMonoidal :
    F.leftDerivedFunctor.Monoidal := by
  let m : F.leftDerivedFunctor.Monoidal := by
    letI := residueDerivedOplax F
    haveI := residueDerivedOplax_isIso_δ F
    haveI := residueDerivedOplax_isIso_η F
    exact (CoreMonoidal.ofOplaxMonoidal _).toMonoidal
  letI := m
  exact m.copy (LaxMonoidal.ε _) (LaxMonoidal.μ _)
    (OplaxMonoidal.η _) (fun X Y ↦ (F.leftDerivedTensorComparison.app X).app Y)
    rfl rfl rfl rfl
```

The model retains its original presentation import and publicly imports the new counit
API because its new comparison statements use that API. The following proved APIs are
added to the supporting modules. Their source/proof docstrings and DAG declarations accompany this delivery.

In the new `Sheaf.Paper.IntegralResidueTensorCounit` (the first theorem is in
`CategoryTheory.Mod`):

```lean
theorem residueDerivedTensorIso_eq :
    letI := Mod.tensorPresentationDerivedCounit_isLeftDerivedFunctor φ
    residueDerivedTensorIso φ =
      CategoryTheory.derivedTensorPresentationIso _ _ (Mod.tensorPresentationDerivedCounit φ) := by
  unfold residueDerivedTensorIso
  rfl
```

```lean
noncomputable abbrev residueExchangeOrdinaryCoefficientObj (T : Scheme.{u}) :=
  (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
    (Mod.regular (condensedRingObj
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T))
```

```lean
@[irreducible] noncomputable def residueExchangeTensorCounit (T : Scheme.{u}) :
    DerivedCategory.Qh ⋙ (residueExchangeReduction ℓ E T ⋙
      residueExchangeRestriction ℓ E T) ⟶
    (tensorLeft (residueExchangeOrdinaryCoefficientObj ℓ E T)).mapHomotopyCategory
      (.up ℤ) ⋙ DerivedCategory.Qh := by
  unfold residueExchangeOrdinaryCoefficientObj
  unfold residueExchangeReduction integralReduction residueExchangeRestriction
  exact Mod.tensorPresentationDerivedCounit (coefficientMap (integralReductionMap ℓ E) T)
```

```lean
theorem residueExchangeTensorCounit_isLeftDerivedFunctor (T : Scheme.{u}) :
    (residueExchangeReduction ℓ E T ⋙ residueExchangeRestriction ℓ E T).IsLeftDerivedFunctor
      (residueExchangeTensorCounit ℓ E T)
      (HomotopyCategory.quasiIso
        (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
          (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ)) := by
  unfold residueExchangeOrdinaryCoefficientObj residueExchangeTensorCounit
    residueExchangeReduction integralReduction
    residueExchangeRestriction
  exact Mod.tensorPresentationDerivedCounit_isLeftDerivedFunctor
    (coefficientMap (integralReductionMap ℓ E) T)
```

```lean
theorem residueExchangeTensorIso_eq (T : Scheme.{u}) :
    letI := residueExchangeTensorCounit_isLeftDerivedFunctor ℓ E T
    residueExchangeTensorIso ℓ E T =
      derivedTensorPresentationIso (residueExchangeOrdinaryCoefficientObj ℓ E T)
        (residueExchangeReduction ℓ E T ⋙ residueExchangeRestriction ℓ E T)
        (residueExchangeTensorCounit ℓ E T) := by
  unfold residueExchangeTensorIso residueExchangeTensorCounit
    residueExchangeOrdinaryCoefficientObj residueExchangeReduction integralReduction
    residueExchangeRestriction
  exact Mod.residueDerivedTensorIso_eq (coefficientMap (integralReductionMap ℓ E) T)
```

In `Sheaf.Paper.IntegralResidueTensorModel`:

```lean
theorem derivedTensorPresentationIso_normalization (B : C)
    (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (P : HomotopyCategory C (.up ℤ)) :
    letI := DerivedCategory.braidedCategory C
    (derivedTensorPresentationIso B H ε).hom.app (DerivedCategory.Qh.obj P) ≫
      (β_ ((DerivedCategory.singleFunctor C 0).obj B) (DerivedCategory.Qh.obj P)).inv ≫
      ((tensorModelCoefficientIso B).hom ▷ DerivedCategory.Qh.obj P) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh (tensorModelCoefficient B) P =
    ε.app P ≫ DerivedCategory.Qh.map ((homotopyTensorSingleIso B).inv.app P) := by
  let := DerivedCategory.braidedCategory C
  unfold derivedTensorPresentationIso derivedTensorSingleIso
  simp only [Iso.trans_hom, NatTrans.comp_app, BraidedCategory.tensorLeftIsoTensorRight,
    Category.assoc, Iso.hom_inv_id_assoc]
  dsimp only [Functor.mapIso_hom, Iso.symm_hom, curriedTensor_map_app]
  change _ ≫ _ ≫ (tensorModelCoefficientIso B).inv ▷ _ ≫
    (tensorModelCoefficientIso B).hom ▷ _ ≫ _ = _
  rw [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  change _ ≫ _ ≫ (DerivedCategory.tensorLeftQhObjCounit
    (tensorModelCoefficient B)).app P = _
  simp only [Functor.leftDerivedNatIso_hom]
  rw [Functor.leftDerivedNatTrans_app]
  simp only [Functor.isoWhiskerRight_hom, Iso.symm_hom, Functor.whiskerRight_app]
  rw [Functor.leftDerivedNatTrans_app_assoc]
  simp
```

```lean
theorem residueExchangeTensorModelTarget_eq :
    residueExchangeTensorModelTarget ℓ E f P =
      Functor.tensorModelTarget (f)^*⟦integralCoeff ℓ E⟧
        (residueExchangeOrdinaryCoefficient ℓ E Y) P := by
  unfold residueExchangeTensorModelTarget residueExchangeUpperStar
  rfl
```

```lean
theorem residueExchangeTensorModelMap_eq :
    letI := residueExchangeOrdinaryPullMonoidal ℓ E f
    residueExchangeTensorModelMap ℓ E f P =
      Functor.tensorModelMap (f)^*⟦integralCoeff ℓ E⟧
        (residueExchangeOrdinaryCoefficient ℓ E Y)
        (residueExchangeReduction ℓ E Y ⋙ residueExchangeRestriction ℓ E Y)
        (residueExchangeTensorCounit ℓ E Y) P := by
  unfold residueExchangeTensorModelMap residueExchangeUpperStar residueExchangeTensorCounit
  rfl
```

In `Sheaf.Paper.IntegralResidueDerivedMonoidal`:

```lean
theorem residueDerivedMonoidal_δ (K M : DerivedCategory C) :
    letI := F.residueDerivedMonoidal
    Functor.OplaxMonoidal.δ F.leftDerivedFunctor K M =
      (F.leftDerivedTensorComparison.app K).app M := by
  unfold residueDerivedMonoidal
  rfl
```

```lean
theorem residueExchangePullMonoidal_δ {X Y : Scheme.{u}} (f : X ⟶ Y)
    (m : (f)^*⟦integralCoeff ℓ E⟧.Monoidal)
    (hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat)
    (K M : residueExchangeDerived (integralCoeff ℓ E) Y) :
    letI := m
    letI := hFlat
    letI := residueExchangePullMonoidal ℓ E f m hFlat
    Functor.OplaxMonoidal.δ (residueExchangeUpperStar (integralCoeff ℓ E) f) K M =
      ((f)^*⟦integralCoeff ℓ E⟧.leftDerivedTensorComparison.app K).app M := by
  unfold residueExchangePullMonoidal residueExchangeUpperStar
  rfl
```

## Users

All transitive importers of the supporting modules are listed, including import-only
users. Existing signatures and mathematical data are preserved; no client adaptation is
part of this delivery. The only target proof changed is this item.

| Module | Group holding it | Effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResidueTensorRouteGeneric | A2 (new helper) | Use the supporting comparison API and canonical derived braiding in the proved generic calculation. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Existing statements and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Existing statements and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Existing statements and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueComparisons | unclaimed | Existing statements and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueDerivedMonoidal | unclaimed | Add proved projection/normalization API; retain existing statements and data. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Existing statements and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Existing statements and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueProjectionNormalization | unclaimed | Existing statements and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueScalarCounitModel | unclaimed | Existing statements and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueScalarGeometryBridge | unclaimed | Existing statements and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueScalarRouteModel | unclaimed | Existing statements and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorGeometry | unclaimed | Existing statements and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorModel | unclaimed | Add proved projection/normalization API; retain existing statements and data. |
| Sheaf.Paper.IntegralResidueTensorPresentation | unclaimed | Unchanged. |
| Sheaf.Paper.IntegralResidueTensorCounit | A2 (new helper) | Prove the defining counit API separately to fit the remote compiler limit. |
| Sheaf.Paper.IntegralResidueTensorPullCounitModel | unclaimed | Existing statements and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorPullPresentation | unclaimed | Existing statements and data unchanged; no adaptation. |
| Sheaf.Paper.IntegralResidueTensorRouteModel | A2 | Close the original hole using the proved generic calculation. |
| Sheaf.Paper.IntegralResidueTensorSquare | unclaimed | Existing statements and data unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Existing statements and data unchanged; no adaptation. |
| TargetsCheck | unclaimed | Existing statements and data unchanged; no adaptation. |
| WeilConjectures | unclaimed | Existing statements and data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Existing statements and data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactlySupported | unclaimed | Existing statements and data unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Existing statements and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.CompactCohomology | unclaimed | Existing statements and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Existing statements and data unchanged; no adaptation. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Existing statements and data unchanged; no adaptation. |
| WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek | unclaimed | Existing statements and data unchanged; no adaptation. |

## Status

landed 20261017T051253-L-3360851 2026-10-17 (merge of deliver/A2/Sheaf.Paper.IntegralResidueTensorRouteModel)
