/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.GlobalTensorPullbackMatesIsIso
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.LocalizedOpenTensorEquivalence
import WeilConjectures.AlgebraicGeometry.OpenRestrictionKFlatModel
import WeilConjectures.AlgebraicGeometry.OpenRestrictionTotalTensor
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

/-! # K-flat tensor models under localized open restriction

## References

* [Stacks, Tag 06YC](https://stacks.math.columbia.edu/tag/06YC)
* [Stacks, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

@[instance_reducible]
private noncomputable def loktr_localizedTensor (X : Scheme.{u}) (U : X.Opens) :
    MonoidalCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
  SheafOfModules.monoidalCategory (X.sheaf.over U)

attribute [local instance] loktr_localizedTensor

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance loktr_globalTensorZero (X : Scheme.{u}) :
    (@curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _
            (SheafOfModules.monoidalCategory X.sheaf)).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf

local instance loktr_globalTensorObjZero (X : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    ((@curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _
            (SheafOfModules.monoidalCategory X.sheaf)).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

local instance loktr_localTensorZero (X : Scheme.{u}) (U : X.Opens) :
    (@curriedTensor (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) _
          (SheafOfModules.monoidalCategory (X.sheaf.over U))).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor (X.sheaf.over U)

local instance loktr_localTensorObjZero (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :
    ((@curriedTensor (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) _
          (SheafOfModules.monoidalCategory (X.sheaf.over U))).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj (X.sheaf.over U) M

attribute [local instance] Scheme.Modules.globalPullbackMatesColimits

local instance loktr_localColimits (X : Scheme.{u}) (U : X.Opens) :
    CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) := inferInstance

local instance loktr_globalTotal (X : Scheme.{u})
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    HomologicalComplex.HasMapBifunctor P N
      (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)) (.up ℤ) :=
  fun _ ↦ inferInstance

local instance loktr_localTotal (X : Scheme.{u}) (U : X.Opens)
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ) :
    HomologicalComplex.HasMapBifunctor A B
      (@curriedTensor _ _ (SheafOfModules.monoidalCategory (X.sheaf.over U))) (.up ℤ) :=
  fun _ ↦ inferInstance

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem localizedEquiv_totalTensor_iso (X : Scheme.{u}) (U : X.Opens)
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ) :
    let E := Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    Nonempty (((E.mapHomologicalComplex (.up ℤ)).obj
      (CochainComplex.mapBifunctor A B (curriedTensor _))) ≅
      CochainComplex.mapBifunctor ((E.mapHomologicalComplex (.up ℤ)).obj A)
        ((E.mapHomologicalComplex (.up ℤ)).obj B) (curriedTensor _)) := by
  let E := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv U)
  let K := (((curriedTensor
    (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))).mapBifunctorHomologicalComplex
      (.up ℤ) (.up ℤ)).obj A).obj B
  have : E.PreservesTotalComplex K (.up ℤ) := fun _ ↦ inferInstance
  let e₁ := (HomologicalComplex₂.mapTotalIso E K (.up ℤ)).symm
  obtain ⟨e, he⟩ := exists_localizedOpen_tensor_equivalence X U
  let e₂ :
      (((E.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℤ)).obj K) ≅
        (((curriedTensor (SheafOfModules.{u}
          (moduleRings U.toScheme.toRingedSpace))).mapBifunctorHomologicalComplex
            (.up ℤ) (.up ℤ)).obj ((E.mapHomologicalComplex (.up ℤ)).obj A)).obj
              ((E.mapHomologicalComplex (.up ℤ)).obj B) :=
    HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ HomologicalComplex.Hom.isoOfComponents (fun q ↦ e (A.X p) (B.X q))
        (by
          intro q q' hq
          change (e (A.X p) (B.X q)).hom ≫ E.obj (A.X p) ◁ E.map (B.d q q') =
            E.map (A.X p ◁ B.d q q') ≫ (e (A.X p) (B.X q')).hom
          simpa [E] using (he (A.X p) (A.X p) (B.X q) (B.X q') (𝟙 _) (B.d q q')).symm))
      (by
        intro p p' hp
        apply HomologicalComplex.Hom.ext
        funext q
        change (e (A.X p) (B.X q)).hom ≫ E.map (A.d p p') ▷ E.obj (B.X q) =
          E.map (A.d p p' ▷ B.X q) ≫ (e (A.X p') (B.X q)).hom
        simpa [E] using (he (A.X p) (A.X p') (B.X q) (B.X q) (A.d p p') (𝟙 _)).symm)
  exact ⟨e₁ ≪≫ HomologicalComplex₂.total.mapIso e₂ (.up ℤ)⟩

-- The localized-site tensor carrier needs additional elaboration steps.
/-- Exact open restriction preserves K-flatness and the total tensor model.
(Stacks, Tags 06YC, 01CD, 08DX) -/
theorem localizedOpen_kFlat_tensor_restriction (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (hN : CochainComplex.IsKFlatTensor (R := X.sheaf) N) :
    let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
    let P' := (R.mapHomologicalComplex (.up ℤ)).obj P
    let N' := (R.mapHomologicalComplex (.up ℤ)).obj N
    CochainComplex.IsKFlatTensor (R := X.sheaf.over U) P' ∧
      CochainComplex.IsKFlatTensor (R := X.sheaf.over U) N' ∧
      Nonempty (R.mapDerivedCategory.obj
        (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P N
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor P' N'
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory (X.sheaf.over U))))) := by
  let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  let E := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
    (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv U)
  let RC := R.mapHomologicalComplex (.up ℤ)
  let EC := E.mapHomologicalComplex (.up ℤ)
  have hrestrict (K : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
      (hK : CochainComplex.IsKFlatTensor (R := X.sheaf) K) :
      CochainComplex.IsKFlatTensor (R := X.sheaf.over U) (RC.obj K) := by
    have h := openRestriction_isKFlat X U K hK
    change ∀ F : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
      F.Acyclic → (CochainComplex.mapBifunctor F (RC.obj K)
        (@curriedTensor _ _ (SheafOfModules.monoidalCategory (X.sheaf.over U)))).Acyclic
    intro F hF i
    obtain ⟨e⟩ := localizedEquiv_totalTensor_iso X U F (RC.obj K)
    have hEF : (EC.obj F).Acyclic := fun j ↦ (hF j).map E
    have hT := (h (EC.obj F) hEF i).of_iso e.symm
    exact ((CochainComplex.mapBifunctor F (RC.obj K) (curriedTensor _)).sc i
      |>.exact_map_iff_of_faithful E).mp hT
  refine ⟨hrestrict P hP, hrestrict N hN, ?_⟩
  obtain ⟨e⟩ := openRestriction_totalTensor_iso X U P N
  obtain ⟨t⟩ := localizedEquiv_totalTensor_iso X U (RC.obj P) (RC.obj N)
  let e' : RC.obj (CochainComplex.mapBifunctor P N (curriedTensor _)) ≅
      CochainComplex.mapBifunctor (RC.obj P) (RC.obj N) (curriedTensor _) :=
    EC.preimageIso (e ≪≫ t.symm)
  exact ⟨(R.mapDerivedCategoryFactors.app
    (CochainComplex.mapBifunctor P N (curriedTensor _))) ≪≫
      DerivedCategory.Q.mapIso e'⟩

end AlgebraicGeometry
