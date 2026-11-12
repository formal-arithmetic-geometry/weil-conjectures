/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionTotalCoherence
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparisonNaturality

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionHomologyCoherence_localInst1 (X : Scheme.{u}) :
  MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionHomologyCoherence_localInst2 (X : Scheme.{u}) :
  MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionHomologyCoherence_localInst3 (X : Scheme.{u}) :
  (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionHomologyCoherence_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

-- Tensor-resolution comparisons require substantial definitional reduction.
/-- Normalized restriction of ordinary total tensor homology. -/
noncomputable def tensorResolutionNormalizedRestrictHomologyIso {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (E F : CochainComplex Y.Modules ℤ) (i : ℤ) :
    (Scheme.Modules.restrictFunctor j).obj
        ((CochainComplex.mapBifunctor E F (curriedTensor Y.Modules)).homology i) ≅
      (CochainComplex.mapBifunctor
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E)
        (((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F)
        (curriedTensor X.Modules)).homology i :=
  (((CochainComplex.mapBifunctor E F (curriedTensor Y.Modules)).sc i).mapHomologyIso
    (Scheme.Modules.restrictFunctor j)).symm ≪≫
  (HomologicalComplex.homologyFunctor X.Modules (.up ℤ) i).mapIso
    (tensorResolutionRestrictionTotalIso j E F)

-- Tensor-resolution comparisons require substantial definitional reduction.
set_option profiler true in
/-- Nested chart restriction is compatible with normalized tensor homology. -/
theorem tensorResolutionNormalizedRestrictHomologyIso_naturality
    (Y : Scheme.{u}) (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (E F : CochainComplex Y.Modules ℤ) (i : ℤ)
    (hc :
      ((Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE
        h).op))).mapHomologicalComplex
        (.up ℤ)).map (tensorResolutionRestrictionTotalIso U.2.fromSpec E F).hom ≫
        tensorResolutionRestrictionTensorMap (Spec.map (Y.presheaf.map (homOfLE h).op))
          (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj E)
          (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj F)
          (((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj E)
          (((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj F)
          (tensorResolutionChartRestrictionComplexIso Y V U h E).hom
          (tensorResolutionChartRestrictionComplexIso Y V U h F).hom =
      (tensorResolutionChartRestrictionComplexIso Y V U h
        (CochainComplex.mapBifunctor E F (curriedTensor Y.Modules))).hom ≫
          (tensorResolutionRestrictionTotalIso V.2.fromSpec E F).hom) :
    let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let R := Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))
    R.map (tensorResolutionNormalizedRestrictHomologyIso U.2.fromSpec E F i).hom ≫
      (((CochainComplex.mapBifunctor (RU.obj E) (RU.obj F)
        (curriedTensor (Spec Γ(Y, U.1)).Modules)).sc i).mapHomologyIso R).inv ≫
      HomologicalComplex.homologyMap
        (tensorResolutionRestrictionTensorMap (Spec.map (Y.presheaf.map (homOfLE h).op))
          (RU.obj E) (RU.obj F)
          (((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj E)
          (((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj F)
          (tensorResolutionChartRestrictionComplexIso Y V U h E).hom
          (tensorResolutionChartRestrictionComplexIso Y V U h F).hom) i =
      (tensorResolutionChartRestrictionIso Y V U h).hom.app
        ((CochainComplex.mapBifunctor E F (curriedTensor Y.Modules)).homology i) ≫
          (tensorResolutionNormalizedRestrictHomologyIso V.2.fromSpec E F i).hom := by
  dsimp only
  let A := CochainComplex.mapBifunctor E F (curriedTensor Y.Modules)
  let RU := Scheme.Modules.restrictFunctor U.2.fromSpec
  let RV := Scheme.Modules.restrictFunctor V.2.fromSpec
  let R := Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op))
  have h₁ := tensorResolution_homology_square R (.up ℤ) i
    (tensorResolutionRestrictionTotalIso U.2.fromSpec E F).hom
    (tensorResolutionRestrictionTotalIso V.2.fromSpec E F).hom
    (tensorResolutionChartRestrictionComplexIso Y V U h A).hom _ hc
  have h₂ := tensorResolution_homology_composition RU R RV
    (tensorResolutionChartRestrictionIso Y V U h).hom (A.sc i)
  dsimp only [tensorResolutionNormalizedRestrictHomologyIso, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp]
  dsimp only [HomologicalComplex.homologyFunctor]
  rw [Functor.map_comp]
  rw [Category.assoc]
  change R.map ((A.sc i).mapHomologyIso RU).inv ≫
    R.map (HomologicalComplex.homologyMap
      (tensorResolutionRestrictionTotalIso U.2.fromSpec E F).hom i) ≫ _ = _
  have h₁' := congrArg (fun f ↦ R.map ((A.sc i).mapHomologyIso RU).inv ≫ f) h₁
  refine h₁'.trans ?_
  change R.map ((A.sc i).mapHomologyIso RU).inv ≫
    (((A.sc i).map RU).mapHomologyIso R).inv ≫
      ShortComplex.homologyMap ((A.sc i).mapNatTrans
        (tensorResolutionChartRestrictionIso Y V U h).hom) ≫ _ = _
  rw [reassoc_of% h₂]
  rfl

end AlgebraicGeometry
