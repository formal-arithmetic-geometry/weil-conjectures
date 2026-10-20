module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartRestriction
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionExtendHomology
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionSingleTensor

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
attribute [local instance 2000] SheafOfModules.instCategory
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionChartModel_localInst1 (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionChartModel_localInst2 (X : Scheme.{u}) : MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionChartModel_localInst3 (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionChartModel_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- The sheafified nonpositive resolution on a specified affine chart. -/
noncomputable abbrev tensorResolutionChartComplex {Y : Scheme.{u}}
    (U : Y.affineOpens) (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (P : ProjectiveResolution MA) : CochainComplex (Spec Γ(Y, U.1)).Modules ℤ :=
  ((tilde.functor Γ(Y, U.1)).mapHomologicalComplex (.up ℤ)).obj
    (P.complex.extend ComplexShape.embeddingDownNat)

/-- The augmentation to the literal restriction of the coefficient complex. -/
noncomputable def tensorResolutionChartAugmentation {Y : Scheme.{u}}
    (M : Y.Modules) [M.IsQuasicoherent]
    (U : Y.affineOpens) (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1)) (P : ProjectiveResolution MA) :
    tensorResolutionChartComplex U MA P ⟶
      ((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor Y.Modules 0).obj M) :=
  tensorResolutionTildeAugmentation _ MA P ≫
    (CochainComplex.singleFunctor (Spec Γ(Y, U.1)).Modules 0).map
      (tensorResolutionChartModel M U MA sM).hom ≫
    ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.restrictFunctor U.2.fromSpec) (.up ℤ) 0).app M).inv

instance tensorResolutionChartAugmentation_quasiIso {Y : Scheme.{u}}
    (M : Y.Modules) [M.IsQuasicoherent]
    (U : Y.affineOpens) (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1)) (P : ProjectiveResolution MA) :
    QuasiIso (tensorResolutionChartAugmentation M U MA sM P) := by
  let f := tensorResolutionTildeAugmentation (Γ(Y, U.1) : Type u) MA P
  let g := (CochainComplex.singleFunctor (Spec Γ(Y, U.1)).Modules 0).map
    (tensorResolutionChartModel M U MA sM).hom
  let t := ((HomologicalComplex.singleMapHomologicalComplex
    (Scheme.Modules.restrictFunctor U.2.fromSpec) (.up ℤ) 0).app M).inv
  haveI : QuasiIso f := tensorResolutionTildeAugmentation_quasiIso _ MA P
  haveI : IsIso g := by dsimp [g]; infer_instance
  haveI : IsIso t := by dsimp [t]; infer_instance
  change QuasiIso (f ≫ g ≫ t)
  infer_instance


end AlgebraicGeometry
