module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionTensorNaturality
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionComparison

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionComparisonNaturality_localInst1 (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
noncomputable local instance TensorResolutionComparisonNaturality_localInst2 (X : Scheme.{u}) : MonoidalPreadditive X.Modules :=
  (SheafOfModules.tensorClosed X.sheaf).1.some
local instance TensorResolutionComparisonNaturality_localInst3 (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionComparisonNaturality_localInst4 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- Restrict a tensor complex and then apply the two specified chain maps. -/
noncomputable def tensorResolutionRestrictionTensorMap {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j]
    (E F : CochainComplex Y.Modules ℤ) (E' F' : CochainComplex X.Modules ℤ)
    (a : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj E ⟶ E')
    (b : ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj F ⟶ F') :
    ((Scheme.Modules.restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor E F (curriedTensor Y.Modules)) ⟶
      CochainComplex.mapBifunctor E' F' (curriedTensor X.Modules) :=
  (tensorResolutionRestrictionTotalIso j E F).hom ≫
    HomologicalComplex.mapBifunctorMap a b (curriedTensor X.Modules) (.up ℤ)


end AlgebraicGeometry
