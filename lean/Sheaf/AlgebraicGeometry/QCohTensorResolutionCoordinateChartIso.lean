/- Copyright (c) 2026 The SHEAF contributors. All rights reserved. -/
module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionCoordinateSheafIso

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
attribute [local instance 2000] SheafOfModules.instCategory
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionCoordinateChartIso_monoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance TensorResolutionCoordinateChartIso_zero (X : Scheme.{u}) :
    (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionCoordinateChartIso_objZero (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

/-- The comparison on the affine chart before commuting restriction and homology. -/
noncomputable def tensorResolutionCoordinateChartIso
    (Y : Scheme.{u}) (M N : Y.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (U : Y.affineOpens) (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sN : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ProjectiveResolution MA) (K F : CochainComplex Y.Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj M)
    (s : F ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj N)
    (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K)
    (hF : CochainComplex.IsKFlatTensor (R := Y.sheaf) F)
    (hq : QuasiIso q) (hs : QuasiIso s) (n : ℕ) :
    tilde (R := Γ(Y, U.1))
        ((((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj P.complex).homology n) ≅
      (CochainComplex.mapBifunctor
        (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj K)
        (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor Y.Modules 0).obj N))
        (curriedTensor (Spec Γ(Y, U.1)).Modules)).homology (-(n : ℤ)) := by
  -- The full coordinates end in inverse normalization; normalize to cancel it.
  -- This keeps the large tensor-comparison composite bundled during elaboration.
  refine tensorResolutionCoordinateSheafIso Y M N U MA NA sM sN P K F q s hK hF hq hs n ≪≫ ?_
  exact tensorResolutionNormalizedRestrictHomologyIso U.2.fromSpec K
    ((CochainComplex.singleFunctor Y.Modules 0).obj N) (-(n : ℤ))

end AlgebraicGeometry
