module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionHomologyCoherence

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance TensorResolutionCoordinateSheafIso_localInst1 (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance TensorResolutionCoordinateSheafIso_localInst2 (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance TensorResolutionCoordinateSheafIso_localInst3 (X : Scheme.{u}) (M : X.Modules) :
    ((curriedTensor X.Modules).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

set_option maxHeartbeats 800000 in
/-- The comparison on the affine chart before commuting restriction and homology. -/
noncomputable def tensorResolutionCoordinateChartIso
    (Y : Scheme.{u}) (M N : Y.Modules) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (U : Y.affineOpens) (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : MA ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sN : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ProjectiveResolution MA) (K F : CochainComplex Y.Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj M)
    (s : F ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj N)
    (hK : CochainComplex.IsAcyclicTensorKFlat (R := Y.sheaf) K)
    (hF : CochainComplex.IsAcyclicTensorKFlat (R := Y.sheaf) F)
    (hq : QuasiIso q) (hs : QuasiIso s) (n : ℕ) :
    tilde (R := Γ(Y, U.1))
        ((((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj P.complex).homology n) ≅
      (CochainComplex.mapBifunctor
        (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj K)
        (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor Y.Modules 0).obj N))
        (curriedTensor (Spec Γ(Y, U.1)).Modules)).homology (-(n : ℤ)) := by
  exact tensorResolutionChartHomologyIso N U MA NA sN P n ≪≫
    tensorResolutionChartComparisonIso Y M N U MA sM P K F q s hK hF hq hs (-(n : ℤ))

end AlgebraicGeometry
