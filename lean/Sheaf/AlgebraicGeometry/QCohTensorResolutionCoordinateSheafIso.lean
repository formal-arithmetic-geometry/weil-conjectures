module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionCoordinateChartIso
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionHomologyCoherence

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] TensorResolutionCoordinateSheafIso_localInst1 TensorResolutionCoordinateSheafIso_localInst2 TensorResolutionCoordinateSheafIso_localInst3

/-- Affine ordinary tensor coordinates obtained through one global second resolution. -/
noncomputable def tensorResolutionCoordinateSheafIso
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
      (Scheme.Modules.restrictFunctor U.2.fromSpec).obj
        ((CochainComplex.mapBifunctor K
          ((CochainComplex.singleFunctor Y.Modules 0).obj N)
          (curriedTensor Y.Modules)).homology (-(n : ℤ))) := by
  exact tensorResolutionCoordinateChartIso Y M N U MA NA sM sN P K F q s hK hF hq hs n ≪≫
    (tensorResolutionNormalizedRestrictHomologyIso U.2.fromSpec K
      ((CochainComplex.singleFunctor Y.Modules 0).obj N) (-(n : ℤ))).symm

end AlgebraicGeometry
