module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartTensor
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionExtendHomology
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionSingleTensor

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry
attribute [local instance 2000] SheafOfModules.instCategory
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] TensorResolutionChartModel_localInst1 TensorResolutionChartModel_localInst2 TensorResolutionChartModel_localInst3 TensorResolutionChartModel_localInst4

/-- Ordinary resolution homology in its normalized affine tensor model. -/
noncomputable def tensorResolutionChartHomologyIso {Y : Scheme.{u}}
    (N : Y.Modules) [N.IsQuasicoherent]
    (U : Y.affineOpens) (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sN : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1)) (P : ProjectiveResolution MA) (n : ℕ) :
    tilde (R := Γ(Y, U.1))
        ((((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj P.complex).homology n) ≅
      (CochainComplex.mapBifunctor (tensorResolutionChartComplex U MA P)
        (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor Y.Modules 0).obj N))
        (curriedTensor (Spec Γ(Y, U.1)).Modules)).homology (-(n : ℤ)) := by
  let T := tilde.functor Γ(Y, U.1)
  letI : T.PreservesHomology := tilde_preservesHomology (Γ(Y, U.1) : Type u)
  let L := ((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj P.complex
  let h := tensorResolutionExtendLeftHomologyData ComplexShape.embeddingDownNat
    L (i := n) (i' := -(n : ℤ)) rfl (L.sc n).homologyData.left
  exact (h.map T).homologyIso.symm ≪≫
    (HomologicalComplex.homologyFunctor (Spec Γ(Y, U.1)).Modules (.up ℤ) (-(n : ℤ))).mapIso
      (tensorResolutionChartTensorIso N U MA NA sN P)

end AlgebraicGeometry
