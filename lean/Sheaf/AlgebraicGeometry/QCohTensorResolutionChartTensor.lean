module
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionChartAugmentation
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

/-- The affine tensor model, with target the literal restricted second coefficient. -/
noncomputable def tensorResolutionChartTensorIso {Y : Scheme.{u}}
    (N : Y.Modules) [N.IsQuasicoherent]
    (U : Y.affineOpens) (MA NA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sN : NA ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1)) (P : ProjectiveResolution MA) :
    ((tilde.functor Γ(Y, U.1)).mapHomologicalComplex (.up ℤ)).obj
        ((((tensorRight NA).mapHomologicalComplex (.down ℕ)).obj P.complex).extend
          ComplexShape.embeddingDownNat) ≅
      CochainComplex.mapBifunctor (tensorResolutionChartComplex U MA P)
        (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor Y.Modules 0).obj N))
        (curriedTensor (Spec Γ(Y, U.1)).Modules) := by
  let A := (Γ(Y, U.1) : Type u)
  let X := Spec Γ(Y, U.1)
  let E := P.complex.extend ComplexShape.embeddingDownNat
  let T := tilde.functor Γ(Y, U.1)
  letI : T.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  let TC := T.mapHomologicalComplex (.up ℤ)
  let R := Scheme.Modules.restrictFunctor U.2.fromSpec
  let S := CochainComplex.singleFunctor X.Modules 0
  let c := tensorResolutionMapExtendIso (tensorRight NA)
    ComplexShape.embeddingDownNat P.complex
  let d := (Functor.mapHomologicalComplexCompIso
    (tensorResolutionTildeTensorRightIso A NA) (.up ℤ)).app E
  let t := (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor X.Modules)
    (tilde (R := Γ(Y, U.1)) NA) (TC.obj E)).symm
  let eN := S.mapIso (tensorResolutionChartModel N U NA sN) ≪≫
    ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).app N).symm
  exact TC.mapIso c.symm ≪≫ d ≪≫ t ≪≫
    ((curriedTensor X.Modules).map₂CochainComplex.obj (TC.obj E)).mapIso eN


end AlgebraicGeometry
