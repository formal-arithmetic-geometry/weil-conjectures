module

public import Sheaf.AlgebraicGeometry.QCohTensorResolutionCoefficientMap
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionRestrictedLift
public import Sheaf.AlgebraicGeometry.QCohTensorResolutionSemilinearTensorLift

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Canonical semilinear comparison of two chosen affine tensor resolutions. -/
theorem exists_tensorResolutionCanonicalComparison
    (Y : Scheme.{u}) (M N : Y.Modules)
    (MA NA : ∀ U : Y.affineOpens, ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : ∀ U : Y.affineOpens, MA U ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (sN : ∀ U : Y.affineOpens, NA U ≃ₗ[Γ(Y, U.1)] N.val.obj (op U.1))
    (P : ∀ U : Y.affineOpens, ProjectiveResolution (MA U))
    (V U : Y.affineOpens) (h : V.1 ≤ U.1) :
    let φ := (Y.presheaf.map (homOfLE h).op).hom
    let TA := (tensorRight (NA U)).mapHomologicalComplex (.down ℕ)
    let TC := (tensorRight (NA V)).mapHomologicalComplex (.down ℕ)
    ∃ (b : NA U →ₛₗ[φ] NA V)
      (a : (P U).complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
        (.down ℕ)).obj (P V).complex)
      (k : TA.obj (P U).complex ⟶
        ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
          (TC.obj (P V).complex)),
      (∀ x : (P U).complex.X 0,
        sM V ((P V).π.f 0 (a.f 0 x)) =
          M.val.map (homOfLE h).op (sM U ((P U).π.f 0 x))) ∧
      (∀ y : NA U, sN V (b y) = N.val.map (homOfLE h).op (sN U y)) ∧
      (∀ (j : ℕ) (x : (P U).complex.X j) (y : NA U),
        k.f j (x ⊗ₜ[Γ(Y, U.1)] y) =
          (show (P V).complex.X j from a.f j x) ⊗ₜ[Γ(Y, V.1)] (b y)) := by
  classical
  dsimp only
  let φ := (Y.presheaf.map (homOfLE h).op).hom
  obtain ⟨bm, hbm⟩ := exists_tensorResolutionCoefficientMap Y M MA sM V U h
  obtain ⟨bn, hbn⟩ := exists_tensorResolutionCoefficientMap Y N NA sN V U h
  let f : MA U ⟶ (ModuleCat.restrictScalars φ).obj (MA V) :=
    ModuleCat.ofHom (X := MA U) (Y := (ModuleCat.restrictScalars φ).obj (MA V))
      { toFun := bm
        map_add' := bm.map_add
        map_smul' := bm.map_smul' }
  obtain ⟨a, ha⟩ := tensorResolutionRestrictedLift
    (Γ(Y, U.1) : Type u) (Γ(Y, V.1) : Type u) φ (MA U) (MA V) (P U) (P V) f
  obtain ⟨k, hk⟩ := tensorResolutionSemilinearTensorLift
    (Γ(Y, U.1) : Type u) (Γ(Y, V.1) : Type u) φ
    (P U).complex (P V).complex (NA U) (NA V) a bn
  refine ⟨bn, a, k, ?_, hbn, hk⟩
  intro x
  have hx := congrArg (fun g ↦ g x) ha
  exact (congrArg (sM V) hx).trans (hbm ((P U).π.f 0 x))

end AlgebraicGeometry
