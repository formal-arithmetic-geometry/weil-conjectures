/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientData
import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluation.FreeParameterScalarMaps
import all WeilConjectures.AlgebraicGeometry.FiniteConstantModel.FiniteConstantModelResolutionSupplement
import WeilConjectures.AlgebraicGeometry.FiniteConstantModel.ConstantToContinuousScalarFlat
import WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelFreeComplexReduction

/-! # Specified finite-model chart comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ZeroObject
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FiniteModelQuotient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem double_resolution {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (S : ShortComplex C) (hS : S.ShortExact) :
    Nonempty
      (DerivedCategory.Q.obj (HomologicalComplex.double S.f
        (c := ComplexShape.up ℤ) (i₀ := -1) (i₁ := 0) (by decide)) ≅
      (DerivedCategory.singleFunctor C 0).obj S.X₃) := by
  let hrel : (ComplexShape.up ℤ).Rel (-1) 0 := by decide
  let K : CochainComplex C ℤ := HomologicalComplex.double S.f hrel
  let e₁ : K.X (-1) ≅ S.X₁ := HomologicalComplex.doubleXIso₀ S.f hrel
  let e₀ : K.X 0 ≅ S.X₂ := HomologicalComplex.doubleXIso₁ S.f hrel (by decide)
  let L := (CochainComplex.singleFunctor C 0).obj S.X₃
  let e : L.X 0 ≅ S.X₃ := HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₃
  let ε : K ⟶ L := HomologicalComplex.mkHomFromDouble hrel (by decide)
    (0 : S.X₁ ⟶ L.X (-1)) (S.g ≫ e.inv)
    (by simp) (by intros; simp [L])
  have hK (i : ℤ) (h₁ : i ≠ -1) (h₀ : i ≠ 0) : IsZero (K.X i) :=
    HomologicalComplex.isZero_double_X S.f hrel i h₁ h₀
  have hd : K.d (-1) 0 = e₁.hom ≫ S.f ≫ e₀.inv :=
    HomologicalComplex.double_d S.f hrel (by decide)
  have hε : ε.f 0 = e₀.hom ≫ S.g ≫ e.inv := by
    dsimp [ε]
    simp only [HomologicalComplex.mkHomFromDouble_f₁]
    rfl
  have hqi : QuasiIso ε := by
    have hL (i : ℤ) (hi : i ≠ 0) : IsZero (L.X i) :=
      HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 S.X₃ i hi
    have hmono : Mono (K.d (-1) 0) := by
      have := hS.mono_f
      rw [hd]
      infer_instance
    have hepi : Epi (ε.f 0) := by
      have := hS.epi_g
      rw [hε]
      infer_instance
    have hw : K.d (-1) 0 ≫ ε.f 0 = 0 := by
      rw [hd, hε]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [S.zero_assoc]
      simp
    let S' := ShortComplex.mk (K.d (-1) 0) (ε.f 0) hw
    let φ : S ⟶ S' :=
      { τ₁ := e₁.inv
        τ₂ := e₀.inv
        τ₃ := e.inv
        comm₁₂ := by dsimp [S']; rw [hd]; simp
        comm₂₃ := by dsimp [S']; rw [hε]; simp }
    have : Epi φ.τ₁ := by dsimp [φ]; infer_instance
    have : IsIso φ.τ₂ := by dsimp [φ]; infer_instance
    have : Mono φ.τ₃ := by dsimp [φ]; infer_instance
    have hex : S'.Exact :=
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hS.exact
    rw [quasiIso_iff]
    intro i
    by_cases hi : i = 0
    · subst i
      rw [quasiIsoAt_iff' ε (-1) 0 1 (by simp) (by simp)]
      apply (ShortComplex.quasiIso_iff_of_zeros' _
        ((hK 1 (by decide) (by decide)).eq_of_tgt _ _)
        ((hL (-1) (by decide)).eq_of_src _ _)
        ((hL 1 (by decide)).eq_of_tgt _ _)).2
      exact ⟨hex, hepi⟩
    · have hLex : L.ExactAt i := HomologicalComplex.ExactAt.of_isZero (hL i hi)
      rw [quasiIsoAt_iff_exactAt' ε i hLex]
      by_cases hi' : i = -1
      · subst i
        rw [HomologicalComplex.exactAt_iff' K (-2) (-1) 0 (by simp) (by simp)]
        apply (ShortComplex.exact_iff_mono _
          ((hK (-2) (by decide) (by decide)).eq_of_src _ _)).2
        exact hmono
      · exact HomologicalComplex.ExactAt.of_isZero (hK i hi' hi)
  exact ⟨asIso (DerivedCategory.Q.map ε) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app S.X₃).symm⟩

private theorem model_exact (T : Scheme.{u}) :
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    PreservesFiniteLimits (FiniteConstantModel.modelFunctor (A l E) T) ∧
      PreservesFiniteColimits (FiniteConstantModel.modelFunctor (A l E) T) ∧
      (FiniteConstantModel.modelFunctor (A l E) T).Additive := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have hpid : IsPrincipalIdealRing (A l E) := by
    have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
    exact h.2.2.2.2.2.2.2.2.1
  have := hpid
  apply FiniteConstantModel.modelFunctor_exact (A l E) T
  apply FiniteConstantModel.constantToContinuous_preservesFiniteLimits (A l E)
    (FiniteConstantModel.scalarToContinuous (A l E))
  intro S a
  have h := ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
    ((Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} (A l E))))
    (Profinite.continuousCoefficientRingObj (A l E))).apply_symm_apply
      (FiniteConstantModel.constantFunctions (A l E))
  exact ConcreteCategory.congr_hom (congr_app h S) a

end AlgebraicGeometry.ProEtale.FiniteModelQuotient
