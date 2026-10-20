/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.FiniteFreeCompletedScalarComparison
public import Sheaf.Paper.IntegralScalarExtension
public import Sheaf.Paper.DerivedCompleteIntegralDetailed
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.CompletedIntegralCoefficientGerm
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.Paper.IntegralScalarExtensionConstructible
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.SfDerivedCompleteLegacyComparison
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Sheaf.NumberTheory.Padics.IntegersProfiniteTower
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Sheaf.Paper.ScalarExtensionComposition
import Mathlib.LinearAlgebra.TensorProduct.Map
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Sections of the geometric point and integral coefficient extension

Source: blueprint `def-weil-finite-coefficient-point`, final paragraph;
Bhatt--Scholze, Lemmas 4.2.12, 6.8.2(1), Definition 3.4.10 and Lemma 3.4.12
(blueprint: lem-weil-point-sections-scalar-extension).

All tensors on coefficient modules below are ordinary termwise tensors. The
sections-tensor arrow is fixed on pure tensors, and the derived arrow is fixed
on every K-flat flat-term representative. Completion uses the recorded strict
zero-homotopy comparison, rather than an unspecified derived-limit lift.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u a b c r w v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

namespace WeilConjectures

private theorem pointFlatTensor_exact {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : f.Flat) :
    (ModuleCat.extendScalars.{u, u, u + 1} f).Additive ∧
      PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u + 1} f) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u + 1} f) := by
  let T := ModuleCat.extendScalars.{u, u, u + 1} f
  have : T.Additive :=
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} f).left_adjoint_additive
  refine ⟨inferInstance, (T.exact_tfae.out 1 3).mp ?_⟩
  intro S hS
  let := f.toAlgebra
  have : Module.Flat A B := hf
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact Module.Flat.lTensor_exact B hS

private theorem pointModuleId_apply {A : Type u} [CommRing A]
    (N : ModuleCat.{u + 1} A) (a : A) (n : N) :
    (ModuleCat.extendScalarsId.{u, u + 1} A).hom.app N
      (a ⊗ₜ[A, RingHom.id A] n) = a • n := by
  have h := ((ModuleCat.extendScalarsId.{u, u + 1} A).hom.app N).hom.map_smul a
    ((1 : A) ⊗ₜ[A, RingHom.id A] n)
  simp only [ModuleCat.extendScalarsId_hom_app_one_tmul] at h
  change (ModuleCat.extendScalarsId.{u, u + 1} A).hom.app N
    ((a * 1) ⊗ₜ[A, RingHom.id A] n) = a • n at h
  simpa only [mul_one] using h

private theorem pointModuleComp_apply {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (N : ModuleCat.{u + 1} A) (c : C) (n : N) :
    (ModuleCat.extendScalarsComp.{u, u + 1} f g).hom.app N
      (c ⊗ₜ[A, g.comp f] n) = c ⊗ₜ[B, g] ((1 : B) ⊗ₜ[A, f] n) := by
  have h := ((ModuleCat.extendScalarsComp.{u, u + 1} f g).hom.app N).hom.map_smul c
    ((1 : C) ⊗ₜ[A, g.comp f] n)
  simp only [ModuleCat.extendScalarsComp_hom_app_one_tmul] at h
  change (ModuleCat.extendScalarsComp.{u, u + 1} f g).hom.app N
    ((c * 1) ⊗ₜ[A, g.comp f] n) =
      (c * 1) ⊗ₜ[B, g] ((1 : B) ⊗ₜ[A, f] n) at h
  simpa only [mul_one] using h

private theorem pointModuleAssoc_apply {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (N : ModuleCat.{u + 1} A) (b : C) (a : B) (n : N) :
    (ModuleCat.extendScalarsComp.{u, u + 1} f g).inv.app N
      (b ⊗ₜ[B, g] (a ⊗ₜ[A, f] n)) = (b * g a) ⊗ₜ[A, g.comp f] n := by
  let e := ModuleCat.extendScalarsComp.{u, u + 1} f g
  have hone : e.inv.app N ((1 : C) ⊗ₜ[B, g] ((1 : B) ⊗ₜ[A, f] n)) =
      (1 : C) ⊗ₜ[A, g.comp f] n := by
    rw [← ModuleCat.extendScalarsComp_hom_app_one_tmul.{u, u + 1} f g N n]
    exact ConcreteCategory.congr_hom (e.hom_inv_id_app N) _
  have hinner : a ⊗ₜ[A, f] n =
      a • ((1 : B) ⊗ₜ[A, f] n : (ModuleCat.extendScalars f).obj N) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  have houter (x : (ModuleCat.extendScalars f).obj N) :
      b ⊗ₜ[B, g] (a • x) =
        (b * g a) • ((1 : C) ⊗ₜ[B, g] x :
          (ModuleCat.extendScalars g).obj ((ModuleCat.extendScalars f).obj N)) := by
    let := g.toAlgebra
    rw [← TensorProduct.smul_tmul]
    change (g a * b) ⊗ₜ[B, g] x = _
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one, mul_comm]
  rw [hinner, houter, map_smul, hone, ModuleCat.ExtendScalars.smul_tmul, mul_one]

private noncomputable def pointSheafScalarIso
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {R S : Sheaf J CommRingCat.{u}} (φ ψ : R ⟶ S) (hφ : φ = ψ)
    (F G : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (hF : ∀ N, F.obj N = SheafOfModules.changeOfRings φ N)
    (hFm : ∀ {N N'} (f : N ⟶ N'), F.map f = eqToHom (hF N) ≫
      SheafOfModules.changeOfRingsHom φ N f ≫ eqToHom (hF N').symm)
    (hG : ∀ N, G.obj N = SheafOfModules.changeOfRings ψ N)
    (hGm : ∀ {N N'} (f : N ⟶ N'), G.map f = eqToHom (hG N) ≫
      SheafOfModules.changeOfRingsHom ψ N f ≫ eqToHom (hG N').symm) : F ≅ G := by
  subst ψ
  exact NatIso.ofComponents (fun N ↦ eqToIso ((hF N).trans (hG N).symm)) (by
    intro N N' f
    dsimp only [eqToIso.hom]
    rw [hFm f, hGm f]
    simp)

private theorem pointSheafScalarEq
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {R S : Sheaf J CommRingCat.{u}} (φ ψ : R ⟶ S) (hφ : φ = ψ)
    (F G : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (hF : ∀ N, F.obj N = SheafOfModules.changeOfRings φ N)
    (hFm : ∀ {N N'} (f : N ⟶ N'), F.map f = eqToHom (hF N) ≫
      SheafOfModules.changeOfRingsHom φ N f ≫ eqToHom (hF N').symm)
    (hG : ∀ N, G.obj N = SheafOfModules.changeOfRings ψ N)
    (hGm : ∀ {N N'} (f : N ⟶ N'), G.map f = eqToHom (hG N) ≫
      SheafOfModules.changeOfRingsHom ψ N f ≫ eqToHom (hG N').symm) : F = G := by
  apply Functor.ext_of_iso
    (pointSheafScalarIso φ ψ hφ F G hF (fun f ↦ hFm f) hG (fun f ↦ hGm f))
    (fun N ↦ (hF N).trans
      ((congrArg (fun α ↦ SheafOfModules.changeOfRings α N) hφ).trans (hG N).symm))

section Transfer
variable {C : Type*} [Category C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    {R S T : Sheaf J CommRingCat.{u}}
private noncomputable def pointChosenTensorSection (φ : R ⟶ S)
    (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (hF : ∀ N, F.obj N = SheafOfModules.changeOfRings φ N)
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : N.val.obj U) : (F.obj N).val.obj U :=
  (eqToHom (hF N).symm).val.app U
    ((toSheafify J (SheafOfModules.changeOfRingsPresheaf φ N).presheaf).app U
      (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
private def pointChosenTensorAssocProperty (φ : R ⟶ S) (ψ : S ⟶ T) (γ : R ⟶ T)
    (F : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (G : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (H : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (hF : ∀ N, F.obj N = SheafOfModules.changeOfRings φ N)
    (hG : ∀ N, G.obj N = SheafOfModules.changeOfRings ψ N)
    (hH : ∀ N, H.obj N = SheafOfModules.changeOfRings γ N) : Prop :=
  ∃! α : F ⋙ G ≅ H,
    ∀ (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
      (U : Cᵒᵖ) (a : S.obj.obj U) (b : T.obj.obj U) (x : N.val.obj U),
      (α.hom.app N).val.app U
        (pointChosenTensorSection ψ G hG (F.obj N) U b
          (pointChosenTensorSection φ F hF N U a x)) =
        pointChosenTensorSection γ H hH N U (b * ψ.hom.app U a) x

private theorem pointChosenTensorAssocProperty_congr
    (φ φ' : R ⟶ S) (ψ ψ' : S ⟶ T) (γ γ' : R ⟶ T)
    (eφ : φ = φ') (eψ : ψ = ψ') (eγ : γ = γ')
    (F F' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S))
    (G G' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (H H' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj T))
    (eF : F = F') (eG : G = G') (eH : H = H')
    (hF : ∀ N, F.obj N = SheafOfModules.changeOfRings φ N)
    (hF' : ∀ N, F'.obj N = SheafOfModules.changeOfRings φ' N)
    (hG : ∀ N, G.obj N = SheafOfModules.changeOfRings ψ N)
    (hG' : ∀ N, G'.obj N = SheafOfModules.changeOfRings ψ' N)
    (hH : ∀ N, H.obj N = SheafOfModules.changeOfRings γ N)
    (hH' : ∀ N, H'.obj N = SheafOfModules.changeOfRings γ' N) :
    pointChosenTensorAssocProperty φ ψ γ F G H hF hG hH ↔
      pointChosenTensorAssocProperty φ' ψ' γ' F' G' H' hF' hG' hH' := by
  subst φ'
  subst ψ'
  subst γ'
  subst F'
  subst G'
  subst H'
  rfl
end Transfer

variable (k : Type u) [Field k] [IsAlgClosed k]
  (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The recorded abelian sheafification at the point's actual module size.
Source: Stacks 03DA (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance (priority := 5000) pointScalarAbSheafify :
    HasSheafify (Scheme.ProEt.topology (Spec (.of k))) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} (Spec (.of k))

/-- The recorded locally bijective criterion at the point's actual module size.
Source: Stacks 03DA (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance (priority := 5000) pointScalarAbLocallyBijective :
    (Scheme.ProEt.topology (Spec (.of k))).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} (Spec (.of k))

/-- Standard localization of coefficient-module complexes in the section universe.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointScalarModuleDerived (A : Type u) [Ring A] :
    HasDerivedCategory (ModuleCat.{u + 1} A) := HasDerivedCategory.standard _

/-- Standard localization for modules on the point in their actual section universe.
Source: Stacks 05RU (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedSheafDerived
    (R : Sheaf (Scheme.ProEt.topology (Spec (.of k))) RingCat.{u + 1}) :
    HasDerivedCategory (SheafOfModules.{u + 1} R) := HasDerivedCategory.standard _

/-- The canonical constant-section coefficient map at the final object, obtained
from the recorded constant-to-completion morphism and sheafification unit.
Source: Bhatt--Scholze 6.8.2(1); blueprint completed coefficients, order 1455
(blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointCompletedConstant :
    Padic.coefficientExtensionIntegers l E →+*
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k))).obj.obj
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) :=
  (((integralConstantToCompletion l E (Spec (.of k))).hom.app
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))).hom).comp
      ((((forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((toSheafify (Scheme.ProEt.topology (Spec (.of k)))
          ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))))).app
              (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))))).hom).comp
                ULift.ringEquiv.symm.toRingHom)

/-- Evaluation, with coefficients restricted along the actual constant-section map.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointCompletedSections :
    integralTowerModules.{u, u} l E (Spec (.of k)) ⥤
      ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E) :=
  SheafOfModules.evaluation.{u + 1}
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k)))
      (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) ⋙
    ModuleCat.restrictScalars (pointCompletedConstant k l E)

/-- Exactness and additivity of completed integral sections.
Source: exact point-sections node and blueprint final paragraph
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: point evaluation is exact by lem-weil-point-proetale-sections-exact.
Restriction of scalars leaves the underlying abelian group unchanged, so preserves
kernels and cokernels. Both functors add maps sectionwise. -/
theorem pointCompletedSections_exact :
    (pointCompletedSections k l E).Additive ∧
      PreservesFiniteLimits (pointCompletedSections k l E) ∧
      PreservesFiniteColimits (pointCompletedSections k l E) := by
  have h := (ProEtale.point_proEtale_sections_exact.{u, u + 1, u + 1} k).2
    (completedIntegralCommRingSheafUnrestricted.{u, u} l E (Spec (.of k)))
  let : PreservesFiniteLimits
      (SheafOfModules.evaluation.{u + 1}
        (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k)))
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) := h.1
  let : PreservesFiniteColimits
      (SheafOfModules.evaluation.{u + 1}
        (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k)))
        (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))) := h.2.1
  have : PreservesFiniteLimits (ModuleCat.restrictScalars.{u + 1}
      (pointCompletedConstant k l E)) :=
    ⟨fun _ _ _ ↦ ⟨fun {_} ↦ inferInstance⟩⟩
  have : PreservesFiniteColimits (ModuleCat.restrictScalars.{u + 1}
      (pointCompletedConstant k l E)) :=
    ⟨fun _ _ _ ↦ ⟨fun {_} ↦ inferInstance⟩⟩
  dsimp only [pointCompletedSections]
  refine ⟨⟨?map_add⟩, inferInstance, inferInstance⟩
  case map_add => intros; rfl

/-- Additivity supplied by exact evaluation.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedSectionsAdditive :
    (pointCompletedSections k l E).Additive := (pointCompletedSections_exact k l E).1

/-- Finite-limit preservation supplied by exact evaluation.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedSectionsLimits :
    PreservesFiniteLimits (pointCompletedSections k l E) :=
  (pointCompletedSections_exact k l E).2.1

/-- Finite-colimit preservation supplied by exact evaluation.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedSectionsColimits :
    PreservesFiniteColimits (pointCompletedSections k l E) :=
  (pointCompletedSections_exact k l E).2.2

/-- Termwise completed sections, descended through derived localization.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointCompletedDerivedSections :
    DerivedCategory (integralTowerModules.{u, u} l E (Spec (.of k))) ⥤
      DerivedCategory (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) :=
  (pointCompletedSections k l E).mapDerivedCategory

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

/-- Ordinary tensor with the valuation ring of the larger coefficient field.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointIntegralModuleTensor :=
  ModuleCat.extendScalars.{u, u, u + 1} (integralScalarIntegerInclusion.{u} l E L ι)

/-- The ordinary module tensor and fraction-field tensor functors are exact and additive.
Source: Bhatt--Scholze 6.8.2(1), blueprint final paragraph
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: O_L is finite free over O_E, so tensor is a finite direct sum, hence exact.
The fraction field of a valuation DVR is its localization at nonzero elements;
localization preserves kernels and cokernels. The tensor maps add termwise. -/
theorem pointCoefficientTensors_exact :
    ((pointIntegralModuleTensor l E L ι).Additive ∧
      PreservesFiniteLimits (pointIntegralModuleTensor l E L ι) ∧
      PreservesFiniteColimits (pointIntegralModuleTensor l E L ι)) ∧
    ((ModuleCat.extendScalars.{u, u, u + 1}
      (algebraMap (Padic.coefficientExtensionIntegers l E) E)).Additive ∧
      PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u + 1}
        (algebraMap (Padic.coefficientExtensionIntegers l E) E)) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u + 1}
        (algebraMap (Padic.coefficientExtensionIntegers l E) E))) := by
  have h := (Padic.extension_integers_dvr l E
    (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have : IsPrincipalIdealRing (Padic.coefficientExtensionIntegers l E) :=
    h.2.2.2.2.2.2.2.2.1
  constructor
  · apply pointFlatTensor_exact
    let := (integralScalarIntegerInclusion l E L ι).toAlgebra
    have hinj : Function.Injective (integralScalarIntegerInclusion l E L ι) := by
      intro a b hab
      apply Subtype.ext
      exact ι.injective (congrArg Subtype.val hab)
    have : Module.IsTorsionFree (Padic.coefficientExtensionIntegers l E)
        (Padic.coefficientExtensionIntegers l L) :=
      (Module.isTorsionFree_iff_algebraMap_injective).mpr hinj
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  · apply pointFlatTensor_exact
    exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- Additivity of the ordinary integral tensor.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointIntegralModuleTensorAdditive :
    (pointIntegralModuleTensor l E L ι).Additive :=
  (pointCoefficientTensors_exact l E L ι).1.1

/-- Exactness at kernels of the ordinary integral tensor.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointIntegralModuleTensorLimits :
    PreservesFiniteLimits (pointIntegralModuleTensor l E L ι) :=
  (pointCoefficientTensors_exact l E L ι).1.2.1

/-- Exactness at cokernels of the ordinary integral tensor.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointIntegralModuleTensorColimits :
    PreservesFiniteColimits (pointIntegralModuleTensor l E L ι) :=
  (pointCoefficientTensors_exact l E L ι).1.2.2

/-- Ordinary termwise integral tensor on module derived categories.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointIntegralModuleDerivedTensor :=
  (pointIntegralModuleTensor l E L ι).mapDerivedCategory

section GenericCoefficientSquare
variable {A B : Type a} {R S : Type r}
  [CommRing A] [CommRing B] [CommRing R] [CommRing S]
  (eA : A ≃+* R) (eB : B ≃+* S) (f : A →+* B) (φ : R →+* S)
  (hc : eB.toRingHom.comp f = φ.comp eA.toRingHom)
private noncomputable def pointSquareComponent (N : ModuleCat.{max w a r} R) :
    (ModuleCat.extendScalars f).obj ((ModuleCat.restrictScalars eA.toRingHom).obj N) ≅
      (ModuleCat.restrictScalars eB.toRingHom).obj ((ModuleCat.extendScalars φ).obj N) := by
  letI : RingHomInvPair eA.toRingHom eA.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv eA
  letI : RingHomInvPair eA.symm.toRingHom eA.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm eA
  let := f.toAlgebra
  let := φ.toAlgebra
  let NA := (ModuleCat.restrictScalars.{max w a r} eA.toRingHom).obj N
  let e₁ : B ≃ₛₗ[eA.toRingHom] S :=
    { eB.toAddEquiv with
      map_smul' := fun a b ↦ by
        change eB (f a * b) = φ (eA a) * eB b
        rw [map_mul]
        exact congrArg (fun z ↦ z * eB b) (RingHom.congr_fun hc a) }
  let e₂ : NA ≃ₛₗ[eA.toRingHom] N :=
    { Equiv.refl _ with
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let e := TensorProduct.congr e₁ e₂
  let e' : (ModuleCat.extendScalars f).obj NA ≃ₗ[B]
      (ModuleCat.restrictScalars eB.toRingHom).obj ((ModuleCat.extendScalars φ).obj N) :=
    { e.toAddEquiv with
      map_smul' := fun b t ↦ by
        change e (b • t) = eB b • e t
        induction t using TensorProduct.induction_on with
        | zero => simp only [smul_zero, map_zero]
        | tmul b' n =>
          change B at b'
          change e ((b * b') ⊗ₜ[A] n) = eB b • e (b' ⊗ₜ[A] n)
          simp only [e, TensorProduct.congr_tmul]
          change eB (b * b') ⊗ₜ[R] n = (eB b * eB b') ⊗ₜ[R] n
          rw [map_mul]
        | add t t' ht ht' => simp only [smul_add, map_add, ht, ht'] }
  exact e'.toModuleIso
private theorem pointSquareComponent_tmul
    (N : ModuleCat.{max w a r} R) (b : B) (n : N) :
    (pointSquareComponent eA eB f φ hc N).hom
      (b ⊗ₜ[A, f] (show (ModuleCat.restrictScalars eA.toRingHom).obj N from n)) =
        eB b ⊗ₜ[R, φ] n := by rfl
private noncomputable def pointSquareIso :
    ModuleCat.restrictScalars.{max w a r} eA.toRingHom ⋙ ModuleCat.extendScalars f ≅
      ModuleCat.extendScalars φ ⋙ ModuleCat.restrictScalars eB.toRingHom :=
  NatIso.ofComponents (pointSquareComponent eA eB f φ hc) (by
    intro N N' g
    apply ModuleCat.ExtendScalars.hom_ext
    intro n
    change (pointSquareComponent eA eB f φ hc N').hom
      ((1 : B) ⊗ₜ[A, f] g n) =
      (ModuleCat.extendScalars φ).map g
        ((pointSquareComponent eA eB f φ hc N).hom
          ((1 : B) ⊗ₜ[A, f] (show (ModuleCat.restrictScalars eA.toRingHom).obj N from n)))
    rw [pointSquareComponent_tmul, pointSquareComponent_tmul,
      ModuleCat.ExtendScalars.map_tmul])

private theorem pointSquareIso_tmul (N : ModuleCat.{max w a r} R) (b : B) (n : N) :
    (pointSquareIso eA eB f φ hc).hom.app N
      (b ⊗ₜ[A, f] (show (ModuleCat.restrictScalars eA.toRingHom).obj N from n)) =
        eB b ⊗ₜ[R, φ] n := by
  exact pointSquareComponent_tmul eA eB f φ hc N b n

end GenericCoefficientSquare
private theorem pointCover_id
    {S : Sieve (ProEt.mk (𝟙 (Spec (.of k))))}
    (hS : S ∈ ProEt.topology (Spec (.of k)) _) : S (𝟙 _) := by
  obtain ⟨P, hP, hPS⟩ := ProEt.mem_topology_iff.1 hS
  obtain ⟨I, Z, f, rfl⟩ := P.exists_eq_ofArrows
  have hP' : Presieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (f i).left) ∈
      proetalePrecoverage (Spec (.of k)) := by
    simpa only [ProEt.mem_precoverage_iff, Presieve.map_ofArrows,
      Functor.comp_obj, Functor.comp_map, ProEt.forget, MorphismProperty.Over.forget,
      MorphismProperty.Comma.forget, Over.forget, Comma.fst, ProEt.mk,
      MorphismProperty.Over.mk] using hP
  have hp := (ofArrows_mem_precoverage_iff _).1
    (propQCPrecoverage_le_precoverage _ hP')
  obtain ⟨i, x, hx⟩ := hp.1 (default : PrimeSpectrum k)
  have : WeaklyEtale (f i).left := hp.2 i
  obtain ⟨σ, hσ⟩ := exists_comp_eq_id_of_weaklyEtale (f i).left x
  let σ' : ProEt.mk (𝟙 (Spec (.of k))) ⟶ Z i :=
    MorphismProperty.Over.homMk σ (by
      rw [← MorphismProperty.Over.w (f i)]
      change σ ≫ (f i).left ≫ 𝟙 _ = 𝟙 _
      simpa only [Category.comp_id] using hσ)
  have h := S.downward_closed (hPS _ _ ⟨i⟩) σ'
  convert h using 1
  apply MorphismProperty.Over.Hom.ext
  exact hσ.symm
private theorem pointAbUnit_bijective
    (P : (Spec (.of k)).ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Function.Bijective ((toSheafify (ProEt.topology (Spec (.of k))) P).app
      (op (ProEt.mk (𝟙 (Spec (.of k)))))) := by
  refine ⟨fun x y hxy ↦ ?_, fun s ↦ ?_⟩
  · have hh := pointCover_id k
      (Presheaf.equalizerSieve_mem (ProEt.topology (Spec (.of k)))
        (toSheafify _ P) x y hxy)
    change P.map (𝟙 _) x = P.map (𝟙 _) y at hh
    simpa only [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using hh
  · obtain ⟨t, ht⟩ := pointCover_id k
      (Presheaf.imageSieve_mem (ProEt.topology (Spec (.of k))) (toSheafify _ P) s)
    change (toSheafify _ P).app _ t = (sheafify _ P).map (𝟙 _) s at ht
    rw [CategoryTheory.Functor.map_id] at ht
    exact ⟨t, ht⟩
private theorem pointCommRingUnit_bijective
    (P : (Spec (.of k)).ProEtᵒᵖ ⥤ CommRingCat.{u + 1}) :
    Function.Bijective ((toSheafify (ProEt.topology (Spec (.of k))) P).app
      (op (ProEt.mk (𝟙 (Spec (.of k)))))) := by
  refine ⟨fun x y hxy ↦ ?_, fun s ↦ ?_⟩
  · have hh := pointCover_id k
      (Presheaf.equalizerSieve_mem (ProEt.topology (Spec (.of k)))
        (toSheafify _ P) x y hxy)
    change P.map (𝟙 _) x = P.map (𝟙 _) y at hh
    simpa only [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using hh
  · obtain ⟨t, ht⟩ := pointCover_id k
      (Presheaf.imageSieve_mem (ProEt.topology (Spec (.of k))) (toSheafify _ P) s)
    change (toSheafify _ P).app _ t = (sheafify _ P).map (𝟙 _) s at ht
    rw [CategoryTheory.Functor.map_id] at ht
    exact ⟨t, ht⟩

private noncomputable def pointConstantUnit (A : CommRingCat.{u + 1}) :
    A →+* (((constantSheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}).obj A).obj.obj
      (op (ProEt.mk (𝟙 (Spec (.of k)))))) :=
  ((toSheafify (ProEt.topology (Spec (.of k)))
    ((Functor.const (Spec (.of k)).ProEtᵒᵖ).obj A)).app
      (op (ProEt.mk (𝟙 (Spec (.of k)))))).hom
omit [IsAlgClosed k] in
private theorem pointConstantUnit_naturality {A B : CommRingCat.{u + 1}} (f : A ⟶ B) (a : A) :
    (((constantSheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}).map f).hom.app
      (op (ProEt.mk (𝟙 (Spec (.of k)))))) (pointConstantUnit k A a) =
        pointConstantUnit k B (f a) := by
  exact (congrArg (fun η ↦ (η.app (op (ProEt.mk (𝟙 (Spec (.of k)))))) a)
    (toSheafify_naturality (ProEt.topology (Spec (.of k)))
      ((Functor.const (Spec (.of k)).ProEtᵒᵖ).map f))).symm
private noncomputable def pointLevelEquiv (n : ℕ) :
    ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)) ≃+*
      (integralCoefficientSheaf.{u, u} l E (Spec (.of k)) n).obj.obj
        (op (ProEt.mk (𝟙 (Spec (.of k))))) :=
  RingEquiv.ofBijective
    (pointConstantUnit k (.of (ULift.{u + 1, u}
      (Padic.coefficientExtensionRing l E (n + 1)))))
    (pointCommRingUnit_bijective k _)
private theorem pointLevelEquiv_transition (n : ℕ)
    (x : (integralCoefficientSheaf.{u, u} l E (Spec (.of k)) (n + 1)).obj.obj
      (op (ProEt.mk (𝟙 (Spec (.of k)))))) :
    (pointLevelEquiv k l E n).symm
      ((integralCoefficientSheafTransition.{u, u} l E (Spec (.of k)) n).hom.app
        (op (ProEt.mk (𝟙 (Spec (.of k))))) x) =
      ULift.up (Padic.coefficientExtensionTransition l E (n + 1)
        ((pointLevelEquiv k l E (n + 1)).symm x).down) := by
  apply (pointLevelEquiv k l E n).injective
  rw [RingEquiv.apply_symm_apply]
  conv_lhs => rw [← (pointLevelEquiv k l E (n + 1)).apply_symm_apply x]
  exact pointConstantUnit_naturality k
    (CommRingCat.ofHom ((ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).symm.toRingHom.comp
      ((Padic.coefficientExtensionTransition l E (n + 1)).comp
        (ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).toRingHom))) _

private noncomputable def pointResidue (n : ℕ)
    (x : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k))).obj.obj
      (op (ProEt.mk (𝟙 (Spec (.of k)))))) :
    Padic.coefficientExtensionRing l E (n + 1) :=
  ((pointLevelEquiv k l E n).symm
    ((limit.π (integralCoefficientSheafSystem.{u, u} l E (Spec (.of k))) (op n)).hom.app
      (op (ProEt.mk (𝟙 (Spec (.of k))))) x)).down
private theorem pointResidue_compatible
    (x : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k))).obj.obj
      (op (ProEt.mk (𝟙 (Spec (.of k)))))) (n : ℕ) :
    Padic.coefficientExtensionTransition l E (n + 1) (pointResidue k l E (n + 1) x) =
      pointResidue k l E n x := by
  let D := integralCoefficientSheafSystem.{u, u} l E (Spec (.of k))
  have hw : limit.π D (op (n + 1)) ≫
      integralCoefficientSheafTransition.{u, u} l E (Spec (.of k)) n = limit.π D (op n) := by
    simpa only [D, integralCoefficientSheafSystem,
      CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ] using
      (limit.w D (homOfLE (Nat.le_succ n)).op)
  have h := congrArg (fun f ↦ (f.hom.app (op (ProEt.mk (𝟙 (Spec (.of k)))))) x) hw
  have he := pointLevelEquiv_transition k l E n
    (((limit.π D (op (n + 1))).hom.app (op (ProEt.mk (𝟙 (Spec (.of k)))))) x)
  have he' := congrArg ULift.down he
  exact he'.symm.trans
    (congrArg (fun z ↦ ((pointLevelEquiv k l E n).symm z).down) h)
private theorem pointResidue_injective
    (x y : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k))).obj.obj
      (op (ProEt.mk (𝟙 (Spec (.of k))))))
    (h : ∀ n : ℕ, pointResidue k l E n x = pointResidue k l E n y) : x = y := by
  let D := integralCoefficientSheafSystem.{u, u} l E (Spec (.of k))
  let ev := sheafToPresheaf (ProEt.topology (Spec (.of k))) RingCat.{u + 1} ⋙
    (evaluation (Spec (.of k)).ProEtᵒᵖ RingCat.{u + 1}).obj
      (op (ProEt.mk (𝟙 (Spec (.of k)))))
  apply Concrete.isLimit_ext (D ⋙ ev) (isLimitOfPreserves ev (limit.isLimit D)) x y
  intro j
  obtain ⟨n⟩ := j
  apply (pointLevelEquiv k l E n).symm.injective
  apply ULift.down_injective
  exact h n
private noncomputable def pointResidueFamily
    (x : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k))).obj.obj
      (op (ProEt.mk (𝟙 (Spec (.of k)))))) : Padic.coefficientExtensionPositiveLimit l E :=
  ⟨fun n ↦ pointResidue k l E n x, by
    simp only [Padic.coefficientExtensionPositiveLimit, Subring.mem_iInf,
      RingHom.mem_eqLocus, RingHom.comp_apply, Pi.evalRingHom_apply]
    intro n
    exact pointResidue_compatible k l E x n⟩
private theorem pointProjection_constant (n : ℕ)
    (a : Padic.coefficientExtensionIntegers l E) :
    (limit.π (integralCoefficientSheafSystem.{u, u} l E (Spec (.of k))) (op n)).hom.app
      (op (ProEt.mk (𝟙 (Spec (.of k))))) (pointCompletedConstant k l E a) =
        pointLevelEquiv k l E n (ULift.up
          (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a)) := by
  let U := op (ProEt.mk (𝟙 (Spec (.of k))))
  let q := pointConstantUnit k
    (.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) (ULift.up a)
  have h := congrArg (fun f ↦ (f.hom.app U) q)
    (limit.lift_π (integralConstantCoefficientCone l E (Spec (.of k))) (op n))
  have hn := pointConstantUnit_naturality k
    (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
          (ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).toRingHom))) (ULift.up a)
  exact h.trans hn
private theorem pointResidue_constant (n : ℕ)
    (a : Padic.coefficientExtensionIntegers l E) :
    pointResidue k l E n (pointCompletedConstant k l E a) =
      Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a := by
  let U := op (ProEt.mk (𝟙 (Spec (.of k))))
  let q := pointConstantUnit k
    (.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) (ULift.up a)
  have h := congrArg (fun f ↦ (f.hom.app U) q)
    (limit.lift_π (integralConstantCoefficientCone l E (Spec (.of k))) (op n))
  have hn := pointConstantUnit_naturality k
    (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).symm.toRingHom.comp
        ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).comp
          (ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).toRingHom))) (ULift.up a)
  have hh : (limit.π (integralCoefficientSheafSystem.{u, u} l E (Spec (.of k))) (op n)).hom.app
      U (pointCompletedConstant k l E a) =
        pointLevelEquiv k l E n (ULift.up
          (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a)) := h.trans hn
  exact congrArg (fun z ↦ ((pointLevelEquiv k l E n).symm z).down) hh |>.trans
    (congrArg ULift.down ((pointLevelEquiv k l E n).symm_apply_apply _))
private theorem pointCompletedConstant_bijective :
    Function.Bijective (pointCompletedConstant k l E) := by
  obtain ⟨e, he, _⟩ := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).1
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply e.injective
    apply Subtype.ext
    funext n
    exact (he a n).trans ((pointResidue_constant k l E n a).symm.trans
      ((congrArg (pointResidue k l E n) hab).trans
        ((pointResidue_constant k l E n b).trans (he b n).symm)))
  · intro x
    let a := e.symm (pointResidueFamily k l E x)
    refine ⟨a, pointResidue_injective k l E _ x (fun n ↦ ?_)⟩
    exact (pointResidue_constant k l E n a).trans ((he a n).symm.trans
      (congrArg (fun z : Padic.coefficientExtensionPositiveLimit l E ↦ z.val n)
        (e.apply_symm_apply (pointResidueFamily k l E x))))
private theorem pointCompletedConstant_map
    (a : Padic.coefficientExtensionIntegers l E) :
    (completedCoefficientMap.{u, u} l E L ι (Spec (.of k))).hom.app
      (op (ProEt.mk (𝟙 (Spec (.of k))))) (pointCompletedConstant k l E a) =
        pointCompletedConstant k l L (integralScalarIntegerInclusion l E L ι a) := by
  let U := op (ProEt.mk (𝟙 (Spec (.of k))))
  apply pointResidue_injective k l L
  intro n
  have hE : (limit.π (integralCoefficientSheafSystem.{u, u} l E (Spec (.of k))) (op n)).hom.app
      U (pointCompletedConstant k l E a) =
        pointLevelEquiv k l E n (ULift.up
          (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a)) := by
    exact pointProjection_constant k l E n a
  have hp := congrArg (fun f ↦ (f.hom.app U) (pointCompletedConstant k l E a))
    ((completedCoefficientMap_existsUnique.{u, u} l E L ι (Spec (.of k))).exists.choose_spec n)
  have hn := pointConstantUnit_naturality k
    (CommRingCat.ofHom
      ((ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).symm.toRingHom.comp
        ((integralScalarQuotientMap l E L ι n).comp
          (ULift.ringEquiv : ULift.{u + 1, u} _ ≃+* _).toRingHom)))
    (ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a))
  have hproj :
      (limit.π (integralCoefficientSheafSystem.{u, u} l L (Spec (.of k))) (op n)).hom.app U
        ((completedCoefficientMap.{u, u} l E L ι (Spec (.of k))).hom.app U
          (pointCompletedConstant k l E a)) =
      pointLevelEquiv k l L n (ULift.up (Ideal.Quotient.mk
        (Padic.coefficientExtensionIdeal l L (n + 1))
          (integralScalarIntegerInclusion l E L ι a))) :=
    hp.trans ((congrArg (fun z ↦
      (integralScalarQuotientSheafMap l E L ι (Spec (.of k)) n).hom.app U z) hE).trans hn)
  exact ((congrArg (fun z ↦ ((pointLevelEquiv k l L n).symm z).down) hproj).trans
    (congrArg ULift.down ((pointLevelEquiv k l L n).symm_apply_apply _))).trans
      (pointResidue_constant k l L n _).symm
private noncomputable def pointChangeSectionsIso
    {R S : Sheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (F : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (φ.hom.app (op (ProEt.mk (𝟙 (Spec (.of k)))))).hom).obj
        (F.val.obj (op (ProEt.mk (𝟙 (Spec (.of k)))))) ≅
      (SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ F).val.obj
        (op (ProEt.mk (𝟙 (Spec (.of k))))) := by
  let P := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ F
  let η := ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose (ProEt.topology (Spec (.of k)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) (𝟙 _)).unit.app P).app
    (op (ProEt.mk (𝟙 (Spec (.of k)))))
  have hη : Function.Bijective η := pointAbUnit_bijective k P.presheaf
  have : IsIso η := (ConcreteCategory.isIso_iff_bijective η).2 hη
  exact asIso η
private theorem pointChangeSectionsIso_naturality
    {R S : Sheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}} (φ : R ⟶ S)
    {F G : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)} (f : F ⟶ G) :
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
      (φ.hom.app (op (ProEt.mk (𝟙 (Spec (.of k)))))).hom).map
        (f.val.app (op (ProEt.mk (𝟙 (Spec (.of k)))))) ≫
      (pointChangeSectionsIso k φ G).hom =
    (pointChangeSectionsIso k φ F).hom ≫
      (SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} φ F f).val.app
        (op (ProEt.mk (𝟙 (Spec (.of k))))) := by
  let a : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ F ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ G :=
    { app := fun U ↦ (ModuleCat.extendScalars (φ.hom.app U).hom).map (f.val.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ F f }
  have h := (PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose (ProEt.topology (Spec (.of k)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) (𝟙 _)).unit.naturality a
  exact congrArg (fun η ↦ η.app (op (ProEt.mk (𝟙 (Spec (.of k)))))) h
private noncomputable def pointChosenSectionsIso
    {R S : Sheaf (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (G : SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⥤
      SheafOfModules.{u + 1}
      ((sheafCompose (ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    (hG : ∀ N, G.obj N = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ N)
    (hGm : ∀ {N N'} (f : N ⟶ N'), G.map f = eqToHom (hG N) ≫
      SheafOfModules.changeOfRingsHom φ N f ≫ eqToHom (hG N').symm) :
    SheafOfModules.evaluation.{u + 1}
      ((sheafCompose (ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
        (op (ProEt.mk (𝟙 (Spec (.of k))))) ⋙
      ModuleCat.extendScalars.{u + 1, u + 1, u + 1}
        (R := R.obj.obj (op (ProEt.mk (𝟙 (Spec (.of k))))))
        (S := S.obj.obj (op (ProEt.mk (𝟙 (Spec (.of k))))))
        (φ.hom.app (op (ProEt.mk (𝟙 (Spec (.of k)))))).hom ≅
    G ⋙ SheafOfModules.evaluation.{u + 1}
      ((sheafCompose (ProEt.topology (Spec (.of k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
        (op (ProEt.mk (𝟙 (Spec (.of k))))) := by
  let U := op (ProEt.mk (𝟙 (Spec (.of k))))
  refine NatIso.ofComponents
    (fun N ↦ pointChangeSectionsIso k φ N ≪≫
      (SheafOfModules.evaluation.{u + 1}
        ((sheafCompose (ProEt.topology (Spec (.of k)))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) U).mapIso
            (eqToIso (hG N).symm)) ?_
  intro N N' f
  have hm : eqToHom (hG N).symm ≫ G.map f =
      SheafOfModules.changeOfRingsHom φ N f ≫ eqToHom (hG N').symm := by
    rw [hGm f]
    simp
  change (ModuleCat.extendScalars (φ.hom.app U).hom).map (f.val.app U) ≫
      ((pointChangeSectionsIso k φ N').hom ≫ (eqToHom (hG N').symm).val.app U) =
    (pointChangeSectionsIso k φ N).hom ≫ (eqToHom (hG N).symm ≫ G.map f).val.app U
  rw [hm]
  change _ = (pointChangeSectionsIso k φ N).hom ≫
    ((SheafOfModules.changeOfRingsHom φ N f).val.app U ≫
      (eqToHom (hG N').symm).val.app U)
  rw [← Category.assoc, pointChangeSectionsIso_naturality, Category.assoc]

attribute [local irreducible] completedScalarChangeData
  completedIntegralCoefficientSheafUnrestricted integralCoefficientSheafSystem

/-- The sections-tensor map is uniquely fixed by its balanced pure-tensor formula.
Source: Bhatt--Scholze 6.8.2(1), blueprint final paragraph
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: send a tensor n to the sheafified tensor of the constant section a with n.
The coefficient maps agree on every finite quotient, so balancing is valid.
The sheaf tensor universal property gives the map. Pure tensors generate its
source, proving uniqueness, and the same formula commutes with every sheaf map.
A finite free basis of R_L over R_E gives a global O_E-basis of O_L by evaluating
at the point; both sides are then the same finite sum of sections. -/
theorem pointSectionsTensor_existsUnique :
    ∃! θ : pointCompletedSections k l E ⋙ pointIntegralModuleTensor l E L ι ≅
        completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)) ⋙
          pointCompletedSections k l L,
      ∀ (F : integralTowerModules.{u, u} l E (Spec (.of k)))
        (a : Padic.coefficientExtensionIntegers l L)
        (n : (pointCompletedSections k l E).obj F),
        θ.hom.app F (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion.{u} l E L ι] n) =
          completedScalarTensorSection.{u, u} l E L ι (Spec (.of k)) F
            (op (Scheme.ProEt.mk (𝟙 (Spec (.of k))))) (pointCompletedConstant k l L a) n := by
  let U := op (ProEt.mk (𝟙 (Spec (.of k))))
  let RE := completedIntegralCommRingSheafUnrestricted.{u, u} l E (Spec (.of k))
  let RL := completedIntegralCommRingSheafUnrestricted.{u, u} l L (Spec (.of k))
  let eE : Padic.coefficientExtensionIntegers l E ≃+* RE.obj.obj U :=
    RingEquiv.ofBijective (pointCompletedConstant k l E) (pointCompletedConstant_bijective k l E)
  let eL : Padic.coefficientExtensionIntegers l L ≃+* RL.obj.obj U :=
    RingEquiv.ofBijective (pointCompletedConstant k l L) (pointCompletedConstant_bijective k l L)
  let φ : RE ⟶ RL := completedCoefficientMap.{u, u} l E L ι (Spec (.of k))
  have hc : eL.toRingHom.comp (integralScalarIntegerInclusion l E L ι) =
      (φ.hom.app U).hom.comp eE.toRingHom := by
    ext x
    exact (pointCompletedConstant_map k l E L ι x).symm
  let d := completedScalarChangeData.{u, u} l E L ι (Spec (.of k))
  let evalE := SheafOfModules.evaluation.{u + 1}
    ((sheafCompose (ProEt.topology (Spec (.of k)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RE) U
  let q := pointChosenSectionsIso k φ d.choose
    d.choose_spec.choose (fun f ↦ d.choose_spec.choose_spec.choose f)
  let θ := Functor.isoWhiskerLeft evalE
    (pointSquareIso.{u, u + 1, u + 1} eE eL
      (integralScalarIntegerInclusion l E L ι) (φ.hom.app U).hom hc) ≪≫
    Functor.isoWhiskerRight q (ModuleCat.restrictScalars.{u + 1, u, u + 1}
      (R := Padic.coefficientExtensionIntegers l L) (S := RL.obj.obj U) eL.toRingHom)
  have hθ (F : integralTowerModules.{u, u} l E (Spec (.of k)))
      (a : Padic.coefficientExtensionIntegers l L) (n : (pointCompletedSections k l E).obj F) :
      θ.hom.app F (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
        integralScalarIntegerInclusion l E L ι] n) =
        completedScalarTensorSection.{u, u} l E L ι (Spec (.of k)) F U
          (pointCompletedConstant k l L a) n := by
    have hs := pointSquareIso_tmul.{u, u + 1, u + 1} eE eL
      (integralScalarIntegerInclusion l E L ι) (φ.hom.app U).hom hc (F.val.obj U) a n
    exact congrArg (fun z ↦ (q.hom.app F) z) hs
  refine ⟨θ, hθ, ?_⟩
  intro θ' hθ'
  apply Iso.ext
  apply NatTrans.ext
  funext F
  apply ModuleCat.ExtendScalars.hom_ext
  intro n
  exact (hθ' F 1 n).trans (hθ F 1 n).symm

/-- The canonical balanced sections-tensor transformation.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointSectionsTensor :=
  (pointSectionsTensor_existsUnique k l E L ι).exists.choose

section PointScalarFunctorComparisons
omit [IsAlgClosed k] in
private theorem pointCompletedMap_eq :
    completedCoefficientMap.{u, u} l E L ι (Spec (.of k)) =
      integralCompletedScalarMap l E L ι (Spec (.of k)) :=
  (completedCoefficientMap_existsUnique l E L ι (Spec (.of k))).unique
    (completedCoefficientMap_existsUnique l E L ι (Spec (.of k))).exists.choose_spec
    (integralCompletedScalarMap_existsUnique l E L ι (Spec (.of k))).exists.choose_spec

omit [IsAlgClosed k] in
private theorem pointCompleted_obj
    (N : integralTowerModules.{u, u} l E (Spec (.of k))) :
    (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))).obj N =
      SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (completedCoefficientMap.{u, u} l E L ι (Spec (.of k))) N := by
  exact (completedScalarChangeData.{u, u} l E L ι (Spec (.of k))).choose_spec.choose N
omit [IsAlgClosed k] in
private theorem pointCompleted_map
    {N N' : integralTowerModules.{u, u} l E (Spec (.of k))} (g : N ⟶ N') :
    (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))).map g =
      eqToHom (pointCompleted_obj k l E L ι N) ≫
        SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
          (completedCoefficientMap.{u, u} l E L ι (Spec (.of k))) N g ≫
            eqToHom (pointCompleted_obj k l E L ι N').symm := by
  exact (completedScalarChangeData.{u, u} l E L ι (Spec (.of k))).choose_spec.choose_spec.choose g
omit [IsAlgClosed k] in
private theorem pointIntegral_obj
    (N : integralTowerModules.{u, u} l E (Spec (.of k))) :
    (integralOrdinaryScalar l E L ι (Spec (.of k))).obj N =
      SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (integralCompletedScalarMap l E L ι (Spec (.of k))) N := by
  exact (integralOrdinaryScalarWitness l E L ι (Spec (.of k))).choose_spec.choose N
omit [IsAlgClosed k] in
private theorem pointIntegral_map
    {N N' : integralTowerModules.{u, u} l E (Spec (.of k))} (g : N ⟶ N') :
    (integralOrdinaryScalar l E L ι (Spec (.of k))).map g =
      eqToHom (pointIntegral_obj k l E L ι N) ≫
        SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
          (integralCompletedScalarMap l E L ι (Spec (.of k))) N g ≫
            eqToHom (pointIntegral_obj k l E L ι N').symm := by
  exact (integralOrdinaryScalarWitness l E L ι (Spec (.of k))).choose_spec.choose_spec.choose g
omit [IsAlgClosed k] in
private theorem pointCompleted_section
    (N : integralTowerModules.{u, u} l E (Spec (.of k)))
    (U : (Spec (.of k)).ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted.{u, u} l L (Spec (.of k))).obj.obj U)
    (x : N.val.obj U) :
    pointChosenTensorSection
      (completedCoefficientMap.{u, u} l E L ι (Spec (.of k)))
      (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)))
      (pointCompleted_obj k l E L ι) N U s x =
      completedScalarTensorSection.{u, u} l E L ι (Spec (.of k)) N U s x := by
  rfl
omit [IsAlgClosed k] in
private theorem pointIntegral_section
    (N : integralTowerModules.{u, u} l E (Spec (.of k)))
    (U : (Spec (.of k)).ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted.{u, u} l L (Spec (.of k))).obj.obj U)
    (x : N.val.obj U) :
    pointChosenTensorSection
      (integralCompletedScalarMap l E L ι (Spec (.of k)))
      (integralOrdinaryScalar l E L ι (Spec (.of k)))
      (pointIntegral_obj k l E L ι) N U s x =
      integralOrdinaryTensorSection l E L ι (Spec (.of k)) N U s x := by
  rfl
attribute [local irreducible] completedOrdinaryScalarExtension integralOrdinaryScalar
omit [IsAlgClosed k] in
private theorem pointCompletedFunctor_eq :
    completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)) =
      integralOrdinaryScalar l E L ι (Spec (.of k)) := by
  exact pointSheafScalarEq.{u + 1, u + 1, u}
    (J := Scheme.ProEt.topology (Spec (.of k)))
    (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E (Spec (.of k)))
    (S := completedIntegralCommRingSheafUnrestricted.{u, u} l L (Spec (.of k)))
    _ _ (pointCompletedMap_eq k l E L ι) _ _
    (pointCompleted_obj k l E L ι) (fun f ↦ pointCompleted_map k l E L ι f)
    (pointIntegral_obj k l E L ι) (fun f ↦ pointIntegral_map k l E L ι f)

end PointScalarFunctorComparisons

set_option linter.unusedSectionVars false in
/-- Finite-free ordinary completed coefficient extension is exact.
Source: Bhatt--Scholze 6.8.2(1)
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: choose a finite free R_E-basis of R_L. Ordinary sheafified tensor is then
naturally a finite direct sum on the underlying R_E-modules. Finite sums are exact,
and restriction of scalars detects exactness. -/
theorem pointCompletedOrdinary_exact :
    PreservesFiniteLimits (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))) ∧
      PreservesFiniteColimits (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))) := by
  rw [pointCompletedFunctor_eq k l E L ι]
  exact integralOrdinaryScalar_exact l E L ι (Spec (.of k))

/-- Preservation of kernels by finite-free coefficient extension.
Source: Bhatt--Scholze 6.8.2(1)
(blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedOrdinaryLimits :
    PreservesFiniteLimits (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))) :=
  (pointCompletedOrdinary_exact k l E L ι).1

/-- Preservation of cokernels by coefficient extension.
Source: Bhatt--Scholze 6.8.2(1)
(blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCompletedOrdinaryColimits :
    PreservesFiniteColimits (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))) :=
  (pointCompletedOrdinary_exact k l E L ι).2

private theorem pointExactDerivedUnique
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (LF : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hε : LF.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))) :
    ∃! δ : LF ≅ F.mapDerivedCategory,
    ∀ P : CochainComplex C ℤ,
      δ.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P =
        ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) := by
  let := hε
  let W := HomotopyCategory.quasiIso C (.up ℤ)
  have : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts W _ F.mapDerivedCategoryFactorsh
  let δ := Functor.leftDerivedUnique (LF := LF) (LF' := F.mapDerivedCategory)
    ε F.mapDerivedCategoryFactorsh.hom W
  have hδ (P : CochainComplex C ℤ) :
      δ.hom.app (DerivedCategory.Q.obj P) ≫ F.mapDerivedCategoryFactors.hom.app P =
        ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) := by
    have h := Functor.leftDerivedNatTrans_app LF F.mapDerivedCategory ε
      F.mapDerivedCategoryFactorsh.hom W (Iso.refl _).hom
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
    rw [F.mapDerivedCategoryFactorsh_hom_app] at h
    change δ.hom.app (DerivedCategory.Q.obj P) ≫
      (F.mapDerivedCategory.map (𝟙 _) ≫ F.mapDerivedCategoryFactors.hom.app P ≫
        𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _)) =
      ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫ 𝟙 _ at h
    rw [F.mapDerivedCategory.map_id, DerivedCategory.Qh.map_id] at h
    erw [Category.comp_id, Category.id_comp, Category.comp_id,
      Category.comp_id] at h
    exact h
  refine ⟨δ, hδ, ?_⟩
  intro δ' hδ'
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro P
  exact (cancel_mono (F.mapDerivedCategoryFactors.hom.app P)).mp
    ((hδ' P).trans (hδ P).symm)


private noncomputable def pointCompletedCounitUniversalData :
    {ε : DerivedCategory.Qh ⋙ completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of k)) ⟶
      (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))).mapHomotopyCategory
        (.up ℤ) ⋙ DerivedCategory.Qh //
      (completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of k))).IsLeftDerivedFunctor ε
        (HomotopyCategory.quasiIso (integralTowerModules.{u, u} l E (Spec (.of k))) (.up ℤ))} := by
  let := (completedScalarChangeData.{u, u} l E L ι
    (Spec (.of k))).choose_spec.choose_spec.choose_spec.choose
  dsimp only [completedDerivedScalarExtension, completedOrdinaryScalarExtension,
    integralOperationsCommHasDerivedCategory, integralTowerHasDerivedCategory,
    pointCompletedSheafDerived]
  exact ⟨_, (completedScalarChangeData.{u, u} l E L ι
    (Spec (.of k))).choose_spec.choose_spec.choose_spec.choose_spec.2.2.choose_spec.choose_spec.1⟩

/-- The universal derived tensor comparison is the termwise one for a finite-free extension.
Source: Stacks 06YY and Bhatt--Scholze 6.8.2(1)
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: ordinary finite-free tensor preserves every quasi-isomorphism, not only those
between K-flat complexes. Its exact-functor localization is therefore its left derived
functor. The universal counit gives the displayed comparison, and localization at
quasi-isomorphisms makes the normalization on representatives determine it uniquely. -/
theorem pointOrdinaryDerivedComparison_existsUnique :
    ∃! δ : completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of k)) ≅
        (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))).mapDerivedCategory,
      ∀ P : CochainComplex (integralTowerModules.{u, u} l E (Spec (.of k))) ℤ,
        δ.hom.app (DerivedCategory.Q.obj P) ≫
          (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of
        k))).mapDerivedCategoryFactors.hom.app P =
            completedScalarCounit.{u, u} l E L ι (Spec (.of k)) P := by
  let d := pointCompletedCounitUniversalData k l E L ι
  obtain ⟨δ, hδ, hu⟩ := pointExactDerivedUnique
    (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)))
    (completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of k))) d.val d.property
  have hn (P : CochainComplex (integralTowerModules.{u, u} l E (Spec (.of k))) ℤ) :
      d.val.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
        completedScalarCounit.{u, u} l E L ι (Spec (.of k)) P := by rfl
  refine ⟨δ, fun P ↦ (hδ P).trans (hn P), ?_⟩
  intro δ' hδ'
  exact hu δ' (fun P ↦ (hδ' P).trans (hn P).symm)

/-- The canonical identification of ordinary derived and termwise tensor.
Source: Stacks 06YY (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointOrdinaryDerivedComparison :=
  (pointOrdinaryDerivedComparison_existsUnique k l E L ι).exists.choose

/-- The derived sections-tensor isomorphism, normalized by actual termwise tensors.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointDerivedSectionsTensor :
    pointCompletedDerivedSections k l E ⋙ pointIntegralModuleDerivedTensor l E L ι ≅
      completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of k)) ⋙
        pointCompletedDerivedSections k l L :=
  (Functor.mapDerivedCategoryCompIso
    (pointCompletedSections k l E) (pointIntegralModuleTensor l E L ι)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointSectionsTensor k l E L ι) ≪≫
    Functor.mapDerivedCategoryCompIso
      (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)))
      (pointCompletedSections k l L) ≪≫
    Functor.isoWhiskerRight (pointOrdinaryDerivedComparison k l E L ι).symm
      (pointCompletedDerivedSections k l L)

set_option linter.unusedSectionVars false in
/-- Multiplication on ordinary sheaf tensor fixes the identity-extension identification.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: multiplication s tensor x to sx is balanced and inverse to x to 1 tensor x.
These formulas commute with restrictions and sheaf maps, and tensors generate,
so they determine exactly one natural isomorphism. -/
theorem pointOrdinaryTensorUnit_existsUnique :
    ∃! μ : completedOrdinaryScalarExtension.{u, u} l E E (AlgHom.id ℚ_[l] E) (Spec (.of k)) ≅
        𝟭 (integralTowerModules.{u, u} l E (Spec (.of k))),
      ∀ (F : integralTowerModules.{u, u} l E (Spec (.of k))) (U : (Spec (.of k)).ProEtᵒᵖ)
        (a : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E (Spec (.of k))).obj.obj U)
        (x : F.val.obj U),
        (μ.hom.app F).val.app U
          (completedScalarTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) (Spec (.of k)) F U a x) =
            a • x := by
  obtain ⟨μc, hμc, hμc_unique⟩ :=
    completedScalarIdentityMultiplication_existsUnique.{u, u} l E (Spec (.of k))
  let S := HomologicalComplex.single
    (integralTowerModules.{u, u} l E (Spec (.of k))) (.up ℤ) (0 : ℤ)
  let ev := HomologicalComplex.eval
    (integralTowerModules.{u, u} l E (Spec (.of k))) (.up ℤ) (0 : ℤ)
  let μ : completedOrdinaryScalarExtension.{u, u} l E E
      (AlgHom.id ℚ_[l] E) (Spec (.of k)) ≅ 𝟭 _ :=
    NatIso.ofComponents (fun F ↦ ev.mapIso (μc.app (S.obj F))) (by
      intro F G f
      exact congrArg (fun g ↦ g.f 0) (μc.hom.naturality (S.map f)))
  refine ⟨μ, ?_, ?_⟩
  · intro F U a x
    exact hμc (S.obj F) 0 U a x
  · intro ν hν
    let νc := NatIso.mapHomologicalComplex ν (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)
    have he : νc = μc := hμc_unique νc (by
      intro P i U a x
      exact hν (P.X i) U a x)
    apply Iso.ext
    apply NatTrans.ext
    funext F
    exact congrArg (fun e ↦ (e.hom.app (S.obj F)).f 0) he

/-- The canonical ordinary multiplication isomorphism.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointOrdinaryTensorUnit :=
  (pointOrdinaryTensorUnit_existsUnique k l E).exists.choose

/-- The canonical derived multiplication isomorphism.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointDerivedTensorUnit :
    completedDerivedScalarExtension.{u, u} l E E (AlgHom.id ℚ_[l] E) (Spec (.of k)) ≅
      𝟭 (DerivedCategory (integralTowerModules.{u, u} l E (Spec (.of k)))) :=
  pointOrdinaryDerivedComparison k l E E (AlgHom.id ℚ_[l] E) ≪≫
    Functor.mapDerivedCategoryNatIso (pointOrdinaryTensorUnit k l E) ≪≫
    Functor.mapDerivedCategoryIdIso _

variable (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (κ : L →ₐ[ℚ_[l]] M)

section PointOrdinaryAssociator

attribute [local irreducible] completedOrdinaryScalarExtension integralOrdinaryScalar

set_option linter.unusedSectionVars false in
/-- The balanced sheaf-tensor associator is fixed on all iterated pure tensors.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: send b tensor (a tensor x) to b*iota(a) tensor x. Balancing proves that
this is well defined; its inverse sends c tensor x to c tensor (1 tensor x).
The two composites are identities on generators. These maps respect restrictions
and all sheaf morphisms, and their generator formulas imply uniqueness. -/
theorem pointOrdinaryTensorAssoc_existsUnique :
    ∃! α : completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)) ⋙
        completedOrdinaryScalarExtension.{u, u} l L M κ (Spec (.of k)) ≅
        completedOrdinaryScalarExtension.{u, u} l E M (κ.comp ι) (Spec (.of k)),
      ∀ (F : integralTowerModules.{u, u} l E (Spec (.of k))) (U : (Spec (.of k)).ProEtᵒᵖ)
        (a : (completedIntegralCommRingSheafUnrestricted.{u, u} l L (Spec (.of k))).obj.obj U)
        (b : (completedIntegralCommRingSheafUnrestricted.{u, u} l M (Spec (.of k))).obj.obj U)
        (x : F.val.obj U),
        (α.hom.app F).val.app U
          (completedScalarTensorSection.{u, u} l L M κ (Spec (.of k))
            ((completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))).obj F) U b
            (completedScalarTensorSection.{u, u} l E L ι (Spec (.of k)) F U a x)) =
          completedScalarTensorSection.{u, u} l E M (κ.comp ι) (Spec (.of k)) F U
            (b * (completedCoefficientMap.{u, u} l L M κ (Spec (.of k))).hom.app U a) x := by
  let Y := Spec (.of k)
  let φ := completedCoefficientMap.{u, u} l E L ι Y
  let ψ := completedCoefficientMap.{u, u} l L M κ Y
  let γ := completedCoefficientMap.{u, u} l E M (κ.comp ι) Y
  let φ' := integralCompletedScalarMap l E L ι Y
  let ψ' := integralCompletedScalarMap l L M κ Y
  let γ' := integralCompletedScalarMap l E M (κ.comp ι) Y
  have h0 : pointChosenTensorAssocProperty.{u + 1, u + 1, u}
      (J := Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E Y)
      (S := completedIntegralCommRingSheafUnrestricted.{u, u} l L Y)
      (T := completedIntegralCommRingSheafUnrestricted.{u, u} l M Y)
      φ' ψ' γ' (integralOrdinaryScalar l E L ι Y) (integralOrdinaryScalar l L M κ Y)
      (integralOrdinaryScalar l E M (κ.comp ι) Y)
      (pointIntegral_obj k l E L ι) (pointIntegral_obj k l L M κ)
      (pointIntegral_obj k l E M (κ.comp ι)) := by
    obtain ⟨α, hα, hα_unique⟩ := integralOrdinaryScalarComp_existsUnique l E L ι Y M κ
    refine ⟨α, ?_, ?_⟩
    · intro N U a b x
      erw [pointIntegral_section k l E L ι, pointIntegral_section k l L M κ,
        pointIntegral_section k l E M (κ.comp ι)]
      exact hα N U b a x
    · intro β hβ
      apply hα_unique β
      intro N U b a x
      have h := hβ N U a b x
      erw [pointIntegral_section k l E L ι, pointIntegral_section k l L M κ,
        pointIntegral_section k l E M (κ.comp ι)] at h
      exact h
  have ht := pointChosenTensorAssocProperty_congr.{u + 1, u + 1, u}
    (J := Scheme.ProEt.topology Y)
    (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E Y)
    (S := completedIntegralCommRingSheafUnrestricted.{u, u} l L Y)
    (T := completedIntegralCommRingSheafUnrestricted.{u, u} l M Y)
    φ φ' ψ ψ' γ γ'
    (pointCompletedMap_eq k l E L ι) (pointCompletedMap_eq k l L M κ)
    (pointCompletedMap_eq k l E M (κ.comp ι))
    (completedOrdinaryScalarExtension.{u, u} l E L ι Y) (integralOrdinaryScalar l E L ι Y)
    (completedOrdinaryScalarExtension.{u, u} l L M κ Y) (integralOrdinaryScalar l L M κ Y)
    (completedOrdinaryScalarExtension.{u, u} l E M (κ.comp ι) Y)
    (integralOrdinaryScalar l E M (κ.comp ι) Y)
    (pointCompletedFunctor_eq k l E L ι) (pointCompletedFunctor_eq k l L M κ)
    (pointCompletedFunctor_eq k l E M (κ.comp ι))
    (pointCompleted_obj k l E L ι) (pointIntegral_obj k l E L ι)
    (pointCompleted_obj k l L M κ) (pointIntegral_obj k l L M κ)
    (pointCompleted_obj k l E M (κ.comp ι)) (pointIntegral_obj k l E M (κ.comp ι))
  obtain ⟨α, hα, hu⟩ := ht.mpr h0
  have hn (N : integralTowerModules.{u, u} l E Y) (U : Y.ProEtᵒᵖ)
      (a : (completedIntegralCommRingSheafUnrestricted.{u, u} l L Y).obj.obj U)
      (b : (completedIntegralCommRingSheafUnrestricted.{u, u} l M Y).obj.obj U)
      (x : N.val.obj U) :
      pointChosenTensorSection ψ (completedOrdinaryScalarExtension.{u, u} l L M κ Y)
        (pointCompleted_obj k l L M κ)
        ((completedOrdinaryScalarExtension.{u, u} l E L ι Y).obj N) U b
        (pointChosenTensorSection φ (completedOrdinaryScalarExtension.{u, u} l E L ι Y)
          (pointCompleted_obj k l E L ι) N U a x) =
      completedScalarTensorSection.{u, u} l L M κ Y
        ((completedOrdinaryScalarExtension.{u, u} l E L ι Y).obj N) U b
        (completedScalarTensorSection.{u, u} l E L ι Y N U a x) := by
    exact (pointCompleted_section k l L M κ
      ((completedOrdinaryScalarExtension.{u, u} l E L ι Y).obj N) U b _).trans
      (congrArg (fun z ↦ completedScalarTensorSection.{u, u} l L M κ Y
        ((completedOrdinaryScalarExtension.{u, u} l E L ι Y).obj N) U b z)
          (pointCompleted_section k l E L ι N U a x))
  refine ⟨α, ?_, ?_⟩
  · intro N U a b x
    exact (congrArg (fun z ↦ (α.hom.app N).val.app U z) (hn N U a b x).symm).trans
      ((hα N U a b x).trans (pointCompleted_section k l E M (κ.comp ι) N U _ x))
  · intro β hβ
    apply hu β
    intro N U a b x
    exact (congrArg (fun z ↦ (β.hom.app N).val.app U z) (hn N U a b x)).trans
      ((hβ N U a b x).trans (pointCompleted_section k l E M (κ.comp ι) N U _ x).symm)

end PointOrdinaryAssociator

/-- The canonical ordinary tensor associator.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointOrdinaryTensorAssoc :=
  (pointOrdinaryTensorAssoc_existsUnique k l E L ι M κ).exists.choose

/-- The ordinary derived tensor associator, descended from the balanced maps.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointDerivedTensorAssoc :
    completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of k)) ⋙
      completedDerivedScalarExtension.{u, u} l L M κ (Spec (.of k)) ≅
      completedDerivedScalarExtension.{u, u} l E M (κ.comp ι) (Spec (.of k)) :=
  Functor.isoWhiskerRight (pointOrdinaryDerivedComparison k l E L ι) _ ≪≫
    Functor.isoWhiskerLeft _ (pointOrdinaryDerivedComparison k l L M κ) ≪≫
    (Functor.mapDerivedCategoryCompIso
      (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)))
      (completedOrdinaryScalarExtension.{u, u} l L M κ (Spec (.of k)))).symm ≪≫
    Functor.mapDerivedCategoryNatIso (pointOrdinaryTensorAssoc k l E L ι M κ) ≪≫
    (pointOrdinaryDerivedComparison k l E M (κ.comp ι)).symm

/-- The module multiplication isomorphism, for the actual identity integer inclusion.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: a tensor n maps to an; n maps to 1 tensor n. Balancing gives the two inverse
identities, naturality follows on generators, and the formula determines the map. -/
theorem pointIntegralModuleUnit_existsUnique :
    ∃! μ : pointIntegralModuleTensor l E E (AlgHom.id ℚ_[l] E) ≅
        𝟭 (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)),
      ∀ (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
        (a : Padic.coefficientExtensionIntegers l E) (n : N),
        μ.hom.app N (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion.{u} l E E (AlgHom.id ℚ_[l] E)] n) = a • n := by
  let μ : pointIntegralModuleTensor l E E (AlgHom.id ℚ_[l] E) ≅
      𝟭 (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) :=
    ModuleCat.extendScalarsId.{u, u + 1} (Padic.coefficientExtensionIntegers l E)
  have hμ (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
      (a : Padic.coefficientExtensionIntegers l E) (n : N) :
      μ.hom.app N (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
        integralScalarIntegerInclusion l E E (AlgHom.id ℚ_[l] E)] n) = a • n := by
    exact pointModuleId_apply N a n
  refine ⟨μ, hμ, ?_⟩
  intro ν hν
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply ModuleCat.ExtendScalars.hom_ext
  intro n
  exact (hν N 1 n).trans (hμ N 1 n).symm

/-- Ordinary multiplication on integral module complexes after localization.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointIntegralModuleDerivedUnit :
    pointIntegralModuleDerivedTensor l E E (AlgHom.id ℚ_[l] E) ≅
      𝟭 (DerivedCategory (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))) :=
  Functor.mapDerivedCategoryNatIso
    (pointIntegralModuleUnit_existsUnique l E).exists.choose ≪≫
      Functor.mapDerivedCategoryIdIso _

/-- The module associator is the ordinary balanced multiplication of coefficient factors.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: send b tensor (a tensor n) to b*kappa(a) tensor n, with inverse c tensor n
to c tensor (1 tensor n). Balancing proves the inverse identities and naturality;
generators determine the map uniquely. -/
theorem pointIntegralModuleAssoc_existsUnique :
    ∃! α : pointIntegralModuleTensor l E L ι ⋙ pointIntegralModuleTensor l L M κ ≅
        pointIntegralModuleTensor l E M (κ.comp ι),
      ∀ (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
        (a : Padic.coefficientExtensionIntegers l L)
        (b : Padic.coefficientExtensionIntegers l M) (n : N),
        α.hom.app N
          (b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
            integralScalarIntegerInclusion.{u} l L M κ]
            (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              integralScalarIntegerInclusion.{u} l E L ι] n)) =
          (b * integralScalarIntegerInclusion.{u} l L M κ a) ⊗ₜ[
            Padic.coefficientExtensionIntegers l E,
            integralScalarIntegerInclusion.{u} l E M (κ.comp ι)] n := by
  let α : pointIntegralModuleTensor l E L ι ⋙ pointIntegralModuleTensor l L M κ ≅
      pointIntegralModuleTensor l E M (κ.comp ι) :=
    (ModuleCat.extendScalarsComp.{u, u + 1}
      (integralScalarIntegerInclusion l E L ι)
      (integralScalarIntegerInclusion l L M κ)).symm
  have hα (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
      (a : Padic.coefficientExtensionIntegers l L)
      (b : Padic.coefficientExtensionIntegers l M) (n : N) :
      α.hom.app N
          (b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
            integralScalarIntegerInclusion l L M κ]
            (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              integralScalarIntegerInclusion l E L ι] n)) =
        (b * integralScalarIntegerInclusion l L M κ a) ⊗ₜ[
          Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion l E M (κ.comp ι)] n :=
    pointModuleAssoc_apply _ _ N b a n
  refine ⟨α, hα, ?_⟩
  intro β hβ
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | tmul a n => exact (hβ N a 1 n).trans (hα N a 1 n).symm
  | add x y hx hy => simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy


/-- The ordinary module-complex associator in the derived category.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointIntegralModuleDerivedAssoc :
    pointIntegralModuleDerivedTensor l E L ι ⋙ pointIntegralModuleDerivedTensor l L M κ ≅
      pointIntegralModuleDerivedTensor l E M (κ.comp ι) :=
  (Functor.mapDerivedCategoryCompIso
    (pointIntegralModuleTensor l E L ι) (pointIntegralModuleTensor l L M κ)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose

/-- Fraction-field extension on coefficient modules.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointModuleRationalization :=
  ModuleCat.extendScalars.{u, u, u + 1}
    (algebraMap (Padic.coefficientExtensionIntegers l E) E)

/-- Additivity of localization to the coefficient field.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointModuleRationalizationAdditive :
    (pointModuleRationalization l E).Additive :=
  (pointCoefficientTensors_exact l E E (AlgHom.id ℚ_[l] E)).2.1

/-- Localization preserves kernels.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointModuleRationalizationLimits :
    PreservesFiniteLimits (pointModuleRationalization l E) :=
  (pointCoefficientTensors_exact l E E (AlgHom.id ℚ_[l] E)).2.2.1

/-- Localization preserves cokernels.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointModuleRationalizationColimits :
    PreservesFiniteColimits (pointModuleRationalization l E) :=
  (pointCoefficientTensors_exact l E E (AlgHom.id ℚ_[l] E)).2.2.2

/-- Ordinary termwise tensor with the fraction field on derived modules.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointModuleDerivedRationalization :=
  (pointModuleRationalization l E).mapDerivedCategory

set_option linter.unusedSectionVars false in
/-- Tensor with a coefficient field extension is exact and additive.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: a field extension is a free module, so tensor is a direct sum of copies on
underlying vector spaces and preserves kernels and cokernels. It adds maps termwise. -/
theorem pointCoefficientFieldTensor_exact :
    (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom).Additive ∧
      PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom) ∧
      PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom) := by
  apply pointFlatTensor_exact
  let := ι.toRingHom.toAlgebra
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- Additivity of coefficient field extension.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCoefficientFieldTensorAdditive :
    (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom).Additive :=
  (pointCoefficientFieldTensor_exact l E L ι).1

/-- Coefficient field extension preserves kernels.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCoefficientFieldTensorLimits :
    PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom) :=
  (pointCoefficientFieldTensor_exact l E L ι).2.1

/-- Coefficient field extension preserves cokernels.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointCoefficientFieldTensorColimits :
    PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom) :=
  (pointCoefficientFieldTensor_exact l E L ι).2.2

/-- Termwise coefficient field extension on derived vector spaces.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable abbrev pointCoefficientFieldDerivedTensor :=
  (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom).mapDerivedCategory

/-- The ordinary field-complex multiplication isomorphism.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointCoefficientFieldDerivedUnit :
    pointCoefficientFieldDerivedTensor l E E (AlgHom.id ℚ_[l] E) ≅
      𝟭 (DerivedCategory (ModuleCat.{u + 1} E)) :=
  Functor.mapDerivedCategoryNatIso (ModuleCat.extendScalarsId.{u, u + 1} E) ≪≫
    Functor.mapDerivedCategoryIdIso _

/-- The ordinary field-complex associator.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointCoefficientFieldDerivedAssoc :
    pointCoefficientFieldDerivedTensor l E L ι ⋙ pointCoefficientFieldDerivedTensor l L M κ ≅
      pointCoefficientFieldDerivedTensor l E M (κ.comp ι) :=
  (Functor.mapDerivedCategoryCompIso
    (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom) (ModuleCat.extendScalars.{u, u, u + 1}
        κ.toRingHom)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom
        κ.toRingHom).symm

/-- Rationalization and finite extension commute by the actual balanced localization map.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension).
Proof: send b tensor (a tensor n) to ba tensor (1 tensor n), where a is included
in L. The inverse sends b tensor (x tensor n) to b*iota(x) tensor (1 tensor n).
All nonzero O_E-elements are units in L, so denominators move across the tensor
relation. These maps respect the balanced relations and are mutual inverses;
their formulas commute with module morphisms and determine the map uniquely. -/
theorem pointTensorRationalization_existsUnique :
    ∃! β : pointIntegralModuleTensor l E L ι ⋙ pointModuleRationalization l L ≅
        pointModuleRationalization l E ⋙ ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom,
      ∀ (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
        (a : Padic.coefficientExtensionIntegers l L) (b : L) (n : N),
        β.hom.app N
          (b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
            algebraMap (Padic.coefficientExtensionIntegers l L) L]
            (a ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              integralScalarIntegerInclusion.{u} l E L ι] n)) =
          (b * (a : L)) ⊗ₜ[E, ι.toRingHom]
            ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
              algebraMap (Padic.coefficientExtensionIntegers l E) E] n) := by
  let f := integralScalarIntegerInclusion l E L ι
  let g := algebraMap (Padic.coefficientExtensionIntegers l L) L
  let e := algebraMap (Padic.coefficientExtensionIntegers l E) E
  let β : pointIntegralModuleTensor l E L ι ⋙ pointModuleRationalization l L ≅
      pointModuleRationalization l E ⋙ ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom :=
    (ModuleCat.extendScalarsComp.{u, u + 1} f g).symm ≪≫
      ModuleCat.extendScalarsComp.{u, u + 1} e ι.toRingHom
  have hβ (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))
      (a : Padic.coefficientExtensionIntegers l L) (b : L) (n : N) :
      β.hom.app N
        (b ⊗ₜ[Padic.coefficientExtensionIntegers l L, g]
          (a ⊗ₜ[Padic.coefficientExtensionIntegers l E, f] n)) =
        (b * (a : L)) ⊗ₜ[E, ι.toRingHom]
          ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E, e] n) := by
    change (ModuleCat.extendScalarsComp.{u, u + 1} e ι.toRingHom).hom.app N
      ((ModuleCat.extendScalarsComp.{u, u + 1} f g).inv.app N
        (b ⊗ₜ[Padic.coefficientExtensionIntegers l L, g]
          (a ⊗ₜ[Padic.coefficientExtensionIntegers l E, f] n))) = _
    rw [pointModuleAssoc_apply, pointModuleComp_apply]
    rfl
  refine ⟨β, hβ, ?_⟩
  intro γ hγ
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | tmul a n => exact (hγ N a 1 n).trans (hβ N a 1 n).symm
  | add x y hx hy => simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hx hy


/-- The canonical localization-tensor associator on module derived categories.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointDerivedTensorRationalization :
    pointIntegralModuleDerivedTensor l E L ι ⋙ pointModuleDerivedRationalization l L ≅
      pointModuleDerivedRationalization l E ⋙ pointCoefficientFieldDerivedTensor l E L ι :=
  (Functor.mapDerivedCategoryCompIso
    (pointIntegralModuleTensor l E L ι) (pointModuleRationalization l L)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (pointTensorRationalization_existsUnique l E L ι).exists.choose ≪≫
      Functor.mapDerivedCategoryCompIso
        (pointModuleRationalization l E) (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom)

section Constructible

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- The algebraic closure in the fixed finite-field datum is algebraically closed.
Source: blueprint finite-field conventions
(blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable instance pointDatumIsAlgClosed : IsAlgClosed D.k :=
  IsAlgClosure.isAlgClosed D.k₀

/-- The two recorded constructibility interfaces describe the same point objects.
Source: blueprint order 1459 and the point's fixed finite-field datum
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: both predicates require derived completeness of the same completed coefficient
module complex. Identify their quotient reductions by the normalized change-of-rings
counit on K-flat representatives. These identifications preserve constructibility
and cohomological support. The support inclusion in Icc is exactly the pair of bounds
in the finite-field interface, with the same interval for every positive exponent. -/
theorem pointIntegralConstructible_iff
    (K : completedIntegralDerivedCategory l E (Spec (.of D.k)) D hl) :
    boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) K ↔
      sfIntegralConstructible l E (Spec (.of D.k)) K := by
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    constructor
    · rintro ⟨hK, a, b, hab, h⟩
      refine ⟨(sfDerivedComplete_iff_legacy l E _ D hl K).mpr hK, a, b, hab, ?_⟩
      intro n
      exact ⟨(h n).1, fun i hi ↦ (h n).2 i hi⟩
    · rintro ⟨hK, a, b, hab, h⟩
      refine ⟨(sfDerivedComplete_iff_legacy l E _ D hl K).mp hK, a, b, hab, ?_⟩
      intro n
      exact ⟨(h n).1, fun i hi ↦ (h n).2 hi⟩

/-- The canonical completion comparison is invertible on the constructible integral category.
Source: Bhatt--Scholze 3.4.12 and blueprint final paragraph
(blueprint: lem-weil-point-sections-scalar-extension).
Proof: the defining constructible predicate includes derived completeness. Its
augmented reduction tower is the same strict tower as the unrestricted predicate:
both units send x to 1 tensor x, and their product and cone maps agree. Apply
lem-weil-finite-free-completed-scalar-comparison to this complete object. -/
theorem pointConstructibleCompletionComparison_isIso
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (_hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    IsIso ((completedScalarComparison.{u, u} l E L ι
            (Spec (.of D.k))).app K) := by
  suffices h : IsDerivedCompleteUnrestricted l E (Spec (.of D.k)) K from
    ((finiteFreeCompletedScalarComparison.{u, u} l E L ι (Spec (.of D.k))).2.1 K h).1
  rcases Nat.exists_infinite_primes (l + 1) with ⟨p, hp, hpprime⟩
  have hlp : l ≠ p := by omega
  have : Fact p.Prime := ⟨hpprime⟩
  let D₀ : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hpprime
      exponent_pos := le_rfl
      cardinality_eq := (pow_one p).symm
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  refine ⟨D₀, hlp, ?_⟩
  exact (sfDerivedComplete_iff_legacy l E _ D₀ hlp K).mp
    ((pointIntegralConstructible_iff l E D hl K).mp _hK).1

/-- The actual completion comparison as an isomorphism on an integral constructible object.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointConstructibleCompletionIso
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    (completedDerivedScalarExtension.{u, u} l E L ι
            (Spec (.of D.k))).obj K ≅
      (integralScalarExtension.{u} l E L ι
            (Spec (.of D.k))).obj K :=
  letI := pointConstructibleCompletionComparison_isIso l E L ι D hl K hK
  asIso ((completedScalarComparison.{u, u} l E L ι
            (Spec (.of D.k))).app K)

/-- Phi is precisely the inverse of sections of chi after the canonical sections-tensor map.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointSectionsScalarExtensionIso
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    (pointCompletedDerivedSections D.k l L).obj
        ((integralScalarExtension.{u} l E L ι
            (Spec (.of D.k))).obj K) ≅
      (pointIntegralModuleDerivedTensor l E L ι).obj
        ((pointCompletedDerivedSections D.k l E).obj K) :=
  ((pointDerivedSectionsTensor D.k l E L ι).app K ≪≫
    (pointCompletedDerivedSections D.k l L).mapIso
      (pointConstructibleCompletionIso l E L ι D hl K hK)).symm

/-- The integral identity identification is completeness inverted followed by multiplication.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointIntegralScalarUnit
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    (integralScalarExtension.{u} l E E (AlgHom.id ℚ_[l] E)
            (Spec (.of D.k))).obj K ≅ K :=
  (pointConstructibleCompletionIso l E E (AlgHom.id ℚ_[l] E) D hl K hK).symm ≪≫
    (pointDerivedTensorUnit D.k l E).app K

/-- The integral associator is the specified conjugate of the ordinary derived associator.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointIntegralScalarAssoc
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    (integralScalarExtension.{u} l L M κ
            (Spec (.of D.k))).obj
        ((integralScalarExtension.{u} l E L ι
            (Spec (.of D.k))).obj K) ≅
      (integralScalarExtension.{u} l E M (κ.comp ι)
            (Spec (.of D.k))).obj K :=
  (pointConstructibleCompletionIso l L M κ D hl _
    (integralScalarExtension_constructible D l hl E L ι
      (Spec (.of D.k)) ⟨K, hK⟩)).symm ≪≫
    (completedDerivedScalarExtension.{u, u} l L M κ
            (Spec (.of D.k))).mapIso
      (pointConstructibleCompletionIso l E L ι D hl K hK).symm ≪≫
    (pointDerivedTensorAssoc D.k l E L ι M κ).app K ≪≫
    pointConstructibleCompletionIso l E M (κ.comp ι) D hl K hK

/-- Rational phi is integral phi tensored with L, followed by the balanced localization map.
Source: blueprint final paragraph (blueprint: lem-weil-point-sections-scalar-extension). -/
noncomputable def pointRationalSectionsScalarExtensionIso
    (K : completedIntegralDerivedCategory l E
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E
            (Spec (.of D.k)) K) :
    (pointModuleDerivedRationalization l L).obj
        ((pointCompletedDerivedSections D.k l L).obj
          ((integralScalarExtension.{u} l E L ι
            (Spec (.of D.k))).obj K)) ≅
      (pointCoefficientFieldDerivedTensor l E L ι).obj
        ((pointModuleDerivedRationalization l E).obj
          ((pointCompletedDerivedSections D.k l E).obj K)) :=
  (pointModuleDerivedRationalization l L).mapIso
    (pointSectionsScalarExtensionIso l E L ι D hl K hK) ≪≫
      (pointDerivedTensorRationalization l E L ι).app
        ((pointCompletedDerivedSections D.k l E).obj K)

end Constructible

end WeilConjectures

namespace WeilConjectures
section GenericDerived
variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {A : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} A]
  [Abelian C] [Abelian D] [Abelian E] [Abelian A]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory A]
private theorem pointDerivedComp_fac (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      (F ⋙ G).mapDerivedCategoryFactors.hom.app P := by
  have h := Functor.mapDerivedCategoryCompIso_fac F G P
  change (Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (𝟙 _) = _ at h
  rw [DerivedCategory.Q.map_id] at h
  erw [Category.comp_id] at h
  exact h
private theorem pointDerivedComp_inv_fac (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryCompIso F G).inv.app (DerivedCategory.Q.obj P) ≫
      (F ⋙ G).mapDerivedCategoryFactors.hom.app P =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  rw [← pointDerivedComp_fac F G P, Iso.inv_hom_id_app_assoc]
private noncomputable def pointDerivedSquare
    (F : C ⥤ D) (T : D ⥤ E) (S : C ⥤ A) (G : A ⥤ E)
    [F.Additive] [T.Additive] [S.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (θ : F ⋙ T ≅ S ⋙ G) :
    F.mapDerivedCategory ⋙ T.mapDerivedCategory ≅
      S.mapDerivedCategory ⋙ G.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F T).symm ≪≫
    Functor.mapDerivedCategoryNatIso θ ≪≫ Functor.mapDerivedCategoryCompIso S G
private theorem pointDerivedSquare_symm
    (F : C ⥤ D) (T : D ⥤ E) (S : C ⥤ A) (G : A ⥤ E)
    [F.Additive] [T.Additive] [S.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (θ : F ⋙ T ≅ S ⋙ G) :
    pointDerivedSquare S G F T θ.symm = (pointDerivedSquare F T S G θ).symm := by
  apply Iso.ext
  simp only [pointDerivedSquare, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
@[reassoc] private theorem pointDerivedSquare_fac
    (F : C ⥤ D) (T : D ⥤ E) (S : C ⥤ A) (G : A ⥤ E)
    [F.Additive] [T.Additive] [S.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (θ : F ⋙ T ≅ S ⋙ G) (P : CochainComplex C ℤ) :
    (pointDerivedSquare F T S G θ).hom.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (S.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((S.mapHomologicalComplex (.up ℤ)).obj P) =
      T.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      T.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app P) := by
  dsimp only [pointDerivedSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, Category.assoc, pointDerivedComp_fac S G P,
    Functor.mapDerivedCategoryNatIso_fac, ← Category.assoc, pointDerivedComp_inv_fac F T P,
    Category.assoc]
private theorem pointDerivedId_fac (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj P) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app P := by
  have h := congr_app (congrArg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh C))
    ((HomotopyCategory.quotient C (.up ℤ)).obj P)
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_hom_app] at h
  rw [Functor.mapDerivedCategoryFactorsh_hom_app] at h
  have hi := Functor.mapHomotopyCategoryIdIso_hom_app_eq_id C (.up ℤ)
    ((HomotopyCategory.quotient C (.up ℤ)).obj P)
  rw [hi] at h
  change (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj P) ≫ 𝟙 _ =
    ((𝟭 C).mapDerivedCategory.map (𝟙 _) ≫
      (𝟭 C).mapDerivedCategoryFactors.hom.app P ≫ 𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _)) ≫
      DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ at h
  rw [DerivedCategory.Qh.map_id, (𝟭 C).mapDerivedCategory.map_id] at h
  erw [Category.comp_id, Category.comp_id, Category.comp_id, Category.id_comp] at h
  erw [Category.comp_id] at h
  exact h
private noncomputable def pointDerivedUnit (S : C ⥤ C) [S.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S] (μ : S ≅ 𝟭 C) :
    S.mapDerivedCategory ≅ 𝟭 (DerivedCategory C) :=
  Functor.mapDerivedCategoryNatIso μ ≪≫ Functor.mapDerivedCategoryIdIso C
private theorem pointDerivedUnit_fac (S : C ⥤ C) [S.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S] (μ : S ≅ 𝟭 C)
    (P : CochainComplex C ℤ) :
    (pointDerivedUnit S μ).hom.app (DerivedCategory.Q.obj P) =
      S.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex μ.hom (.up ℤ)).app P) := by
  dsimp only [pointDerivedUnit, Iso.trans_hom, NatTrans.comp_app]
  rw [pointDerivedId_fac, Functor.mapDerivedCategoryNatIso_fac]
private theorem pointDerivedSquare_unit
    (F : C ⥤ D) (T : D ⥤ D) (S : C ⥤ C)
    [F.Additive] [T.Additive] [S.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (θ : F ⋙ T ≅ S ⋙ F) (μS : S ≅ 𝟭 C) (μT : T ≅ 𝟭 D)
    (h : ∀ N, θ.hom.app N ≫ F.map (μS.hom.app N) = μT.hom.app (F.obj N))
    (K : DerivedCategory C) :
    (pointDerivedSquare F T S F θ).hom.app K ≫
      F.mapDerivedCategory.map ((pointDerivedUnit S μS).hom.app K) =
      (pointDerivedUnit T μT).hom.app (F.mapDerivedCategory.obj K) := by
  have hn : (pointDerivedSquare F T S F θ).hom ≫
      Functor.whiskerRight (pointDerivedUnit S μS).hom F.mapDerivedCategory =
      Functor.whiskerLeft F.mapDerivedCategory (pointDerivedUnit T μT).hom := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
    intro P
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [← cancel_mono (F.mapDerivedCategoryFactors.hom.app P)]
    have hp : (NatTrans.mapHomologicalComplex θ.hom (.up ℤ)).app P ≫
        (F.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex μS.hom (.up ℤ)).app P) =
        (NatTrans.mapHomologicalComplex μT.hom (.up ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
      ext i
      exact h (P.X i)
    have hnat := (pointDerivedUnit T μT).hom.naturality
      (F.mapDerivedCategoryFactors.hom.app P)
    dsimp only [Functor.id_map, Functor.comp_obj] at hnat
    rw [← hnat, pointDerivedUnit_fac, pointDerivedUnit_fac, Functor.map_comp]
    have hf := F.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex μS.hom (.up ℤ)).app P)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hf
    simp only [Category.assoc]
    erw [hf]
    rw [pointDerivedSquare_fac_assoc]
    simp only [← DerivedCategory.Q.map_comp]
    rw [hp]
  exact congr_app hn K
private noncomputable def pointDerivedAssoc (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (α : F ⋙ G ≅ H) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F G).symm ≪≫ Functor.mapDerivedCategoryNatIso α
@[reassoc] private theorem pointDerivedAssoc_fac
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (α : F ⋙ G ≅ H)
    (P : CochainComplex C ℤ) :
    (pointDerivedAssoc F G H α).hom.app (DerivedCategory.Q.obj P) ≫
      H.mapDerivedCategoryFactors.hom.app P =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app P) := by
  dsimp only [pointDerivedAssoc, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fac,
    ← Category.assoc, pointDerivedComp_inv_fac, Category.assoc]
section Tower
universe x y z
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type x}
  [Category.{y} C₀] [Category.{y} C₁] [Category.{y} C₂]
  [Category.{y} D₀] [Category.{y} D₁] [Category.{y} D₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian D₀] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory.{z} C₀] [HasDerivedCategory.{z} C₁] [HasDerivedCategory.{z} C₂]
  [HasDerivedCategory.{z} D₀] [HasDerivedCategory.{z} D₁] [HasDerivedCategory.{z} D₂]
private theorem pointDerivedSquare_assoc
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
    (S₀₁ : C₀ ⥤ C₁) (S₁₂ : C₁ ⥤ C₂) (S₀₂ : C₀ ⥤ C₂)
    (T₀₁ : D₀ ⥤ D₁) (T₁₂ : D₁ ⥤ D₂) (T₀₂ : D₀ ⥤ D₂)
    [F₀.Additive] [F₁.Additive] [F₂.Additive]
    [S₀₁.Additive] [S₁₂.Additive] [S₀₂.Additive]
    [T₀₁.Additive] [T₁₂.Additive] [T₀₂.Additive]
    [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits S₀₁] [PreservesFiniteColimits S₀₁]
    [PreservesFiniteLimits S₁₂] [PreservesFiniteColimits S₁₂]
    [PreservesFiniteLimits S₀₂] [PreservesFiniteColimits S₀₂]
    [PreservesFiniteLimits T₀₁] [PreservesFiniteColimits T₀₁]
    [PreservesFiniteLimits T₁₂] [PreservesFiniteColimits T₁₂]
    [PreservesFiniteLimits T₀₂] [PreservesFiniteColimits T₀₂]
    (θ₀₁ : F₀ ⋙ T₀₁ ≅ S₀₁ ⋙ F₁) (θ₁₂ : F₁ ⋙ T₁₂ ≅ S₁₂ ⋙ F₂)
    (θ₀₂ : F₀ ⋙ T₀₂ ≅ S₀₂ ⋙ F₂) (αS : S₀₁ ⋙ S₁₂ ≅ S₀₂) (αT : T₀₁ ⋙ T₁₂ ≅ T₀₂)
    (h : ∀ N, T₁₂.map (θ₀₁.hom.app N) ≫ θ₁₂.hom.app (S₀₁.obj N) ≫
      F₂.map (αS.hom.app N) = αT.hom.app (F₀.obj N) ≫ θ₀₂.hom.app N)
    (K : DerivedCategory C₀) :
    T₁₂.mapDerivedCategory.map ((pointDerivedSquare F₀ T₀₁ S₀₁ F₁ θ₀₁).hom.app K) ≫
      (pointDerivedSquare F₁ T₁₂ S₁₂ F₂ θ₁₂).hom.app (S₀₁.mapDerivedCategory.obj K) ≫
      F₂.mapDerivedCategory.map ((pointDerivedAssoc S₀₁ S₁₂ S₀₂ αS).hom.app K) =
      (pointDerivedAssoc T₀₁ T₁₂ T₀₂ αT).hom.app (F₀.mapDerivedCategory.obj K) ≫
        (pointDerivedSquare F₀ T₀₂ S₀₂ F₂ θ₀₂).hom.app K := by
  let q₀₁ := pointDerivedSquare F₀ T₀₁ S₀₁ F₁ θ₀₁
  let q₁₂ := pointDerivedSquare F₁ T₁₂ S₁₂ F₂ θ₁₂
  let q₀₂ := pointDerivedSquare F₀ T₀₂ S₀₂ F₂ θ₀₂
  let aS := pointDerivedAssoc S₀₁ S₁₂ S₀₂ αS
  let aT := pointDerivedAssoc T₀₁ T₁₂ T₀₂ αT
  have hn : Functor.whiskerRight q₀₁.hom T₁₂.mapDerivedCategory ≫
      Functor.whiskerLeft S₀₁.mapDerivedCategory q₁₂.hom ≫
      Functor.whiskerRight aS.hom F₂.mapDerivedCategory =
      Functor.whiskerLeft F₀.mapDerivedCategory aT.hom ≫ q₀₂.hom := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C₀ (.up ℤ))
    intro P
    dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
    rw [← cancel_mono (F₂.mapDerivedCategory.map (S₀₂.mapDerivedCategoryFactors.hom.app P) ≫
      F₂.mapDerivedCategoryFactors.hom.app ((S₀₂.mapHomologicalComplex (.up ℤ)).obj P))]
    have hp :
        (T₁₂.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex θ₀₁.hom (.up ℤ)).app P) ≫
        (NatTrans.mapHomologicalComplex θ₁₂.hom (.up ℤ)).app
          ((S₀₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (F₂.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex αS.hom (.up ℤ)).app P) =
        (NatTrans.mapHomologicalComplex αT.hom (.up ℤ)).app
          ((F₀.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (NatTrans.mapHomologicalComplex θ₀₂.hom (.up ℤ)).app P := by
      ext i
      exact h (P.X i)
    have hs := pointDerivedAssoc_fac S₀₁ S₁₂ S₀₂ αS P
    have ht := pointDerivedAssoc_fac T₀₁ T₁₂ T₀₂ αT
      ((F₀.mapHomologicalComplex (.up ℤ)).obj P)
    have hqn := q₁₂.hom.naturality (S₀₁.mapDerivedCategoryFactors.hom.app P)
    have han := aT.hom.naturality (F₀.mapDerivedCategoryFactors.hom.app P)
    have hfn := F₂.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex αS.hom (.up ℤ)).app P)
    have htn := T₁₂.mapDerivedCategoryFactors.hom.naturality
      ((NatTrans.mapHomologicalComplex θ₀₁.hom (.up ℤ)).app P)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hqn han hfn htn
    simp only [Category.assoc]
    rw [← F₂.mapDerivedCategory.map_comp_assoc, hs, Functor.map_comp, Functor.map_comp]
    simp only [Category.assoc]
    erw [hfn]
    rw [← reassoc_of% hqn]
    erw [pointDerivedSquare_fac_assoc F₁ T₁₂ S₁₂ F₂ θ₁₂
      ((S₀₁.mapHomologicalComplex (.up ℤ)).obj P)]
    simp only [← T₁₂.mapDerivedCategory.map_comp_assoc]
    erw [pointDerivedSquare_fac F₀ T₀₁ S₀₁ F₁ θ₀₁ P]
    simp only [T₁₂.mapDerivedCategory.map_comp, Category.assoc]
    erw [reassoc_of% htn]
    erw [pointDerivedSquare_fac F₀ T₀₂ S₀₂ F₂ θ₀₂ P]
    rw [← reassoc_of% han, reassoc_of% ht]
    simp only [← DerivedCategory.Q.map_comp]
    rw [hp]
    rfl
  exact congr_app hn K
private theorem pointSquareUnit_transport
    {V W : Type*} [Category V] [Category W]
    (F : V ⥤ W) (S S' : V ⥤ V) (T : W ⥤ W)
    (δ : S ≅ S') (θ : F ⋙ T ≅ S' ⋙ F) (μS : S' ≅ 𝟭 V) (μT : T ≅ 𝟭 W)
    (h : ∀ N, θ.hom.app N ≫ F.map (μS.hom.app N) = μT.hom.app (F.obj N))
    (N : V) :
    (θ ≪≫ Functor.isoWhiskerRight δ.symm F).hom.app N ≫
      F.map ((δ ≪≫ μS).hom.app N) = μT.hom.app (F.obj N) := by
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  simp only [Functor.map_comp, Category.assoc, ← F.map_comp_assoc,
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  exact h N
omit [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian D₀] [Abelian D₁] [Abelian D₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory D₀] [HasDerivedCategory D₁] [HasDerivedCategory D₂] in
private theorem pointSquareAssoc_transport
    (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
    (S₀₁ S'₀₁ : C₀ ⥤ C₁) (S₁₂ S'₁₂ : C₁ ⥤ C₂) (S₀₂ S'₀₂ : C₀ ⥤ C₂)
    (T₀₁ : D₀ ⥤ D₁) (T₁₂ : D₁ ⥤ D₂) (T₀₂ : D₀ ⥤ D₂)
    (δ₀₁ : S₀₁ ≅ S'₀₁) (δ₁₂ : S₁₂ ≅ S'₁₂) (δ₀₂ : S₀₂ ≅ S'₀₂)
    (θ₀₁ : F₀ ⋙ T₀₁ ≅ S'₀₁ ⋙ F₁) (θ₁₂ : F₁ ⋙ T₁₂ ≅ S'₁₂ ⋙ F₂)
    (θ₀₂ : F₀ ⋙ T₀₂ ≅ S'₀₂ ⋙ F₂) (αS : S'₀₁ ⋙ S'₁₂ ≅ S'₀₂)
    (αT : T₀₁ ⋙ T₁₂ ≅ T₀₂)
    (h : ∀ N, T₁₂.map (θ₀₁.hom.app N) ≫ θ₁₂.hom.app (S'₀₁.obj N) ≫
      F₂.map (αS.hom.app N) = αT.hom.app (F₀.obj N) ≫ θ₀₂.hom.app N)
    (N : C₀) :
    T₁₂.map ((θ₀₁ ≪≫ Functor.isoWhiskerRight δ₀₁.symm F₁).hom.app N) ≫
      (θ₁₂ ≪≫ Functor.isoWhiskerRight δ₁₂.symm F₂).hom.app (S₀₁.obj N) ≫
      F₂.map ((Functor.isoWhiskerRight δ₀₁ S₁₂ ≪≫
        Functor.isoWhiskerLeft S'₀₁ δ₁₂ ≪≫ αS ≪≫ δ₀₂.symm).hom.app N) =
      αT.hom.app (F₀.obj N) ≫
        (θ₀₂ ≪≫ Functor.isoWhiskerRight δ₀₂.symm F₂).hom.app N := by
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Functor.map_comp, Category.assoc]
  have ht := θ₁₂.hom.naturality (δ₀₁.inv.app N)
  have hd := congrArg F₂.map (δ₁₂.inv.naturality (δ₀₁.hom.app N))
  dsimp only [Functor.comp_map, Functor.comp_obj] at ht
  simp only [Functor.map_comp] at hd
  rw [reassoc_of% ht, ← reassoc_of% hd]
  simp only [← F₂.map_comp_assoc, ← S'₁₂.map_comp_assoc,
    Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% (h N)]
end Tower


end GenericDerived
private theorem pointInverseCompositeSquare {V : Type*} [Category V]
    {A B C D E : V} (a : A ≅ B) (b : B ≅ C) (c : C ≅ D) (d : A ≅ E) (e : E ≅ D)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom) :
    c.hom ≫ e.inv = b.inv ≫ a.inv ≫ d.hom := by
  apply (cancel_epi (a.hom ≫ b.hom)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% h, Iso.hom_inv_id, Category.comp_id]

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
private theorem pointRationalization_unit_forward
    (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) :
    (pointTensorRationalization_existsUnique l E E (AlgHom.id ℚ_[l] E)).exists.choose.hom.app N ≫
      (ModuleCat.extendScalarsId.{u, u + 1} E).hom.app
        ((pointModuleRationalization l E).obj N) =
      (pointModuleRationalization l E).map
        ((pointIntegralModuleUnit_existsUnique l E).exists.choose.hom.app N) := by
  apply ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
    (algebraMap (Padic.coefficientExtensionIntegers l E) E)).homEquiv _ _).injective
  apply ModuleCat.ExtendScalars.hom_ext
  intro n
  change (ModuleCat.extendScalarsId.{u, u + 1} E).hom.app _
    (((pointTensorRationalization_existsUnique l E E (AlgHom.id ℚ_[l] E)).exists.choose.hom.app N)
      ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
        algebraMap (Padic.coefficientExtensionIntegers l E) E]
        ((1 : Padic.coefficientExtensionIntegers l E) ⊗ₜ[
          Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion l E E (AlgHom.id ℚ_[l] E)] n))) =
    ((pointModuleRationalization l E).map
      ((pointIntegralModuleUnit_existsUnique l E).exists.choose.hom.app N))
      ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
        algebraMap (Padic.coefficientExtensionIntegers l E) E]
        ((1 : Padic.coefficientExtensionIntegers l E) ⊗ₜ[
          Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion l E E (AlgHom.id ℚ_[l] E)] n))
  erw [(pointTensorRationalization_existsUnique l E E
    (AlgHom.id ℚ_[l] E)).exists.choose_spec]
  erw [OneMemClass.coe_one, mul_one, ModuleCat.extendScalarsId_hom_app_one_tmul,
    ModuleCat.ExtendScalars.map_tmul,
    (pointIntegralModuleUnit_existsUnique l E).exists.choose_spec, one_smul]

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
  (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (κ : L →ₐ[ℚ_[l]] M)
private theorem pointRationalization_assoc_forward
    (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) :
    (pointModuleRationalization l M).map
        ((pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose.hom.app N) ≫
      (pointTensorRationalization_existsUnique l E M (κ.comp ι)).exists.choose.hom.app N =
    (pointTensorRationalization_existsUnique l L M κ).exists.choose.hom.app
        ((pointIntegralModuleTensor l E L ι).obj N) ≫
      (ModuleCat.extendScalars.{u, u, u + 1} κ.toRingHom).map
        ((pointTensorRationalization_existsUnique l E L ι).exists.choose.hom.app N) ≫
      (ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom κ.toRingHom).inv.app
        ((pointModuleRationalization l E).obj N) := by
  apply (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
    (algebraMap (Padic.coefficientExtensionIntegers l M) M)).homEquiv _ _ |>.injective
  apply (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
    (integralScalarIntegerInclusion l L M κ)).homEquiv _ _ |>.injective
  apply ModuleCat.ExtendScalars.hom_ext
  intro n
  let t := (1 : M) ⊗ₜ[Padic.coefficientExtensionIntegers l M,
    algebraMap (Padic.coefficientExtensionIntegers l M) M]
    ((1 : Padic.coefficientExtensionIntegers l M) ⊗ₜ[
      Padic.coefficientExtensionIntegers l L, integralScalarIntegerInclusion l L M κ]
      ((1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[
        Padic.coefficientExtensionIntegers l E, integralScalarIntegerInclusion l E L ι] n))
  change ((pointTensorRationalization_existsUnique l E M (κ.comp ι)).exists.choose.hom.app N)
    (((pointModuleRationalization l M).map
      ((pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose.hom.app N)) t) =
    ((ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom κ.toRingHom).inv.app _)
      (((ModuleCat.extendScalars κ.toRingHom).map
        ((pointTensorRationalization_existsUnique l E L ι).exists.choose.hom.app N))
        (((pointTensorRationalization_existsUnique l L M κ).exists.choose.hom.app _) t))
  dsimp only [t]
  erw [ModuleCat.ExtendScalars.map_tmul,
    (pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose_spec]
  simp only [map_one, mul_one]
  erw [(pointTensorRationalization_existsUnique l E M (κ.comp ι)).exists.choose_spec,
    (pointTensorRationalization_existsUnique l L M κ).exists.choose_spec]
  erw [OneMemClass.coe_one, mul_one, ModuleCat.ExtendScalars.map_tmul,
    (pointTensorRationalization_existsUnique l E L ι).exists.choose_spec,
    OneMemClass.coe_one, mul_one]
  erw [← ModuleCat.extendScalarsComp_hom_app_one_tmul.{u, u + 1} ι.toRingHom κ.toRingHom
    ((pointModuleRationalization l E).obj N)
    ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
      algebraMap (Padic.coefficientExtensionIntegers l E) E] n)]
  exact (ConcreteCategory.congr_hom
    ((ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom κ.toRingHom).hom_inv_id_app
      ((pointModuleRationalization l E).obj N))
      ((1 : M) ⊗ₜ[E, (κ.comp ι).toRingHom]
        ((1 : E) ⊗ₜ[Padic.coefficientExtensionIntegers l E,
          algebraMap (Padic.coefficientExtensionIntegers l E) E] n))).symm


private theorem pointRationalization_unit
    (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) :
    (pointTensorRationalization_existsUnique l E E (AlgHom.id ℚ_[l] E)).exists.choose.inv.app N ≫
      (pointModuleRationalization l E).map
        ((pointIntegralModuleUnit_existsUnique l E).exists.choose.hom.app N) =
      (ModuleCat.extendScalarsId.{u, u + 1} E).hom.app
        ((pointModuleRationalization l E).obj N) := by
  apply (cancel_epi
    ((pointTensorRationalization_existsUnique l E E
      (AlgHom.id ℚ_[l] E)).exists.choose.hom.app N)).mp
  simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using
    (pointRationalization_unit_forward l E N).symm
private theorem pointRationalization_derived_unit
    (K : DerivedCategory (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))) :
    (pointDerivedTensorRationalization l E E (AlgHom.id ℚ_[l] E)).hom.app K ≫
      (pointCoefficientFieldDerivedUnit l E).hom.app
        ((pointModuleDerivedRationalization l E).obj K) =
      (pointModuleDerivedRationalization l E).map
        ((pointIntegralModuleDerivedUnit l E).hom.app K) := by
  have h := pointDerivedSquare_unit
    (pointModuleRationalization l E)
    (ModuleCat.extendScalars.{u, u, u + 1} (AlgHom.id ℚ_[l] E).toRingHom)
    (pointIntegralModuleTensor l E E (AlgHom.id ℚ_[l] E))
    ((pointTensorRationalization_existsUnique l E E (AlgHom.id ℚ_[l] E)).exists.choose.symm)
    (pointIntegralModuleUnit_existsUnique l E).exists.choose
    (ModuleCat.extendScalarsId.{u, u + 1} E) (pointRationalization_unit l E) K
  rw [pointDerivedSquare_symm] at h
  dsimp only [pointDerivedSquare, pointDerivedUnit] at h
  change (pointDerivedTensorRationalization l E E (AlgHom.id ℚ_[l] E)).inv.app K ≫
      (pointModuleDerivedRationalization l E).map
        ((pointIntegralModuleDerivedUnit l E).hom.app K) =
      (pointCoefficientFieldDerivedUnit l E).hom.app
        ((pointModuleDerivedRationalization l E).obj K) at h
  apply (cancel_epi
    ((pointDerivedTensorRationalization l E E (AlgHom.id ℚ_[l] E)).inv.app K)).mp
  simpa only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp] using h.symm

private theorem pointRationalization_assoc
    (N : ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E)) :
    (ModuleCat.extendScalars.{u, u, u + 1} κ.toRingHom).map
        ((pointTensorRationalization_existsUnique l E L ι).exists.choose.inv.app N) ≫
      (pointTensorRationalization_existsUnique l L M κ).exists.choose.inv.app
        ((pointIntegralModuleTensor l E L ι).obj N) ≫
      (pointModuleRationalization l M).map
        ((pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose.hom.app N) =
    (ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom κ.toRingHom).inv.app
        ((pointModuleRationalization l E).obj N) ≫
      (pointTensorRationalization_existsUnique l E M (κ.comp ι)).exists.choose.inv.app N := by
  have h := pointInverseCompositeSquare
    ((pointTensorRationalization_existsUnique l L M κ).exists.choose.app
      ((pointIntegralModuleTensor l E L ι).obj N))
    ((ModuleCat.extendScalars.{u, u, u + 1} κ.toRingHom).mapIso
      ((pointTensorRationalization_existsUnique l E L ι).exists.choose.app N))
    ((ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom κ.toRingHom).symm.app
      ((pointModuleRationalization l E).obj N))
    ((pointModuleRationalization l M).mapIso
      ((pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose.app N))
    ((pointTensorRationalization_existsUnique l E M (κ.comp ι)).exists.choose.app N)
    (pointRationalization_assoc_forward l E L ι M κ N).symm
  simpa only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Iso.symm_hom] using h.symm
private theorem pointRationalization_derived_assoc
    (K : DerivedCategory (ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l E))) :
    (pointModuleDerivedRationalization l M).map
        ((pointIntegralModuleDerivedAssoc l E L ι M κ).hom.app K) ≫
      (pointDerivedTensorRationalization l E M (κ.comp ι)).hom.app K =
    (pointDerivedTensorRationalization l L M κ).hom.app
        ((pointIntegralModuleDerivedTensor l E L ι).obj K) ≫
      (pointCoefficientFieldDerivedTensor l L M κ).map
        ((pointDerivedTensorRationalization l E L ι).hom.app K) ≫
      (pointCoefficientFieldDerivedAssoc l E L ι M κ).hom.app
        ((pointModuleDerivedRationalization l E).obj K) := by
  have h := pointDerivedSquare_assoc
    (pointModuleRationalization l E) (pointModuleRationalization l L)
    (pointModuleRationalization l M)
    (pointIntegralModuleTensor l E L ι) (pointIntegralModuleTensor l L M κ)
    (pointIntegralModuleTensor l E M (κ.comp ι))
    (ModuleCat.extendScalars.{u, u, u + 1} ι.toRingHom)
    (ModuleCat.extendScalars.{u, u, u + 1} κ.toRingHom)
    (ModuleCat.extendScalars.{u, u, u + 1} (κ.comp ι).toRingHom)
    (pointTensorRationalization_existsUnique l E L ι).exists.choose.symm
    (pointTensorRationalization_existsUnique l L M κ).exists.choose.symm
    (pointTensorRationalization_existsUnique l E M (κ.comp ι)).exists.choose.symm
    (pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose
    (ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom κ.toRingHom).symm
    (pointRationalization_assoc l E L ι M κ) K
  rw [pointDerivedSquare_symm, pointDerivedSquare_symm, pointDerivedSquare_symm] at h
  change (pointCoefficientFieldDerivedTensor l L M κ).map
      ((pointDerivedTensorRationalization l E L ι).inv.app K) ≫
    (pointDerivedTensorRationalization l L M κ).inv.app
      ((pointIntegralModuleDerivedTensor l E L ι).obj K) ≫
    (pointModuleDerivedRationalization l M).map
      ((pointIntegralModuleDerivedAssoc l E L ι M κ).hom.app K) =
    (pointCoefficientFieldDerivedAssoc l E L ι M κ).hom.app
      ((pointModuleDerivedRationalization l E).obj K) ≫
    (pointDerivedTensorRationalization l E M (κ.comp ι)).inv.app K at h
  have ht := pointInverseCompositeSquare
    ((pointCoefficientFieldDerivedTensor l L M κ).mapIso
      ((pointDerivedTensorRationalization l E L ι).symm.app K))
    ((pointDerivedTensorRationalization l L M κ).symm.app
      ((pointIntegralModuleDerivedTensor l E L ι).obj K))
    ((pointModuleDerivedRationalization l M).mapIso
      ((pointIntegralModuleDerivedAssoc l E L ι M κ).app K))
    ((pointCoefficientFieldDerivedAssoc l E L ι M κ).app
      ((pointModuleDerivedRationalization l E).obj K))
    ((pointDerivedTensorRationalization l E M (κ.comp ι)).symm.app K) h
  simpa only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Iso.symm_hom, Iso.symm_inv] using ht
end WeilConjectures

namespace WeilConjectures

section
variable (k : Type u) [Field k] [IsAlgClosed k] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
private theorem pointOrdinarySections_unit
    (N : integralTowerModules.{u, u} l E (Spec (.of k))) :
    (pointSectionsTensor k l E E (AlgHom.id ℚ_[l] E)).hom.app N ≫
      (pointCompletedSections k l E).map ((pointOrdinaryTensorUnit k l E).hom.app N) =
      (pointIntegralModuleUnit_existsUnique l E).exists.choose.hom.app
        ((pointCompletedSections k l E).obj N) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro n
  change ((pointOrdinaryTensorUnit k l E).hom.app N).val.app
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))
      ((pointSectionsTensor k l E E (AlgHom.id ℚ_[l] E)).hom.app N
        ((1 : Padic.coefficientExtensionIntegers l E) ⊗ₜ[
          Padic.coefficientExtensionIntegers l E,
          integralScalarIntegerInclusion l E E (AlgHom.id ℚ_[l] E)] n)) = _
  erw [(pointSectionsTensor_existsUnique k l E E
    (AlgHom.id ℚ_[l] E)).exists.choose_spec]
  erw [(pointOrdinaryTensorUnit_existsUnique k l E).exists.choose_spec]
  rw [map_one, one_smul]
  erw [(pointIntegralModuleUnit_existsUnique l E).exists.choose_spec, one_smul]
end

section
variable (k : Type u) [Field k] [IsAlgClosed k] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
  (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (κ : L →ₐ[ℚ_[l]] M)
private theorem pointOrdinarySections_assoc
    (N : integralTowerModules.{u, u} l E (Spec (.of k))) :
    (pointIntegralModuleTensor l L M κ).map ((pointSectionsTensor k l E L ι).hom.app N) ≫
      (pointSectionsTensor k l L M κ).hom.app
        ((completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))).obj N) ≫
      (pointCompletedSections k l M).map
        ((pointOrdinaryTensorAssoc k l E L ι M κ).hom.app N) =
      (pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose.hom.app
        ((pointCompletedSections k l E).obj N) ≫
      (pointSectionsTensor k l E M (κ.comp ι)).hom.app N := by
  apply (ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
    (integralScalarIntegerInclusion l L M κ)).homEquiv _ _ |>.injective
  apply ModuleCat.ExtendScalars.hom_ext
  intro n
  change ((pointOrdinaryTensorAssoc k l E L ι M κ).hom.app N).val.app
    (op (Scheme.ProEt.mk (𝟙 (Spec (.of k)))))
      ((pointSectionsTensor k l L M κ).hom.app _
        ((1 : Padic.coefficientExtensionIntegers l M) ⊗ₜ[
          Padic.coefficientExtensionIntegers l L, integralScalarIntegerInclusion l L M κ]
          ((pointSectionsTensor k l E L ι).hom.app N
            ((1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[
              Padic.coefficientExtensionIntegers l E,
              integralScalarIntegerInclusion l E L ι] n)))) =
    (pointSectionsTensor k l E M (κ.comp ι)).hom.app N
      ((pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose.hom.app
        ((pointCompletedSections k l E).obj N)
        ((1 : Padic.coefficientExtensionIntegers l M) ⊗ₜ[
          Padic.coefficientExtensionIntegers l L, integralScalarIntegerInclusion l L M κ]
          ((1 : Padic.coefficientExtensionIntegers l L) ⊗ₜ[
            Padic.coefficientExtensionIntegers l E, integralScalarIntegerInclusion l E L ι] n)))
  erw [(pointSectionsTensor_existsUnique k l E L ι).exists.choose_spec,
    (pointSectionsTensor_existsUnique k l L M κ).exists.choose_spec,
    (pointOrdinaryTensorAssoc_existsUnique k l E L ι M κ).exists.choose_spec,
    (pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose_spec,
    (pointSectionsTensor_existsUnique k l E M (κ.comp ι)).exists.choose_spec]
  simp only [map_one, mul_one]
end

variable (k : Type u) [Field k] [IsAlgClosed k] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
private theorem pointCompletedSections_derived_unit
    (K : DerivedCategory (integralTowerModules.{u, u} l E (AlgebraicGeometry.Spec (.of k)))) :
    (pointDerivedSectionsTensor k l E E (AlgHom.id ℚ_[l] E)).hom.app K ≫
      (pointCompletedDerivedSections k l E).map ((pointDerivedTensorUnit k l E).hom.app K) =
      (pointIntegralModuleDerivedUnit l E).hom.app
        ((pointCompletedDerivedSections k l E).obj K) := by
  have h := pointDerivedSquare_unit
    (pointCompletedSections k l E) (pointIntegralModuleTensor l E E (AlgHom.id ℚ_[l] E))
    (completedOrdinaryScalarExtension.{u, u} l E E (AlgHom.id ℚ_[l] E)
      (AlgebraicGeometry.Spec (.of k)))
    (pointSectionsTensor k l E E (AlgHom.id ℚ_[l] E))
    (pointOrdinaryTensorUnit k l E) (pointIntegralModuleUnit_existsUnique l E).exists.choose
    (pointOrdinarySections_unit k l E)
  have ht := pointSquareUnit_transport
    (pointCompletedDerivedSections k l E) _ _ _
    (pointOrdinaryDerivedComparison k l E E (AlgHom.id ℚ_[l] E))
    (pointDerivedSquare (pointCompletedSections k l E)
      (pointIntegralModuleTensor l E E (AlgHom.id ℚ_[l] E))
      (completedOrdinaryScalarExtension.{u, u} l E E (AlgHom.id ℚ_[l] E)
        (AlgebraicGeometry.Spec (.of k))) (pointCompletedSections k l E)
      (pointSectionsTensor k l E E (AlgHom.id ℚ_[l] E)))
    (pointDerivedUnit _ (pointOrdinaryTensorUnit k l E))
    (pointDerivedUnit _ (pointIntegralModuleUnit_existsUnique l E).exists.choose) h K
  simpa only [pointDerivedSectionsTensor, pointDerivedTensorUnit,
    pointIntegralModuleDerivedUnit, pointDerivedSquare, pointDerivedUnit,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.assoc] using ht
variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
  (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (κ : L →ₐ[ℚ_[l]] M)
private theorem pointCompletedSections_derived_assoc
    (K : DerivedCategory (integralTowerModules.{u, u} l E (Spec (.of k)))) :
    (pointIntegralModuleDerivedTensor l L M κ).map
        ((pointDerivedSectionsTensor k l E L ι).hom.app K) ≫
      (pointDerivedSectionsTensor k l L M κ).hom.app
        ((completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of k))).obj K) ≫
      (pointCompletedDerivedSections k l M).map
        ((pointDerivedTensorAssoc k l E L ι M κ).hom.app K) =
      (pointIntegralModuleDerivedAssoc l E L ι M κ).hom.app
        ((pointCompletedDerivedSections k l E).obj K) ≫
      (pointDerivedSectionsTensor k l E M (κ.comp ι)).hom.app K := by
  have h := pointDerivedSquare_assoc
    (pointCompletedSections k l E) (pointCompletedSections k l L)
    (pointCompletedSections k l M)
    (completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k)))
    (completedOrdinaryScalarExtension.{u, u} l L M κ (Spec (.of k)))
    (completedOrdinaryScalarExtension.{u, u} l E M (κ.comp ι) (Spec (.of k)))
    (pointIntegralModuleTensor l E L ι) (pointIntegralModuleTensor l L M κ)
    (pointIntegralModuleTensor l E M (κ.comp ι))
    (pointSectionsTensor k l E L ι) (pointSectionsTensor k l L M κ)
    (pointSectionsTensor k l E M (κ.comp ι))
    (pointOrdinaryTensorAssoc k l E L ι M κ)
    (pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose
    (pointOrdinarySections_assoc k l E L ι M κ)
  let sectionsE := pointCompletedSections k l E
  let sectionsL := pointCompletedSections k l L
  let sectionsM := pointCompletedSections k l M
  let SEL := completedOrdinaryScalarExtension.{u, u} l E L ι (Spec (.of k))
  let SLM := completedOrdinaryScalarExtension.{u, u} l L M κ (Spec (.of k))
  let SEM := completedOrdinaryScalarExtension.{u, u} l E M (κ.comp ι) (Spec (.of k))
  let TEL := pointIntegralModuleTensor l E L ι
  let TLM := pointIntegralModuleTensor l L M κ
  let TEM := pointIntegralModuleTensor l E M (κ.comp ι)
  let θEL := pointSectionsTensor k l E L ι
  let θLM := pointSectionsTensor k l L M κ
  let θEM := pointSectionsTensor k l E M (κ.comp ι)
  let αS := pointOrdinaryTensorAssoc k l E L ι M κ
  let αT := (pointIntegralModuleAssoc_existsUnique l E L ι M κ).exists.choose
  have ht := pointSquareAssoc_transport sectionsE.mapDerivedCategory sectionsL.mapDerivedCategory
    sectionsM.mapDerivedCategory
    (completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of k))) SEL.mapDerivedCategory
    (completedDerivedScalarExtension.{u, u} l L M κ (Spec (.of k))) SLM.mapDerivedCategory
    (completedDerivedScalarExtension.{u, u} l E M (κ.comp ι) (Spec (.of k)))
      SEM.mapDerivedCategory
    TEL.mapDerivedCategory TLM.mapDerivedCategory TEM.mapDerivedCategory
    (pointOrdinaryDerivedComparison k l E L ι) (pointOrdinaryDerivedComparison k l L M κ)
    (pointOrdinaryDerivedComparison k l E M (κ.comp ι))
    (pointDerivedSquare sectionsE TEL SEL sectionsL θEL)
    (pointDerivedSquare sectionsL TLM SLM sectionsM θLM)
    (pointDerivedSquare sectionsE TEM SEM sectionsM θEM)
    (pointDerivedAssoc SEL SLM SEM αS) (pointDerivedAssoc TEL TLM TEM αT) h K
  simpa only [pointDerivedSectionsTensor, pointDerivedTensorAssoc,
    pointIntegralModuleDerivedAssoc, pointDerivedSquare, pointDerivedAssoc,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.assoc] using ht
end WeilConjectures

namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
  (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (κ : L →ₐ[ℚ_[l]] M) (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
private theorem pointIntegralSections_unit
    (K : completedIntegralDerivedCategory l E (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) K) :
    (pointSectionsScalarExtensionIso l E E (AlgHom.id ℚ_[l] E) D hl K hK).hom ≫
      (pointIntegralModuleDerivedUnit l E).hom.app
        ((pointCompletedDerivedSections D.k l E).obj K) =
      (pointCompletedDerivedSections D.k l E).map
        (pointIntegralScalarUnit l E D hl K hK).hom := by
  dsimp only [pointSectionsScalarExtensionIso, pointIntegralScalarUnit,
    Iso.symm_hom, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_inv]
  rw [← pointCompletedSections_derived_unit D.k l E K]
  simp only [Functor.map_comp, Category.assoc, Iso.app_hom, Iso.app_inv,
    Iso.inv_hom_id_app_assoc]
private theorem pointIntegralSections_assoc
    (K : completedIntegralDerivedCategory l E (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) K) :
    (pointCompletedDerivedSections D.k l M).map
        (pointIntegralScalarAssoc l E L ι M κ D hl K hK).hom ≫
      (pointSectionsScalarExtensionIso l E M (κ.comp ι) D hl K hK).hom =
      (pointSectionsScalarExtensionIso l L M κ D hl _
        (integralScalarExtension_constructible D l hl E L ι (Spec (.of D.k)) ⟨K, hK⟩)).hom ≫
      (pointIntegralModuleDerivedTensor l L M κ).map
        (pointSectionsScalarExtensionIso l E L ι D hl K hK).hom ≫
      (pointIntegralModuleDerivedAssoc l E L ι M κ).hom.app
        ((pointCompletedDerivedSections D.k l E).obj K) := by
  have hc := pointInverseCompositeSquare
    ((pointIntegralModuleDerivedTensor l L M κ).mapIso
      ((pointDerivedSectionsTensor D.k l E L ι).app K))
    ((pointDerivedSectionsTensor D.k l L M κ).app
      ((completedDerivedScalarExtension.{u, u} l E L ι (Spec (.of D.k))).obj K))
    ((pointCompletedDerivedSections D.k l M).mapIso
      ((pointDerivedTensorAssoc D.k l E L ι M κ).app K))
    ((pointIntegralModuleDerivedAssoc l E L ι M κ).app
      ((pointCompletedDerivedSections D.k l E).obj K))
    ((pointDerivedSectionsTensor D.k l E M (κ.comp ι)).app K)
    (pointCompletedSections_derived_assoc D.k l E L ι M κ K)
  have hn := (pointDerivedSectionsTensor D.k l L M κ).inv.naturality
    (pointConstructibleCompletionIso l E L ι D hl K hK).inv
  dsimp only [Functor.comp_map] at hn
  dsimp only [Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv] at hc
  dsimp only [pointSectionsScalarExtensionIso, pointIntegralScalarAssoc,
    Iso.symm_hom, Iso.trans_inv, Iso.trans_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.mapIso_inv]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  erw [hc, reassoc_of% hn]
end WeilConjectures

namespace WeilConjectures
private theorem pointInverseIsoNaturality {C : Type*} [Category C]
    {A B X Y : C} (φ : A ≅ X) (ψ : B ≅ Y) (f : A ⟶ B) (g : X ⟶ Y)
    (h : g ≫ ψ.inv = φ.inv ≫ f) : f ≫ ψ.hom = φ.hom ≫ g := by
  have hh := congrArg (fun z ↦ φ.hom ≫ z ≫ ψ.hom) h
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc] using hh.symm
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
private theorem pointIntegralSections_naturality
    (K J : completedIntegralDerivedCategory l E (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) K)
    (hJ : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) J)
    (f : K ⟶ J) :
    (pointCompletedDerivedSections D.k l L).map
      ((integralScalarExtension.{u} l E L ι (Spec (.of D.k))).map f) ≫
        (pointSectionsScalarExtensionIso l E L ι D hl J hJ).hom =
      (pointSectionsScalarExtensionIso l E L ι D hl K hK).hom ≫
        (pointIntegralModuleDerivedTensor l E L ι).map
          ((pointCompletedDerivedSections D.k l E).map f) := by
  apply pointInverseIsoNaturality
    (pointSectionsScalarExtensionIso l E L ι D hl K hK)
    (pointSectionsScalarExtensionIso l E L ι D hl J hJ)
  exact ((pointDerivedSectionsTensor D.k l E L ι).hom ≫
    Functor.whiskerRight (completedScalarComparison.{u, u} l E L ι (Spec (.of D.k)))
      (pointCompletedDerivedSections D.k l L)).naturality f
private theorem pointRationalSections_naturality
    (K J : completedIntegralDerivedCategory l E (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) K)
    (hJ : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) J)
    (f : K ⟶ J) :
    (pointModuleDerivedRationalization l L).map
      ((pointCompletedDerivedSections D.k l L).map
        ((integralScalarExtension.{u} l E L ι (Spec (.of D.k))).map f)) ≫
      (pointRationalSectionsScalarExtensionIso l E L ι D hl J hJ).hom =
    (pointRationalSectionsScalarExtensionIso l E L ι D hl K hK).hom ≫
      (pointCoefficientFieldDerivedTensor l E L ι).map
        ((pointModuleDerivedRationalization l E).map
          ((pointCompletedDerivedSections D.k l E).map f)) := by
  dsimp only [pointRationalSectionsScalarExtensionIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp,
    pointIntegralSections_naturality l E L ι D hl K J hK hJ f,
    Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_map, Iso.app_hom, Functor.comp_obj, Category.assoc] using
    congrArg (fun z ↦ (pointModuleDerivedRationalization l L).map
    (pointSectionsScalarExtensionIso l E L ι D hl K hK).hom ≫ z)
      ((pointDerivedTensorRationalization l E L ι).hom.naturality
        ((pointCompletedDerivedSections D.k l E).map f))
end WeilConjectures

namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
  (M : Type u) [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
  (κ : L →ₐ[ℚ_[l]] M) (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
private theorem pointRationalSections_unit
    (K : completedIntegralDerivedCategory l E (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) K) :
    (pointRationalSectionsScalarExtensionIso l E E (AlgHom.id ℚ_[l] E) D hl K hK).hom ≫
      (pointCoefficientFieldDerivedUnit l E).hom.app
        ((pointModuleDerivedRationalization l E).obj
          ((pointCompletedDerivedSections D.k l E).obj K)) =
    (pointModuleDerivedRationalization l E).map
      ((pointCompletedDerivedSections D.k l E).map
        (pointIntegralScalarUnit l E D hl K hK).hom) := by
  dsimp only [pointRationalSectionsScalarExtensionIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom]
  rw [Category.assoc, pointRationalization_derived_unit, ← Functor.map_comp,
    pointIntegralSections_unit l E D hl K hK]
private theorem pointRationalSections_assoc
    (K : completedIntegralDerivedCategory l E (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl E (Spec (.of D.k)) K) :
    (pointModuleDerivedRationalization l M).map
        ((pointCompletedDerivedSections D.k l M).map
          (pointIntegralScalarAssoc l E L ι M κ D hl K hK).hom) ≫
      (pointRationalSectionsScalarExtensionIso l E M (κ.comp ι) D hl K hK).hom =
    (pointRationalSectionsScalarExtensionIso l L M κ D hl _
      (integralScalarExtension_constructible D l hl E L ι (Spec (.of D.k)) ⟨K, hK⟩)).hom ≫
      (pointCoefficientFieldDerivedTensor l L M κ).map
        (pointRationalSectionsScalarExtensionIso l E L ι D hl K hK).hom ≫
      (pointCoefficientFieldDerivedAssoc l E L ι M κ).hom.app
        ((pointModuleDerivedRationalization l E).obj
          ((pointCompletedDerivedSections D.k l E).obj K)) := by
  dsimp only [pointRationalSectionsScalarExtensionIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom]
  rw [← Category.assoc, ← Functor.map_comp,
    pointIntegralSections_assoc l E L ι M κ D hl K hK]
  simp only [Functor.map_comp, Category.assoc]
  rw [pointRationalization_derived_assoc]
  have hn := (pointDerivedTensorRationalization l L M κ).hom.naturality
    (pointSectionsScalarExtensionIso l E L ι D hl K hK).hom
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [reassoc_of% hn]
end WeilConjectures

namespace WeilConjectures
section Constructible
variable (l : ℕ) [Fact l.Prime] (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)

/-- Sections commute with integral scalar extension, naturally, with identity and tower
coherence; tensoring with L yields the same assertions after rationalization.
The isomorphisms in this statement are the named canonical constructions above.
Source: blueprint `def-weil-finite-coefficient-point`, final paragraph
(blueprint: lem-weil-point-sections-scalar-extension).

Proof:
1. Apply the continuous-coefficient description at Spec k. Evaluation on its one-point
space identifies completed coefficient sections with O_F, compatibly with inclusions
and all quotient projections. A finite free R_E-basis of R_L therefore evaluates to
an O_E-basis of O_L; the completed sheaf is not replaced by the discrete constant one.
2. The balanced map a tensor n to the sheafified tensor of a and n is the identity
on the coordinates of this basis. It is O_L-linear, natural, and commutes with each
differential. Both tensor functors are finite sums and exact. Exact point sections
preserve quasi-isomorphisms, so these comparisons descend to derived categories.
3. Choose a K-flat flat-term representative. The ordinary derived tensor counit and
the strict completion comparison identify its localized comparison with theta followed
by sections of chi. Completeness makes chi invertible; phi is their inverse. For a
roof, use naturality on both chain maps and invert the quasi-isomorphism. This proves
naturality for every derived morphism and independence of representatives.
4. For a tower E to L to M, the ordinary associator sends b tensor (a tensor x)
to b*kappa(a) tensor x, and its inverse sends c tensor x to c tensor (1 tensor x).
Constructibility of the first extension allows the second completion comparison.
Conjugating by the three comparisons gives exactly pointIntegralScalarAssoc.
For the identity extension, the comparison is the completeness unit after multiplication.
5. Both sections-tensor composites send the iterated pure tensor to the section
with coefficient product ab. Insert the four completion comparisons in the conjugate
associator; naturality moves chi past theta and each chi inverse cancels chi. Invert
the resulting equation to obtain the displayed integral composition equation. The unit
calculation sends a tensor n to an and gives the displayed identity equation.
6. Tensor integral phi with L. The balanced localization maps send coefficient
factors to their product. Nonzero O_E-elements are units in L, so the inverse maps
are well defined also on fractions. Localization is exact and field extension is
free, so these are derived isomorphisms. The same coefficient-product calculation,
including denominators, proves rational naturality, identity and composition. -/
theorem pointSectionsScalarExtension
    (Q : Type u) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (F G H : Padic.FiniteCoefficientFields l Q) (hFG : F ≤ G) (hGH : G ≤ H)
    (K : completedIntegralDerivedCategory l F.val
            (Spec (.of D.k)) D hl)
    (hK : boundedConstructibleDerivedCompleteIntegral D l hl F.val
            (Spec (.of D.k)) K) :
    (∀ (J : completedIntegralDerivedCategory l F.val
            (Spec (.of D.k)) D hl)
      (hJ : boundedConstructibleDerivedCompleteIntegral D l hl F.val
            (Spec (.of D.k)) J)
      (f : K ⟶ J),
      (pointCompletedDerivedSections D.k l G.val).map
          ((integralScalarExtension.{u} l F.val G.val (IntermediateField.inclusion hFG)
            (Spec (.of D.k))).map f) ≫
          (pointSectionsScalarExtensionIso l F.val G.val (IntermediateField.inclusion hFG) D hl J
        hJ).hom =
        (pointSectionsScalarExtensionIso l F.val G.val (IntermediateField.inclusion hFG) D hl K
        hK).hom ≫
          (pointIntegralModuleDerivedTensor l F.val G.val (IntermediateField.inclusion hFG)).map
            ((pointCompletedDerivedSections D.k l F.val).map f)) ∧
    ((pointSectionsScalarExtensionIso l F.val F.val (AlgHom.id ℚ_[l] F.val) D hl K hK).hom ≫
        (pointIntegralModuleDerivedUnit l F.val).hom.app
          ((pointCompletedDerivedSections D.k l F.val).obj K) =
      (pointCompletedDerivedSections D.k l F.val).map (pointIntegralScalarUnit l F.val D hl K
        hK).hom) ∧
    ((pointCompletedDerivedSections D.k l H.val).map
        (pointIntegralScalarAssoc l F.val G.val (IntermediateField.inclusion hFG) H.val
        (IntermediateField.inclusion hGH) D hl K hK).hom ≫
        (pointSectionsScalarExtensionIso l F.val H.val ((IntermediateField.inclusion hGH).comp
        (IntermediateField.inclusion hFG)) D hl K hK).hom =
      (pointSectionsScalarExtensionIso l G.val H.val (IntermediateField.inclusion hGH) D hl _
        (integralScalarExtension_constructible D l hl F.val G.val
          (IntermediateField.inclusion hFG) (Spec (.of D.k)) ⟨K, hK⟩)).hom ≫
        (pointIntegralModuleDerivedTensor l G.val H.val (IntermediateField.inclusion hGH)).map
          (pointSectionsScalarExtensionIso l F.val G.val (IntermediateField.inclusion hFG) D hl K
        hK).hom ≫
        (pointIntegralModuleDerivedAssoc l F.val G.val (IntermediateField.inclusion hFG) H.val
        (IntermediateField.inclusion hGH)).hom.app
          ((pointCompletedDerivedSections D.k l F.val).obj K)) ∧
    (∀ (J : completedIntegralDerivedCategory l F.val
            (Spec (.of D.k)) D hl)
      (hJ : boundedConstructibleDerivedCompleteIntegral D l hl F.val
            (Spec (.of D.k)) J)
      (f : K ⟶ J),
      (pointModuleDerivedRationalization l G.val).map
          ((pointCompletedDerivedSections D.k l G.val).map
            ((integralScalarExtension.{u} l F.val G.val (IntermediateField.inclusion hFG)
            (Spec (.of D.k))).map f)) ≫
          (pointRationalSectionsScalarExtensionIso l F.val G.val (IntermediateField.inclusion hFG)
        D hl J hJ).hom =
        (pointRationalSectionsScalarExtensionIso l F.val G.val (IntermediateField.inclusion hFG) D
        hl K hK).hom ≫
          (pointCoefficientFieldDerivedTensor l F.val G.val (IntermediateField.inclusion hFG)).map
            ((pointModuleDerivedRationalization l F.val).map
              ((pointCompletedDerivedSections D.k l F.val).map f))) ∧
    ((pointRationalSectionsScalarExtensionIso l F.val F.val (AlgHom.id ℚ_[l] F.val) D hl K hK).hom ≫
        (pointCoefficientFieldDerivedUnit l F.val).hom.app
          ((pointModuleDerivedRationalization l F.val).obj
            ((pointCompletedDerivedSections D.k l F.val).obj K)) =
      (pointModuleDerivedRationalization l F.val).map
        ((pointCompletedDerivedSections D.k l F.val).map
          (pointIntegralScalarUnit l F.val D hl K hK).hom)) ∧
    ((pointModuleDerivedRationalization l H.val).map
        ((pointCompletedDerivedSections D.k l H.val).map
          (pointIntegralScalarAssoc l F.val G.val (IntermediateField.inclusion hFG) H.val
        (IntermediateField.inclusion hGH) D hl K hK).hom) ≫
        (pointRationalSectionsScalarExtensionIso l F.val H.val ((IntermediateField.inclusion
        hGH).comp (IntermediateField.inclusion hFG)) D hl K hK).hom =
      (pointRationalSectionsScalarExtensionIso l G.val H.val (IntermediateField.inclusion hGH) D
        hl _
        (integralScalarExtension_constructible D l hl F.val G.val
          (IntermediateField.inclusion hFG) (Spec (.of D.k)) ⟨K, hK⟩)).hom ≫
        (pointCoefficientFieldDerivedTensor l G.val H.val (IntermediateField.inclusion hGH)).map
          (pointRationalSectionsScalarExtensionIso l F.val G.val (IntermediateField.inclusion hFG)
        D hl K hK).hom ≫
        (pointCoefficientFieldDerivedAssoc l F.val G.val (IntermediateField.inclusion hFG) H.val
        (IntermediateField.inclusion hGH)).hom.app
          ((pointModuleDerivedRationalization l F.val).obj
            ((pointCompletedDerivedSections D.k l F.val).obj K))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro J hJ f
    exact pointIntegralSections_naturality l F.val G.val (IntermediateField.inclusion hFG)
      D hl K J hK hJ f
  · exact pointIntegralSections_unit l F.val D hl K hK
  · exact pointIntegralSections_assoc l F.val G.val (IntermediateField.inclusion hFG)
      H.val (IntermediateField.inclusion hGH) D hl K hK
  · intro J hJ f
    exact pointRationalSections_naturality l F.val G.val (IntermediateField.inclusion hFG)
      D hl K J hK hJ f
  · exact pointRationalSections_unit l F.val D hl K hK
  · exact pointRationalSections_assoc l F.val G.val (IntermediateField.inclusion hFG)
      H.val (IntermediateField.inclusion hGH) D hl K hK


end Constructible

end WeilConjectures
