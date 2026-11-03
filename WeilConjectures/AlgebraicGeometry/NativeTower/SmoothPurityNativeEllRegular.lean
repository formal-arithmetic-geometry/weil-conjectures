/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.NativeTower.SmoothPurityNativeTowerLimitData
public import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReduction

/-! # Regularity of ell on the native integral section ring

Source: current blueprint sk-lem-sp-tower, first paragraph and native completion step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.NativeTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- The compatible constant section ell in the native integral section ring.
Source: current blueprint sk-lem-sp-tower, the actual ell-power reduction tower
(blueprint: lem-sp-native-ell-regular). -/
def ellSection : (SheafOfModules.unit
    (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) (spIntegralSectionRing l E T))).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ (l : (spIntegralSectionRing l E T).obj.obj U))
    (fun {_ _} f ↦ map_natCast ((spIntegralSectionRing l E T).obj.map f).hom l)

/-- The constant prime acts monomorphically on the native integral section ring.
Source: current blueprint sk-lem-sp-tower, first paragraph; the regularity of the
continuous DVR coefficient ring (blueprint: lem-sp-native-ell-regular).

Proof: on a profinite test object multiplication by the nonzero prime is injective
on continuous functions into the characteristic-zero integer domain. Thus the
prime multiple of the identity is monic on the condensed ring. Exact inverse image
preserves this monomorphism. The section-ring realization has the same underlying
abelian sheaf; its multiplication by the constant prime is this same prime multiple
of the identity. The faithful forgetful functor reflects monomorphisms. -/
theorem ell_regular :
    Mono (globalSectionMultiplication (spIntegralSectionRing l E T) (ellSection l E T)) := by
  let := spectralNorm.normedField (Padic l) E
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap (Padic l) E).injective
  let A := spIntegralCondensed l E
  let f : A ⟶ A := l • 𝟙 A
  have hf : Mono f := by
    have happ (S : Profinite.{u}ᵒᵖ) : Mono (f.hom.app S) := by
      apply (AddCommGrpCat.mono_iff_injective _).mpr
      intro x y h
      apply ULift.ext
      apply ContinuousMap.ext
      intro s
      have hxy := congrArg (fun z ↦ z.down s) h
      change l • x.down s = l • y.down s at hxy
      have hl : (l : Padic.coefficientExtensionIntegers l E) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
      exact mul_left_cancel₀ hl (by simpa only [nsmul_eq_mul] using hxy)
    have : ∀ S : Profinite.{u}ᵒᵖ, Mono (f.hom.app S) := happ
    have : Mono f.hom := NatTrans.mono_of_mono_app f.hom
    exact (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mono_of_mono_map
      (inferInstance : Mono f.hom)
  have hpa : (upperStarFromPoint T).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hpf : Mono ((upperStarFromPoint T).map f) := by infer_instance
  have hm : globalSectionMultiplication (spIntegralSectionRing l E T) (ellSection l E T) =
      l • 𝟙 (SheafOfModules.unit
        (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
          (Scheme.ProEt.topology T) (spIntegralSectionRing l E T))) := by
    apply (SheafOfModules.unitHomEquiv _).injective
    change (SheafOfModules.unitHomEquiv _)
      ((SheafOfModules.unitHomEquiv _).symm (ellSection l E T)) = _
    rw [Equiv.apply_symm_apply]
    apply PresheafOfModules.sections_ext
    intro U
    rw [SheafOfModules.unitHomEquiv_apply_coe]
    let M := SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (spIntegralSectionRing l E T))
    have hv (n : ℕ) : ((n • 𝟙 M).val.app U)
        (1 : (spIntegralSectionRing l E T).obj.obj U) =
          (n : (spIntegralSectionRing l E T).obj.obj U) := by
      induction n with
      | zero => rfl
      | succ n ih =>
        rw [succ_nsmul]
        change (show (spIntegralSectionRing l E T).obj.obj U from
          ((n • 𝟙 M).val.app U) (1 : (spIntegralSectionRing l E T).obj.obj U)) +
            (1 : (spIntegralSectionRing l E T).obj.obj U) = _
        rw [ih, Nat.cast_succ]
    exact (hv l).symm
  rw [hm]
  apply (SheafOfModules.toSheaf _).mono_of_mono_map
  simp only [Functor.map_nsmul]
  change Mono (l • 𝟙 (condensedRingObj A T))
  have he : (upperStarFromPoint T).map f = l • 𝟙 (condensedRingObj A T) := by
    simp only [f, Functor.map_nsmul]
    exact congrArg (fun z ↦ l • z) ((upperStarFromPoint T).map_id A)
  rw [← he]
  exact hpf

end AlgebraicGeometry.ProEtale.NativeTower
