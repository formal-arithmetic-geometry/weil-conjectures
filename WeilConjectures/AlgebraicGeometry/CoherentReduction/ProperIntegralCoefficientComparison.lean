/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoherentReduction.CoherentIntegralReduction
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.Algebra.Field.ULift

import Mathlib.Condensed.TopComparison
import Mathlib.Topology.Category.Profinite.EffectiveEpi

/-! # Comparing embedded and spectral integral coefficients

Source: Bhatt--Scholze, Lemma 4.2.12 and the paragraph before Definition 6.5.1;
uniqueness of the extension of the p-adic norm.
(blueprint: lem-sfb-proper-integral-coefficient-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CoherentReduction

private theorem spectralEmbeddedNorm
    (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E]
    [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
    (x : ULift.{u + 1} E) :
    Padic.coefficientExtensionAbsoluteValue l (ULift.{u + 1} E) x =
      ‖algebraMap E (PadicAlgCl l) x.down‖ := by
  let f : ULift.{u + 1} E →+* PadicAlgCl l :=
    (algebraMap E (PadicAlgCl l)).comp ULift.ringEquiv.toRingHom
  let a : AbsoluteValue (ULift.{u + 1} E) ℝ :=
    { toFun := fun x ↦ ‖f x‖
      map_mul' := fun x y ↦ by rw [map_mul, norm_mul]
      nonneg' := fun x ↦ norm_nonneg _
      eq_zero' := fun x ↦ by simp only [norm_eq_zero, map_eq_zero_iff f f.injective]
      add_le' := fun x y ↦ by rw [map_add]; exact norm_add_le _ _ }
  have ha : ∀ y : ℚ_[l], a (algebraMap ℚ_[l] (ULift.{u + 1} E) y) = ‖y‖ := by
    intro y
    change ‖algebraMap E (PadicAlgCl l) (algebraMap ℚ_[l] E y)‖ = ‖y‖
    rw [← IsScalarTower.algebraMap_apply ℚ_[l] E (PadicAlgCl l)]
    exact PadicAlgCl.norm_extends l y
  exact (spectralNorm_unique_field_norm_ext ha x).symm

private theorem memLiftIntegers
    (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E]
    [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
    (x : ULift.{u + 1} E) :
    x ∈ Padic.coefficientExtensionIntegers l (ULift.{u + 1} E) ↔
      x.down ∈ PadicAlgCl.integers l E := by
  have h := (Padic.extension_integers_dvr l (ULift.{u + 1} E)
    (Padic.coefficientExtensionAbsoluteValue l (ULift.{u + 1} E))
    (spectralNorm_extends (K := ℚ_[l]) (L := ULift.{u + 1} E))).choose_spec.choose_spec.1 x
  rw [spectralEmbeddedNorm l E x] at h
  exact h.trans (by
    rw [PadicAlgCl.mem_integers_iff, ← NNReal.coe_le_coe]
    rfl)

private def integersLiftEquiv
    (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E]
    [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] :
    PadicAlgCl.integers l E ≃+* Padic.coefficientExtensionIntegers l (ULift.{u + 1} E) where
  toFun x := ⟨ULift.up x.val, (memLiftIntegers l E _).mpr x.property⟩
  invFun x := ⟨x.val.down, (memLiftIntegers l E _).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private def integersLiftHomeo
    (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E]
    [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] :
    letI := PadicAlgCl.normedFieldOfAlgebra l E
    PadicAlgCl.integers l E ≃ₜ Padic.coefficientExtensionIntegers l (ULift.{u + 1} E) := by
  letI := PadicAlgCl.normedFieldOfAlgebra l E
  let N := spectralNorm.normedField ℚ_[l] (ULift.{u + 1} E)
  letI : NormedField (ULift.{u + 1} E) := N
  letI : Norm (ULift.{u + 1} E) := N.toNorm
  letI : PseudoMetricSpace (ULift.{u + 1} E) := N.toMetricSpace.toPseudoMetricSpace
  letI : PseudoEMetricSpace (ULift.{u + 1} E) := N.toMetricSpace.toPseudoEMetricSpace
  let e := integersLiftEquiv.{u} l E
  have hi : Isometry e := by
    apply Isometry.of_dist_eq
    intro x y
    simp only [dist_eq_norm]
    change Padic.coefficientExtensionAbsoluteValue l (ULift.{u + 1} E)
      (ULift.up (x.val - y.val)) = ‖algebraMap E (PadicAlgCl l) (x.val - y.val)‖
    exact spectralEmbeddedNorm l E _
  exact { e.toEquiv with
    continuous_toFun := hi.continuous
    continuous_invFun := (hi.right_inv e.right_inv).continuous }

private theorem continuousPresheafIsSheaf
    (T : Type (u + 1)) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] :
    Presheaf.IsSheaf (coherentTopology Profinite.{u}) (continuousPresheaf T) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget CommRingCat.{u + 1})]
  change Presheaf.IsSheaf _ (ContinuousMap.yonedaPresheaf Profinite.toTopCat.{u} T)
  rw [Presheaf.isSheaf_iff_preservesFiniteProducts_and_equalizerCondition]
  refine ⟨inferInstance, ?_⟩
  apply +allowSynthFailures equalizerCondition_yonedaPresheaf Profinite.toTopCat.{u} T
  intro Z B π hπ
  exact .of_surjective_continuous (((Profinite.effectiveEpi_tfae π).out 0 2).mp hπ)
    π.hom.hom.continuous

/-- The actual condensed rings of integers agree under the universe-lifted inclusion.

Source: Bhatt--Scholze, Lemma 4.2.12 and the paragraph before Definition 6.5.1;
uniqueness of the extension of the p-adic norm
(blueprint: lem-sfb-proper-integral-coefficient-comparison).

Proof: the pullback of the norm of the fixed embedding into the algebraic closure
extends the p-adic norm. Uniqueness identifies it with the spectral norm. Thus the
lifted embedding identifies the two unit balls, as topological rings. Continuous
functions into these rings form naturally isomorphic ring presheaves. Continuous
functions satisfy descent for surjective maps of profinite spaces, so the spectral
presheaf is already a sheaf; the sheafification counit is an isomorphism. Forgetting
multiplication retains a monoid-object isomorphism, not merely an additive one. -/
theorem properIntegralCoefficientIso
    (l : ℕ) [Fact l.Prime]
    (E : Type) [Field E] [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E]
    [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E] :
    Nonempty (Mon.mk (Profinite.padicIntegersRingObj.{u} l E) ≅
      Mon.mk (abelianPoint (Padic.coefficientExtensionIntegers l (ULift.{u + 1} E)))) := by
  let := PadicAlgCl.normedFieldOfAlgebra l E
  let T := Padic.coefficientExtensionIntegers l (ULift.{u + 1} E)
  let S : Sheaf (coherentTopology Profinite.{u}) CommRingCat.{u + 1} :=
    ⟨continuousPresheaf T, continuousPresheafIsSheaf T⟩
  let c : continuousPoint T ≅ S :=
    asIso ((sheafificationAdjunction _ CommRingCat.{u + 1}).counit.app S)
  let V := sheafCompose (coherentTopology Profinite.{u})
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let e := integersLiftEquiv.{u} l E
  let h := integersLiftHomeo.{u} l E
  let forward (U : Profinite.{u}ᵒᵖ) : ULift.{u + 1} C(U.unop, PadicAlgCl.integers l E) →+*
      C(U.unop, T) :=
    (e.toRingHom.compLeftContinuous _ h.continuous_toFun).comp ULift.ringEquiv.toRingHom
  let backward (U : Profinite.{u}ᵒᵖ) : C(U.unop, T) →+*
      ULift.{u + 1} C(U.unop, PadicAlgCl.integers l E) :=
    ULift.ringEquiv.symm.toRingHom.comp
      (e.symm.toRingHom.compLeftContinuous _ h.continuous_invFun)
  let d : Profinite.padicIntegersCondensedRing.{u} l E ≅ V.obj S :=
    { hom := ⟨{ app := fun U ↦ RingCat.ofHom (forward U)
                naturality := by intros; ext x; rfl }⟩
      inv := ⟨{ app := fun U ↦ RingCat.ofHom (backward U)
                naturality := by intros; ext x; rfl }⟩
      hom_inv_id := by ext U x; apply ULift.ext; ext t; rfl
      inv_hom_id := by ext U x; apply ContinuousMap.ext; intro t; rfl }
  let q := d ≪≫ (V.mapIso c).symm
  let W := sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat.{u + 1} Ab.{u + 1})
  have : IsMonHom (W.mapIso q).hom := by dsimp [W]; infer_instance
  exact ⟨Mon.mkIso' (W.mapIso q)⟩

end AlgebraicGeometry.ProEtale.CoherentReduction
