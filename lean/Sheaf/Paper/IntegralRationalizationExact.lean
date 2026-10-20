/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U9
-/
module

public import Sheaf.Paper.EtaleMonodromyRealizationData
import Sheaf.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Topology.ContinuousMap.Units
import Mathlib.RingTheory.RingHom.Flat

/-! # Exact rationalization of integral continuous coefficient modules

Source: Bhatt--Scholze, Lemma 6.8.2(2).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open scoped ChangeOfRings

open CategoryTheory CategoryTheory.Limits Opposite

namespace SfScalarExtension
variable {C : Type w} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  {A B : Sheaf J CommRingCat.{u}} (α : A ⟶ B)
set_option hygiene false in
local notation "R" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj A
set_option hygiene false in
local notation "S" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj B
set_option hygiene false in
local notation "a" => (sheafCompose J (forget₂ CommRingCat RingCat)).map α

private noncomputable def P : SheafOfModules.{u} R ⥤ PresheafOfModules.{u} (S).obj where
  obj M := SheafOfModules.changeOfRingsPresheaf α M
  map f := { app := fun U ↦ (ModuleCat.extendScalars (α.hom.app U).hom).map (f.val.app U)
             naturality := SheafOfModules.changeOfRingsHom_naturality α _ f }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.hom.app U).hom).map_id _
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.hom.app U).hom).map_comp _ _

@[irreducible] private noncomputable def F (α : A ⟶ B) :
    SheafOfModules.{u} R ⥤ SheafOfModules.{u} S :=
  P α ⋙ PresheafOfModules.sheafification (𝟙 (S).obj)

private theorem preserves (hflat : ∀ U : Cᵒᵖ, (α.hom.app U).hom.Flat) :
    PreservesFiniteLimits (F α) := by
  have hP : PreservesFiniteLimits (P α) := by
    constructor
    intro D _ _
    constructor
    intro K
    apply preservesLimit_of_preserves_limit_cone (limit.isLimit K)
    apply PresheafOfModules.evaluationJointlyReflectsLimits
    intro U
    have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat (hflat U)
    exact isLimitOfPreserves (ModuleCat.extendScalars (α.hom.app U).hom)
      (isLimitOfPreserves (SheafOfModules.evaluation R U) (limit.isLimit K))
  unfold F
  exact comp_preservesFiniteLimits (P α) (PresheafOfModules.sheafification (𝟙 (S).obj))

private theorem exact_explicit (hflat : ∀ U : Cᵒᵖ, (α.hom.app U).hom.Flat)
    (K : ShortComplex (SheafOfModules.{u} R)) (hK : K.ShortExact)
    (w : SheafOfModules.changeOfRingsHom α K.X₁ K.f ≫
      SheafOfModules.changeOfRingsHom α K.X₂ K.g = 0) :
    (ShortComplex.mk (SheafOfModules.changeOfRingsHom α K.X₁ K.f)
      (SheafOfModules.changeOfRingsHom α K.X₂ K.g) w).ShortExact := by
  have := preserves α hflat
  have : (F α).Additive := Functor.additive_of_preserves_binary_products _
  obtain ⟨_, _, hAdj⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction α
  have hobj (M : SheafOfModules.{u} R) :
      (F α).obj M = SheafOfModules.changeOfRings α M := by
    unfold F
    rfl
  have hmap {M N : SheafOfModules.{u} R} (f : M ⟶ N) :
      (F α).map f = eqToHom (hobj M) ≫ SheafOfModules.changeOfRingsHom α M f ≫
        eqToHom (hobj N).symm := by
    unfold F at hobj ⊢
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨adj, _⟩ := hAdj (F α) hobj hmap
  have := adj.isLeftAdjoint
  have h := hK.map_of_exact (F α)
  unfold F at h
  exact h

end SfScalarExtension

namespace AlgebraicGeometry.Scheme

open Topology

private theorem continuous_denominator {K : Type u} [NormedField K]
    [IsUltrametricDist K] {X : Type v} [TopologicalSpace X]
    (A : Subring K) (hA : ∀ x : K, x ∈ A ↔ ‖x‖ ≤ 1) (f : C(X, K)) :
    ∃ (a s : C(X, A)),
      (∀ x, (s x : K) ≠ 0) ∧ (∀ x, f x * (s x : K) = (a x : K)) := by
  classical
  let D : Set X := {x | ‖f x‖ ≤ 1}
  have hD : IsClopen D := by
    have h := (IsUltrametricDist.isClopen_closedBall (x := (0 : K))
      (by norm_num : (1 : ℝ) ≠ 0)).preimage f.continuous
    simpa only [D, Set.preimage_ofPred_eq, Metric.closedBall, dist_zero_right] using h
  let s₀ : X → K := D.piecewise (fun _ ↦ 1) (fun x ↦ (f x)⁻¹)
  have hs₀ : Continuous s₀ := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ D
    · have hloc : s₀ =ᶠ[nhds x] fun _ ↦ (1 : K) := by
        filter_upwards [hD.isOpen.mem_nhds hx] with y hy
        exact Set.piecewise_eq_of_mem D _ _ hy
      exact continuousAt_const.congr_of_eventuallyEq hloc
    · have hfx : f x ≠ 0 := by
        intro hz
        apply hx
        change ‖f x‖ ≤ 1
        simp [hz]
      have hloc : s₀ =ᶠ[nhds x] fun y ↦ (f y)⁻¹ := by
        filter_upwards [hD.compl.isOpen.mem_nhds hx] with y hy
        exact Set.piecewise_eq_of_notMem D _ _ hy
      exact (f.continuous.continuousAt.inv₀ hfx).congr_of_eventuallyEq hloc
  have hsA (x : X) : s₀ x ∈ A := by
    rw [hA]
    dsimp [s₀, Set.piecewise]
    split_ifs with hx
    · simp
    · rw [norm_inv]
      exact inv_le_one_of_one_le₀ (le_of_lt (lt_of_not_ge hx))
  let s : C(X, A) := ⟨fun x ↦ ⟨s₀ x, hsA x⟩, hs₀.subtype_mk _⟩
  have haA (x : X) : f x * s₀ x ∈ A := by
    rw [hA]
    dsimp [s₀, Set.piecewise]
    split_ifs with hx
    · simpa only [mul_one] using (show ‖f x‖ ≤ 1 from hx)
    · have hfx : f x ≠ 0 := by
        intro hz
        apply hx
        change ‖f x‖ ≤ 1
        simp [hz]
      simp [hfx]
  let a : C(X, A) := ⟨fun x ↦ ⟨f x * s₀ x, haA x⟩,
    (f.continuous.mul hs₀).subtype_mk _⟩
  refine ⟨a, s, ?_, fun _ ↦ rfl⟩
  intro x
  change s₀ x ≠ 0
  dsimp [s₀, Set.piecewise]
  split_ifs with hx
  · exact one_ne_zero
  · apply inv_ne_zero
    intro hz
    apply hx
    change ‖f x‖ ≤ 1
    simp [hz]

private theorem continuous_localization {K : Type u} [NormedField K]
    [IsUltrametricDist K] {X : Type v} [TopologicalSpace X]
    (A : Subring K) (hA : ∀ x : K, x ∈ A ↔ ‖x‖ ≤ 1) :
    let φ : C(X, A) →+* C(X, K) :=
      A.subtype.compLeftContinuous X continuous_subtype_val
    letI := φ.toAlgebra
    IsLocalization ((IsUnit.submonoid C(X, K)).comap φ) C(X, K) := by
  dsimp only
  let φ : C(X, A) →+* C(X, K) := A.subtype.compLeftContinuous X continuous_subtype_val
  let := φ.toAlgebra
  apply (isLocalization_iff _ _).mpr
  refine ⟨fun s ↦ s.property, ?_, ?_⟩
  · intro f
    obtain ⟨a, s, hs, ha⟩ := continuous_denominator A hA f
    refine ⟨⟨a, ⟨s, ?_⟩⟩, ?_⟩
    · exact ⟨⟨φ s, ⟨fun x ↦ (φ s x)⁻¹, s.continuous.subtype_val.inv₀ hs⟩,
        by ext x; exact mul_inv_cancel₀ (hs x),
        by ext x; exact inv_mul_cancel₀ (hs x)⟩, rfl⟩
    · ext x
      exact ha x
  · intro a b hab
    have he : a = b := by
      ext x
      exact DFunLike.congr_fun hab x
    exact ⟨1, by simp [he]⟩

private theorem continuous_flat {K : Type u} [NormedField K]
    [IsUltrametricDist K] {X : Type v} [TopologicalSpace X]
    (A : Subring K) (hA : ∀ x : K, x ∈ A ↔ ‖x‖ ≤ 1) :
    (A.subtype.compLeftContinuous X continuous_subtype_val).Flat := by
  let φ : C(X, A) →+* C(X, K) := A.subtype.compLeftContinuous X continuous_subtype_val
  let := φ.toAlgebra
  have := continuous_localization A hA (X := X)
  exact IsLocalization.flat C(X, K) ((IsUnit.submonoid C(X, K)).comap φ)

private theorem coefficient_flat (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : AlgebraicGeometry.Scheme.{u})
    (U : T.ProEtᵒᵖ) :
    ((AlgebraicGeometry.ProEtale.lisseIntegerToFieldSized l E T).hom.app U).hom.Flat := by
  let := spectralNorm.normedField ℚ_[l] E
  let := spectralNorm.normedAlgebra ℚ_[l] E
  have : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  have hA : ∀ x : E, x ∈ Padic.coefficientExtensionIntegers l E ↔ ‖x‖ ≤ 1 :=
    (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
      (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec.1
  exact ((RingHom.Flat.of_bijective ULift.ringEquiv.bijective).comp
    (continuous_flat _ hA)).comp
      (RingHom.Flat.of_bijective ULift.ringEquiv.symm.bijective)

/-- Inverting l in the continuous integral coefficient sheaf preserves short exact
sequences of arbitrary modules. Source: Bhatt--Scholze, Lemma 6.8.2(2); exactness of
filtered colimits of module sheaves, Stacks Project, Tag 03CO.
(blueprint: lem-sfb-integral-rationalization-exact)

Proof: for a continuous field-valued function f, use the clopen partition according
as its norm is at most one or greater than one. The denominator s is 1 on the first
piece and f inverse on the second. Both s and f s are integral-valued, and s is a
unit in the field-valued function ring. This identifies that ring as a localization
of the integral function ring. Localization is flat. Transport flatness through the
coefficient ULift isomorphisms. Sectionwise scalar extension and sheafification then
preserve finite limits. The ordinary coefficient adjunction makes their composite
a left adjoint, so it also preserves finite colimits and hence short exact sequences.
Its maps are precisely the supplied changeOfRingsHom maps. The calculation includes
zero modules and the empty scheme and requires no local freeness. -/
theorem sf_integral_rationalization_shortExact (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})
    (S : ShortComplex (SfIntegralModules l E T)) (hS : S.ShortExact)
    (w : SheafOfModules.changeOfRingsHom
        (ProEtale.lisseIntegerToFieldSized l E T) S.X₁ S.f ≫
      SheafOfModules.changeOfRingsHom
        (ProEtale.lisseIntegerToFieldSized l E T) S.X₂ S.g = 0) :
    (ShortComplex.mk
      (SheafOfModules.changeOfRingsHom
        (ProEtale.lisseIntegerToFieldSized l E T) S.X₁ S.f)
      (SheafOfModules.changeOfRingsHom
        (ProEtale.lisseIntegerToFieldSized l E T) S.X₂ S.g) w).ShortExact := by
  exact SfScalarExtension.exact_explicit (ProEtale.lisseIntegerToFieldSized l E T)
    (coefficient_flat l E T) S hS w

end AlgebraicGeometry.Scheme
