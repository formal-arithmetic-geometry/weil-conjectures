/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Regular.RegularQuotientRestrictionBounds
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.SixFunctors.CompletedCoefficientFree.CompletedCoefficientFreeResolution
import WeilConjectures.SixFunctors.Regular.RegularQuotientRestrictionScalars
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleLinear
import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleExactClosure
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleRestrictScalars
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Triangulated.Triangulated

/-!
# Dévissage of the finite reductions of an integral complex along the uniformizer

Let `K` be a complex of modules over the completed coefficient ring `𝒪_E` on the pro-étale site
of a scheme `T`, and write `K/π^{n+1}` for its finite reductions
`scalarReductionDerivedExtension l E T n`. We show that bounded constructibility of a single
reduction controls all of them:

* `WeilConjectures.residue_constructible_of_reduction`: if some `K/π^{m+1}` is bounded
  constructible of finite Tor amplitude, then so is the residue reduction `K/π`. Indeed,
  reducing the triangle `K --π^{m+1}--> K --> K/π^{m+1}` modulo `π` kills the first map, so the
  cohomology of `K/π` embeds into that of `(K/π^{m+1}) ⊗ᴸ 𝒪_E/π`, with the next cohomology sheaf
  as cokernel.
* `WeilConjectures.reduction_constructible_of_residue`: if `K/π` is bounded constructible with
  cohomology in `[a, b]`, then so is every reduction `K/π^{n+1}`. This uses the triangles
  `K/π^{n+1} --> K/π^{n+2} --> K/π`, obtained from the octahedral axiom applied to
  `π^{n+2} = π^{n+1} · π`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  AlgebraicGeometry.Scheme

namespace WeilConjectures

attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})

/-- The constant-section action of `𝒪_E` on the integral derived category is multiplicative. -/
theorem integralScalarDerivedAction_mul (a b : Padic.coefficientExtensionIntegers l E)
    (K : DerivedCategory (scalarReductionSource l E T)) :
    (integralScalarDerivedAction l E T (a * b)).app K =
      (integralScalarDerivedAction l E T a).app K ≫
        (integralScalarDerivedAction l E T b).app K := by
  have h := (sfIntegralConstructible_linear l E T).1
  have hab := h (a * b) K K (𝟙 K)
  have hb := h b K K (𝟙 K)
  have ha := h a K K (b • 𝟙 K)
  simp only [CategoryTheory.Functor.id_obj, Category.comp_id] at hab hb ha
  rw [← hab, mul_smul, ha, hb]

/-- Constructibility of a pro-étale module sheaf is invariant under isomorphism. -/
lemma isConstructibleProEtaleModuleSheaf_of_iso {B : Type u} [CommRing B] [Finite B]
    {F G : proEtaleRingModules T (proEtaleConstantRing T B)} (e : F ≅ G)
    (hF : IsConstructibleProEtaleModuleSheaf T B F) : IsConstructibleProEtaleModuleSheaf T B G := by
  rw [proEtaleModuleRestriction_constructible_iff] at hF ⊢
  exact ProEtale.isConstructible_of_iso ((proEtaleModuleRestriction T B).mapIso e) hF

/-- A zero pro-étale module sheaf is constructible. -/
lemma isConstructibleProEtaleModuleSheaf_of_isZero {B : Type u} [CommRing B] [Finite B]
    {F G : proEtaleRingModules T (proEtaleConstantRing T B)}
    (hF : IsConstructibleProEtaleModuleSheaf T B F) (hG : IsZero G) :
    IsConstructibleProEtaleModuleSheaf T B G :=
  isConstructibleProEtaleModuleSheaf_of_iso T ((isZero_kernel_of_mono (𝟙 F)).iso hG)
    ((constructibleProEtale_exactClosure T B).1 F F (𝟙 F) hF hF).1

/-- The reduction triangle `K --π^{n+1}--> K --> K/π^{n+1}`, with `K/π^{n+1}` restricted back
to the completed coefficients. -/
private lemma reductionTriangle_mem (n : ℕ) (K : DerivedCategory (scalarReductionSource l E T)) :
    ∃ δ, Triangle.mk ((integralScalarDerivedAction l E T
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1))).app K)
      ((derivedScalarExtensionRestrictionAdjunction l E T n).choose.unit.app K) δ ∈
        distTriang _ :=
  (CompletedCoefficientFree.completed_coefficient_free_resolution l E T).2.2 n K

/-- Reduction modulo `π` kills multiplication by a positive power of `π`. -/
private lemma residue_map_uniformizerPow (m : ℕ)
    (K : DerivedCategory (scalarReductionSource l E T)) :
    (scalarReductionDerivedExtension l E T 0).map ((integralScalarDerivedAction l E T
      (Padic.coefficientExtensionUniformizer l E ^ (m + 1))).app K) = 0 := by
  let adj := (derivedScalarExtensionRestrictionAdjunction l E T 0).choose
  have : (scalarReductionDerivedRestriction l E T 0).Additive := by
    dsimp only [scalarReductionDerivedRestriction]
    infer_instance
  have : (scalarReductionDerivedExtension l E T 0).Additive := adj.left_adjoint_additive
  obtain ⟨δ, hT⟩ := reductionTriangle_mem l E T 0 K
  have h0 := comp_distTriang_mor_zero₁₂ _ hT
  simp only [Triangle.mk_mor₁, Triangle.mk_mor₂, zero_add, pow_one] at h0
  have hπ : (scalarReductionDerivedExtension l E T 0).map ((integralScalarDerivedAction l E T
      (Padic.coefficientExtensionUniformizer l E)).app K) = 0 := by
    have key : (scalarReductionDerivedExtension l E T 0).map ((integralScalarDerivedAction l E T
        (Padic.coefficientExtensionUniformizer l E)).app K) ≫
        (scalarReductionDerivedExtension l E T 0).map (adj.unit.app K) ≫
          adj.counit.app ((scalarReductionDerivedExtension l E T 0).obj K) = 0 := by
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, h0,
        CategoryTheory.Functor.map_zero, zero_comp]
    simpa only [Adjunction.left_triangle_components, CategoryTheory.Functor.id_obj,
      Category.comp_id] using key
  rw [pow_succ, integralScalarDerivedAction_mul, CategoryTheory.Functor.map_comp, hπ,
    comp_zero]

/-- The derived restriction commutes with cohomology. -/
private def restrictionHomologyIso (n : ℕ) (j : ℤ)
    (X : DerivedCategory (scalarReductionTarget l E T n)) :
    (DerivedCategory.homologyFunctor (scalarReductionSource l E T) j).obj
        ((scalarReductionDerivedRestriction l E T n).obj X) ≅
      (scalarReductionRestriction l E T n).obj
        ((DerivedCategory.homologyFunctor _ j).obj X) :=
  (((scalarReductionRestriction l E T n).mapDerivedCategoryHomologyFunctorIso j).app X).symm

private lemma isZero_homology_restriction_iff (n : ℕ) (j : ℤ)
    (X : DerivedCategory (scalarReductionTarget l E T n)) :
    IsZero ((DerivedCategory.homologyFunctor (scalarReductionSource l E T) j).obj
        ((scalarReductionDerivedRestriction l E T n).obj X)) ↔
      IsZero ((DerivedCategory.homologyFunctor _ j).obj X) := by
  rw [Iso.isZero_iff (restrictionHomologyIso l E T n j X)]
  refine ⟨fun h ↦ ?_, fun h ↦ (scalarReductionRestriction l E T n).map_isZero h⟩
  rw [IsZero.iff_id_eq_zero]
  apply (scalarReductionRestriction l E T n).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact h.eq_of_src _ _

/-- **The residue reduction is constructible if one reduction is.** If `K/π^{m+1}` is bounded
constructible of finite Tor amplitude, then `K/π` is bounded constructible, with cohomology in an
interval `[a, b]`. -/
theorem residue_constructible_of_reduction (K : DerivedCategory (scalarReductionSource l E T))
    (m : ℕ) (hm : finiteTorConstructible l E (m + 1) (Nat.succ_pos m) T
      ((scalarReductionDerivedExtension l E T m).obj K)) :
    ∃ a b : ℤ, a ≤ b ∧
      intrinsicFiniteTorsionConstructible l E 1 le_rfl T
          ((scalarReductionDerivedExtension l E T 0).obj K) ∧
        proEtaleCohomologicalSupport ((scalarReductionDerivedExtension l E T 0).obj K) ⊆
          Set.Icc a b := by
  let := Padic.finite_coefficientExtensionRing l E 1 le_rfl
  obtain ⟨a, b, hab, hQ⟩ := scalarReductionDerivedRestriction_bounds l E T m _ hm
  obtain ⟨⟨-, hQc⟩, hQs, -⟩ := hQ 0
  let R := scalarReductionDerivedExtension l E T 0
  obtain ⟨hshift, htri⟩ :=
    (scalarReductionDerivedExistence l E T 0).choose_spec.choose_spec.2.1
  let : R.CommShift ℤ := hshift
  have : R.IsTriangulated := htri
  obtain ⟨δ, hT⟩ := reductionTriangle_mem l E T m K
  let T' := R.mapTriangle.obj (Triangle.mk ((integralScalarDerivedAction l E T
      (Padic.coefficientExtensionUniformizer l E ^ (m + 1))).app K)
    ((derivedScalarExtensionRestrictionAdjunction l E T m).choose.unit.app K) δ)
  have hRT : T' ∈ distTriang _ := R.map_distinguished _ hT
  have hzero : T'.mor₁ = 0 := residue_map_uniformizerPow l E T m K
  let H (j : ℤ) := DerivedCategory.homologyFunctor (scalarReductionTarget l E T 0) j
  -- the cohomology of `K/π` embeds into that of `(K/π^{m+1}) ⊗ᴸ 𝒪_E/π`
  have hS (i : ℤ) : (ShortComplex.mk _ _
      (DerivedCategory.HomologySequence.comp_δ T' hRT i (i + 1) rfl)).ShortExact := by
    have ex₂ := DerivedCategory.HomologySequence.exact₂ T' hRT i
    have ex₁ := DerivedCategory.HomologySequence.exact₁ T' hRT i (i + 1) rfl
    have : Mono ((H i).map T'.mor₂) :=
      ex₂.mono_g (by
        change (H i).map T'.mor₁ = 0
        rw [hzero, CategoryTheory.Functor.map_zero])
    have : Epi (DerivedCategory.HomologySequence.δ T' i (i + 1) rfl) :=
      ex₁.epi_f (by
        change (H (i + 1)).map T'.mor₁ = 0
        rw [hzero, CategoryTheory.Functor.map_zero])
    exact ⟨DerivedCategory.HomologySequence.exact₃ T' hRT i (i + 1) rfl⟩
  have hsupp : proEtaleCohomologicalSupport (R.obj K) ⊆ Set.Icc a b := by
    intro i hi
    apply hQs
    intro hz
    have := (hS i).mono_f
    exact hi (hz.of_mono ((H i).map T'.mor₂))
  obtain ⟨hk, -⟩ := constructibleProEtale_exactClosure T (Padic.coefficientExtensionRing l E 1)
  -- descending induction on the degree
  have hcon : ∀ k : ℕ, ∀ i : ℤ, b < i + k →
      IsConstructibleProEtaleModuleSheaf T (Padic.coefficientExtensionRing l E 1)
        ((H i).obj (R.obj K)) := by
    intro k
    induction k with
    | zero =>
      intro i hi
      refine isConstructibleProEtaleModuleSheaf_of_isZero T (hQc i) ?_
      by_contra hz
      have := (hsupp hz).2
      push_cast at hi
      omega
    | succ k ih =>
      intro i hi
      have h₁ := ih (i + 1) (by push_cast at hi ⊢; omega)
      have := (hS i).mono_f
      exact isConstructibleProEtaleModuleSheaf_of_iso T
        ((hS i).exact.fIsKernel.conePointUniqueUpToIso (kernelIsKernel _)).symm
        (hk _ _ _ (hQc i) h₁).1
  refine ⟨a, b, hab, ⟨(Set.finite_Icc a b).subset hsupp, fun i ↦ ?_⟩, hsupp⟩
  exact hcon (b - i + 1).toNat i (by omega)

/-- **All reductions are constructible if the residue reduction is.** If `K/π` is bounded
constructible with cohomology in `[a, b]`, then so is every reduction `K/π^{n+1}`. -/
theorem reduction_constructible_of_residue (K : DerivedCategory (scalarReductionSource l E T))
    (a b : ℤ)
    (h₀ : intrinsicFiniteTorsionConstructible l E 1 le_rfl T
      ((scalarReductionDerivedExtension l E T 0).obj K))
    (hs₀ : proEtaleCohomologicalSupport ((scalarReductionDerivedExtension l E T 0).obj K) ⊆
      Set.Icc a b) (n : ℕ) :
    intrinsicFiniteTorsionConstructible l E (n + 1) (Nat.succ_pos n) T
        ((scalarReductionDerivedExtension l E T n).obj K) ∧
      proEtaleCohomologicalSupport ((scalarReductionDerivedExtension l E T n).obj K) ⊆
        Set.Icc a b := by
  induction n with
  | zero => exact ⟨h₀, hs₀⟩
  | succ n ih =>
    let := Padic.finite_coefficientExtensionRing l E 1 le_rfl
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    let := Padic.finite_coefficientExtensionRing l E (n + 1 + 1) (Nat.succ_pos (n + 1))
    let act (j : ℕ) := (integralScalarDerivedAction l E T
      (Padic.coefficientExtensionUniformizer l E ^ (j + 1))).app K
    obtain ⟨δ₁₂, h₁₂⟩ := reductionTriangle_mem l E T n K
    obtain ⟨δ₂₃, h₂₃⟩ := reductionTriangle_mem l E T 0 K
    obtain ⟨δ₁₃, h₁₃⟩ := reductionTriangle_mem l E T (n + 1) K
    have comm : act n ≫ act 0 = act (n + 1) := by
      simp only [act]
      rw [← integralScalarDerivedAction_mul, ← pow_add]
    let O := Triangulated.someOctahedron comm h₁₂ h₂₃ h₁₃
    have hT := O.mem
    let H (j : ℤ) := DerivedCategory.homologyFunctor (scalarReductionSource l E T) j
    let red (k : ℕ) := scalarReductionDerivedExtension l E T k
    -- the triangle `K/π^{n+1} --> K/π^{n+2} --> K/π` gives the support bound
    have hsupp : proEtaleCohomologicalSupport ((red (n + 1)).obj K) ⊆ Set.Icc a b := by
      intro i hi
      by_contra hni
      apply hi
      refine (isZero_homology_restriction_iff l E T (n + 1) i _).1 ?_
      refine (DerivedCategory.HomologySequence.exact₂ _ hT i).isZero_X₂ ?_ ?_
      · refine IsZero.eq_of_src ?_ _ _
        change IsZero ((H i).obj ((scalarReductionDerivedRestriction l E T n).obj ((red n).obj K)))
        exact (isZero_homology_restriction_iff l E T n i _).2
          (by by_contra h; exact hni (ih.2 h))
      · refine IsZero.eq_of_tgt ?_ _ _
        change IsZero ((H i).obj ((scalarReductionDerivedRestriction l E T 0).obj ((red 0).obj K)))
        exact (isZero_homology_restriction_iff l E T 0 i _).2
          (by by_contra h; exact hni (hs₀ h))
    refine ⟨⟨(Set.finite_Icc a b).subset hsupp, fun i ↦ ?_⟩, hsupp⟩
    -- the five-term exact sequence of cohomology, restricted to `𝒪_E/π^{n+2}`
    have hn : n ≤ n + 1 := Nat.le_succ n
    have h0 : 0 ≤ n + 1 := Nat.zero_le _
    let en := scalarReductionRestrictionTransitionIso l E T hn
    let e0 := scalarReductionRestrictionTransitionIso l E T h0
    obtain ⟨hk, hext⟩ :=
      constructibleProEtale_exactClosure T (Padic.coefficientExtensionRing l E (n + 1 + 1))
    have ex₁ := DerivedCategory.HomologySequence.exact₁ _ hT (i - 1) i (sub_add_cancel i 1)
    have ex₂ := DerivedCategory.HomologySequence.exact₂ _ hT i
    have ex₃ := DerivedCategory.HomologySequence.exact₃ _ hT i (i + 1) rfl
    exact ObjectProperty.prop_X₃_of_exact_of_fullyFaithful
      (scalarReductionRestriction l E T (n + 1))
      (IsConstructibleProEtaleModuleSheaf T (Padic.coefficientExtensionRing l E (n + 1 + 1)))
      (fun _ _ f hX hY ↦ (hk _ _ f hX hY).1) (fun _ _ f hX hY ↦ (hk _ _ f hX hY).2) hext
      ex₁ ex₂ ex₃
      (restrictionHomologyIso l E T 0 (i - 1) _ ≪≫ (e0.app _).symm)
      (restrictionHomologyIso l E T n i _ ≪≫ (en.app _).symm)
      (restrictionHomologyIso l E T (n + 1) i _)
      (restrictionHomologyIso l E T 0 i _ ≪≫ (e0.app _).symm)
      (restrictionHomologyIso l E T n (i + 1) _ ≪≫ (en.app _).symm)
      ((h₀.2 (i - 1)).restrictScalars _) ((ih.1.2 i).restrictScalars _)
      ((h₀.2 i).restrictScalars _) ((ih.1.2 (i + 1)).restrictScalars _)

end WeilConjectures
