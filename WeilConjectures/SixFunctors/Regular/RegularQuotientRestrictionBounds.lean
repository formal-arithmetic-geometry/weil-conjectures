/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
import WeilConjectures.SixFunctors.CompletedCoefficientFree.CompletedCoefficientFreeResolution
import WeilConjectures.SixFunctors.Integral.IntegralReductionTorAmplitude
import WeilConjectures.SixFunctors.Regular.RegularQuotientRestrictionScalars
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleExactClosure
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleRestrictScalars
import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Uniform constructibility and Tor bounds for finite quotient restriction

## References

* [Stacks, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [Stacks, Tag 0BZH](https://stacks.math.columbia.edu/tag/0BZH)
* [Stacks, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
* Zheng, Lemma 5.22 and Proposition 5.26
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits

open CategoryTheory.Limits

/-- The cohomology sheaves of a finite reduction of the restriction of a finite-level complex
`K` are controlled by those of `K`: the `i`-th one vanishes if the `i`-th and `(i+1)`-st
cohomology sheaves of `K` vanish, and it is constructible if all cohomology sheaves of `K`
are constructible. -/
theorem scalarReductionDerivedRestriction_reduction_homology
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (K : DerivedCategory (scalarReductionTarget.{u, u} l E T n)) (m : ℕ) (i : ℤ) :
    (IsZero ((DerivedCategory.homologyFunctor _ i).obj K) →
      IsZero ((DerivedCategory.homologyFunctor _ (i + 1)).obj K) →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((scalarReductionDerivedExtension.{u, u} l E T m).obj
          ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)))) ∧
    (letI := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega);
      letI := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega);
      (∀ j : ℤ, IsConstructibleProEtaleModuleSheaf T (Padic.coefficientExtensionRing l E (n + 1))
        ((DerivedCategory.homologyFunctor (proEtaleRingModules T
          (proEtaleConstantRing T (Padic.coefficientExtensionRing l E (n + 1)))) j).obj K)) →
      IsConstructibleProEtaleModuleSheaf T (Padic.coefficientExtensionRing l E (m + 1))
        ((DerivedCategory.homologyFunctor (proEtaleRingModules T
          (proEtaleConstantRing T (Padic.coefficientExtensionRing l E (m + 1)))) i).obj
          ((scalarReductionDerivedExtension.{u, u} l E T m).obj
            ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)))) := by
  let M := (scalarReductionDerivedRestriction.{u, u} l E T n).obj K
  let C := (scalarReductionDerivedExtension.{u, u} l E T m).obj M
  obtain ⟨δ, hT⟩ :=
    (CompletedCoefficientFree.completed_coefficient_free_resolution l E T).2.2 m M
  let H (j : ℤ) := DerivedCategory.homologyFunctor (scalarReductionSource.{u, u} l E T) j
  let eK (j : ℤ) : (H j).obj M ≅ (scalarReductionRestriction.{u, u} l E T n).obj
      ((DerivedCategory.homologyFunctor _ j).obj K) :=
    (((scalarReductionRestriction.{u, u} l E T n).mapDerivedCategoryHomologyFunctorIso j).app
      K).symm
  let eC : (H i).obj ((scalarReductionDerivedRestriction.{u, u} l E T m).obj C) ≅
      (scalarReductionRestriction.{u, u} l E T m).obj
        ((DerivedCategory.homologyFunctor _ i).obj C) :=
    (((scalarReductionRestriction.{u, u} l E T m).mapDerivedCategoryHomologyFunctorIso i).app
      C).symm
  have ex₂ := DerivedCategory.HomologySequence.exact₂ _ hT i
  have ex₃ := DerivedCategory.HomologySequence.exact₃ _ hT i (i + 1)
  have ex₁ := DerivedCategory.HomologySequence.exact₁ _ hT i (i + 1)
  constructor
  · intro h₀ h₁
    have hz : IsZero ((H i).obj ((scalarReductionDerivedRestriction.{u, u} l E T m).obj C)) := by
      exact ex₃.isZero_X₂_iff.2 ⟨(((scalarReductionRestriction.{u, u} l E T n).map_isZero h₀).of_iso
        (eK i)).eq_of_src _ _, (((scalarReductionRestriction.{u, u} l E T n).map_isZero
          h₁).of_iso (eK (i + 1))).eq_of_tgt _ _⟩
    rw [IsZero.iff_id_eq_zero]
    apply (scalarReductionRestriction.{u, u} l E T m).map_injective
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
    exact (hz.of_iso eC.symm).eq_of_src _ _
  · intro hc
    have hn : n ≤ n + m := Nat.le_add_right n m
    have hm : m ≤ n + m := Nat.le_add_left m n
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
    let := Padic.finite_coefficientExtensionRing l E (m + 1) (by omega)
    let := Padic.finite_coefficientExtensionRing l E (n + m + 1) (by omega)
    let en := scalarReductionRestrictionTransitionIso l E T hn
    let em := scalarReductionRestrictionTransitionIso l E T hm
    obtain ⟨hk, hext⟩ :=
      constructibleProEtale_exactClosure T (Padic.coefficientExtensionRing l E (n + m + 1))
    have hP := ObjectProperty.prop_X₃_of_exact_of_fullyFaithful
      (scalarReductionRestriction.{u, u} l E T (n + m))
      (IsConstructibleProEtaleModuleSheaf T (Padic.coefficientExtensionRing l E (n + m + 1)))
      (fun _ _ f hX hY ↦ (hk _ _ f hX hY).1) (fun _ _ f hX hY ↦ (hk _ _ f hX hY).2) hext
      ex₂ ex₃ ex₁ (eK i ≪≫ (en.app _).symm) (eK i ≪≫ (en.app _).symm)
      (eC ≪≫ (em.app _).symm) (eK (i + 1) ≪≫ (en.app _).symm)
      (eK (i + 1) ≪≫ (en.app _).symm)
      ((hc i).restrictScalars _) ((hc i).restrictScalars _)
      ((hc (i + 1)).restrictScalars _) ((hc (i + 1)).restrictScalars _)
    exact IsConstructibleProEtaleModuleSheaf.of_restrictScalars _
      (coefficientExtensionRingMap_surjective l E hm) hP

/-- Restriction of a finite-Tor constructible quotient complex has constructible finite
reductions with one cohomological and Tor interval, independent of the reduction level. -/
theorem scalarReductionDerivedRestriction_bounds
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (n : ℕ)
    (K : DerivedCategory (scalarReductionTarget.{u, u} l E T n))
    (hK : finiteTorConstructible l E (n + 1) (Nat.succ_pos n) T K) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ m : ℕ,
      intrinsicFiniteTorsionConstructible l E (m + 1) (Nat.succ_pos m) T
          ((scalarReductionDerivedExtension.{u, u} l E T m).obj
            ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)) ∧
        proEtaleCohomologicalSupport
          ((scalarReductionDerivedExtension.{u, u} l E T m).obj
            ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)) ⊆ Set.Icc a b ∧
        HasProEtaleTorAmplitude T (Padic.coefficientExtensionRing l E (m + 1))
          ((scalarReductionDerivedExtension.{u, u} l E T m).obj
            ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)) a b := by
  obtain ⟨⟨hfin, hcon⟩, -⟩ := hK
  obtain ⟨s, t, hst, hK⟩ : ∃ s t : ℤ, s ≤ t ∧ ∀ i : ℤ,
      ¬ IsZero ((DerivedCategory.homologyFunctor _ i).obj K) → s ≤ i ∧ i ≤ t := by
    obtain ⟨s, hs⟩ := hfin.bddBelow
    obtain ⟨t, ht⟩ := hfin.bddAbove
    exact ⟨min s t, t, min_le_right _ _,
      fun i hi ↦ ⟨(min_le_left _ _).trans (hs hi), ht hi⟩⟩
  have hsupp (m : ℕ) : proEtaleCohomologicalSupport
      ((scalarReductionDerivedExtension.{u, u} l E T m).obj
        ((scalarReductionDerivedRestriction.{u, u} l E T n).obj K)) ⊆ Set.Icc (s - 1) t := by
    intro i hi
    by_contra hni
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hni
    apply hi
    refine (scalarReductionDerivedRestriction_reduction_homology l E T n K m i).1 ?_ ?_
    · by_contra h
      have := hK i h
      omega
    · by_contra h
      have := hK (i + 1) h
      omega
  refine ⟨s - 1, t, by omega, fun m ↦ ⟨⟨(Set.finite_Icc (s - 1) t).subset (hsupp m),
    fun i ↦ (scalarReductionDerivedRestriction_reduction_homology l E T n K m i).2 hcon⟩,
    hsupp m, ?_⟩⟩
  exact scalarReductionDerivedExtension_torAmplitude_of_residue_support l E T _ (s - 1) t
    (by omega) (fun i hi ↦ hsupp 0 hi) m

end WeilConjectures
