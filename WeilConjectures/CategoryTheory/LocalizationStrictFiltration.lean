/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Group.TransferInstance
public import WeilConjectures.CategoryTheory.FiniteFilteredGradedExactness
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The strict two-step filtration of a natural monomorphism

Source: the strict filtration in Step 2 of the open--closed trace-additivity proof;
Stacks Tags 0121 and 03TF (blueprint: lem-trf-localization-strict-filtration).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
  (J : C ⥤ C) (a : J ⟶ 𝟭 C) [∀ M, Mono (a.app M)]

/-- The whole object, the specified monomorphism, and zero, in that order.
Source: Stacks Tag 0121, blueprint Step 2
(blueprint: lem-trf-localization-strict-filtration). -/
def localizationStrictStep (M : C) (p : ℤ) : Subobject M :=
  if p ≤ 0 then ⊤ else if p = 1 then Subobject.mk (a.app M) else ⊥

theorem localizationStrictStep_succ_le (M : C) (p : ℤ) :
    localizationStrictStep J a M (p + 1) ≤ localizationStrictStep J a M p := by
  by_cases hp : p ≤ 0
  · simp [localizationStrictStep, hp]
  · have hq : ¬p + 1 ≤ 0 := by omega
    have hq' : p + 1 ≠ 1 := by omega
    simp [localizationStrictStep, hq, hq']

/-- The actual decreasing filtration represented by the natural monomorphism.
Source: Stacks Tag 0121, blueprint Step 2
(blueprint: lem-trf-localization-strict-filtration). -/
abbrev localizationStrictFiltration (M : C) : DecreasingFiltration M where
  F := localizationStrictStep J a M
  F_succ_le := localizationStrictStep_succ_le J a M

theorem localizationStrictFiltration_finite (M : C) :
    (localizationStrictFiltration J a M).IsFinite := by
  exact ⟨0, 2, by simp [localizationStrictStep],
    by simp [localizationStrictStep]⟩

theorem localizationStrictMap_preserves {M N : C} (f : M ⟶ N) (p : ℤ) :
    ∃ l : ((localizationStrictFiltration J a M).step p : C) ⟶
        ((localizationStrictFiltration J a N).step p : C),
      l ≫ ((localizationStrictFiltration J a N).step p).arrow =
        ((localizationStrictFiltration J a M).step p).arrow ≫ f := by
  change ∃ l : (localizationStrictStep J a M p : C) ⟶
      (localizationStrictStep J a N p : C),
      l ≫ (localizationStrictStep J a N p).arrow =
        (localizationStrictStep J a M p).arrow ≫ f
  by_cases hp : p ≤ 0
  · have hM : localizationStrictStep J a M p = ⊤ := by simp [localizationStrictStep, hp]
    have hN : localizationStrictStep J a N p = ⊤ := by simp [localizationStrictStep, hp]
    rw [hM, hN]
    refine ⟨(⊤ : Subobject M).arrow ≫ f ≫ inv (⊤ : Subobject N).arrow, ?_⟩
    simp
  · by_cases hq : p = 1
    · have hM : localizationStrictStep J a M p = Subobject.mk (a.app M) := by
        simp [localizationStrictStep, hq]
      have hN : localizationStrictStep J a N p = Subobject.mk (a.app N) := by
        simp [localizationStrictStep, hq]
      rw [hM, hN]
      refine ⟨(Subobject.underlyingIso (a.app M)).hom ≫ J.map f ≫
        (Subobject.underlyingIso (a.app N)).inv, ?_⟩
      simp only [Category.assoc, Subobject.underlyingIso_arrow]
      rw [a.naturality f]
      simp
    · have hM : localizationStrictStep J a M p = ⊥ := by simp [localizationStrictStep, hp, hq]
      have hN : localizationStrictStep J a N p = ⊥ := by simp [localizationStrictStep, hp, hq]
      rw [hM, hN]
      exact ⟨0, by simp⟩

variable (I : C ⥤ C) (q : 𝟭 C ⟶ I)
  (hzero : ∀ M, a.app M ≫ q.app M = 0)
  (hseq : ∀ M, (ShortComplex.mk (a.app M) (q.app M) (hzero M)).ShortExact)

omit I q hzero hseq in
end CategoryTheory
