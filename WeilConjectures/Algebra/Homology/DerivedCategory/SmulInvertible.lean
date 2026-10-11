/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.HomologyProducts
public import WeilConjectures.CategoryTheory.Triangulated.SmulInvertible
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Objects without maps from `ϖ`-invertible objects, homology sheaf by homology sheaf

Let `C` be an abelian category which is linear over a commutative ring `R`, has K-injective
resolutions, and in which countable products exist and are exact (for instance sheaves of
modules on the pro-étale site of a scheme). Let `ϖ ∈ R`. An object `K` of `D(C)` receives no
nonzero morphism from an object on which `ϖ` acts invertibly if and only if each of its
homology objects `Hⁿ K`, placed in degree `0`, has this property
(`DerivedCategory.rightOrthogonal_smulInvertible_iff_singleFunctor`). For a nonzerodivisor `ϖ`
of `R = Λ` and `C` the sheaves of `Λ`-modules on a site, this is the statement that a complex
is derived complete for `(ϖ)` if and only if its cohomology sheaves are (Stacks, Tag 091P;
[BS, Proposition 3.4.4] for the pro-étale site).

Both conditions are tested on `1 - ϖ • s` acting on a countable product, where `s` is the shift
of the factors (`CategoryTheory.Pretriangulated.rightOrthogonal_smulInvertible_iff`), and the
homology functors commute with countable products because these are exact.

As a consequence, the truncations of such an object for the canonical t-structure have the
same property (`DerivedCategory.rightOrthogonal_smulInvertible_truncLT_obj`,
`DerivedCategory.rightOrthogonal_smulInvertible_truncGE_obj`).
-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory

variable {R : Type*} [CommRing R] {C : Type*} [Category C] [Abelian C] [Linear R C]
  [HasDerivedCategory C] [Abelian.HasKInjectiveResolutions C]
  [HasLimitsOfShape (Discrete ℕ) C] [HasExactLimitsOfShape (Discrete ℕ) C]

/-- An object of `D(C)` receives no nonzero morphism from an object on which `ϖ` acts invertibly
if and only if, for every `n`, the endomorphism `1 - ϖ • s` of `∏ₖ Hⁿ K` is an isomorphism. -/
theorem rightOrthogonal_smulInvertible_iff (ϖ : R) (K : DerivedCategory C) :
    (smulInvertible (DerivedCategory C) ϖ).rightOrthogonal K ↔
      ∀ n : ℤ, IsIso (𝟙 _ - ϖ • fanShift
        (productIsProduct fun _ : ℕ ↦ (homologyFunctor C n).obj K)) := by
  rw [Pretriangulated.rightOrthogonal_smulInvertible_iff ϖ (productIsProduct fun _ : ℕ ↦ K),
    isIso_iff]
  refine forall_congr' fun n ↦ ?_
  let H := homologyFunctor C n
  have hH : IsLimit (Fan.mk (H.obj (∏ᶜ fun _ : ℕ ↦ K)) fun i ↦ H.map (Pi.π _ i)) :=
    isLimitFanMkObjOfIsLimit H _ _ (productIsProduct _)
  have hs : H.map (fanShift (productIsProduct fun _ : ℕ ↦ K)) = fanShift hH :=
    Fan.IsLimit.hom_ext hH _ _ fun i ↦ by
      rw [fanShift_proj]
      change H.map _ ≫ H.map (Pi.π (fun _ : ℕ ↦ K) i) = H.map (Pi.π (fun _ : ℕ ↦ K) (i + 1))
      rw [← H.map_comp]
      exact congrArg H.map (fanShift_proj (productIsProduct fun _ : ℕ ↦ K) i)
  have : H.map (𝟙 _ - ϖ • fanShift (productIsProduct fun _ : ℕ ↦ K)) =
      𝟙 _ - ϖ • fanShift hH := by
    rw [Functor.map_sub, CategoryTheory.Functor.map_id, Functor.map_smul, hs]
    rfl
  rw [this]
  exact isIso_one_sub_smul_fanShift_iff_of_iso (Iso.refl _) hH (productIsProduct _) ϖ

/-- An object `M` of `C`, placed in degree `0` of `D(C)`, receives no nonzero morphism from an
object on which `ϖ` acts invertibly if and only if `1 - ϖ • s` is an isomorphism of `∏ₖ M`. -/
theorem rightOrthogonal_smulInvertible_singleFunctor_obj_iff (ϖ : R) (M : C) :
    (smulInvertible (DerivedCategory C) ϖ).rightOrthogonal ((singleFunctor C 0).obj M) ↔
      IsIso (𝟙 _ - ϖ • fanShift (productIsProduct fun _ : ℕ ↦ M)) := by
  rw [rightOrthogonal_smulInvertible_iff]
  have e : (homologyFunctor C 0).obj ((singleFunctor C 0).obj M) ≅ M :=
    (singleFunctorCompHomologyFunctorIso C 0).app M
  refine ⟨fun h ↦ (isIso_one_sub_smul_fanShift_iff_of_iso e _ _ ϖ).1 (h 0), fun h n ↦ ?_⟩
  by_cases hn : n = 0
  · subst hn
    exact (isIso_one_sub_smul_fanShift_iff_of_iso e _ _ ϖ).2 h
  · refine isIso_one_sub_smul_fanShift_of_isZero ?_ _ ϖ
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact isZero_of_isGE _ 0 n hn
    · exact isZero_of_isLE _ 0 n hn

/-- **Derived completeness is detected on homology objects.** An object `K` of `D(C)` receives
no nonzero morphism from an object on which `ϖ` acts invertibly if and only if each of its
homology objects, placed in degree `0`, has this property. -/
theorem rightOrthogonal_smulInvertible_iff_singleFunctor (ϖ : R) (K : DerivedCategory C) :
    (smulInvertible (DerivedCategory C) ϖ).rightOrthogonal K ↔
      ∀ n : ℤ, (smulInvertible (DerivedCategory C) ϖ).rightOrthogonal
        ((singleFunctor C 0).obj ((homologyFunctor C n).obj K)) := by
  rw [rightOrthogonal_smulInvertible_iff]
  exact forall_congr' fun n ↦ (rightOrthogonal_smulInvertible_singleFunctor_obj_iff ϖ _).symm

/-- If each homology object of `L` is zero or isomorphic to the homology object of `K` in the
same degree, and `K` receives no nonzero morphism from an object on which `ϖ` acts invertibly,
then neither does `L`. -/
lemma rightOrthogonal_smulInvertible_of_homology (ϖ : R) {K L : DerivedCategory C}
    (h : ∀ n : ℤ, IsZero ((homologyFunctor C n).obj L) ∨
      Nonempty ((homologyFunctor C n).obj L ≅ (homologyFunctor C n).obj K))
    (hK : (smulInvertible (DerivedCategory C) ϖ).rightOrthogonal K) :
    (smulInvertible (DerivedCategory C) ϖ).rightOrthogonal L := by
  rw [rightOrthogonal_smulInvertible_iff] at hK ⊢
  intro n
  rcases h n with h | ⟨⟨e⟩⟩
  · exact isIso_one_sub_smul_fanShift_of_isZero h _ ϖ
  · exact (isIso_one_sub_smul_fanShift_iff_of_iso e.symm _ _ ϖ).1 (hK n)

/-- The truncation `τ_{<a} K` of an object receiving no nonzero morphism from an object on which
`ϖ` acts invertibly has the same property. -/
lemma rightOrthogonal_smulInvertible_truncLT_obj (ϖ : R) {K : DerivedCategory C}
    (hK : (smulInvertible (DerivedCategory C) ϖ).rightOrthogonal K) (a : ℤ) :
    (smulInvertible (DerivedCategory C) ϖ).rightOrthogonal ((TStructure.t.truncLT a).obj K) := by
  refine rightOrthogonal_smulInvertible_of_homology ϖ (fun n ↦ ?_) hK
  by_cases hn : n < a
  · have := isIso_homologyFunctor_map_truncLTι_app K a n hn
    exact Or.inr ⟨asIso ((homologyFunctor C n).map ((TStructure.t.truncLTι a).app K))⟩
  · exact Or.inl (isZero_of_isLE _ (a - 1) n (by lia))

/-- The truncation `τ_{≥a} K` of an object receiving no nonzero morphism from an object on which
`ϖ` acts invertibly has the same property. -/
lemma rightOrthogonal_smulInvertible_truncGE_obj (ϖ : R) {K : DerivedCategory C}
    (hK : (smulInvertible (DerivedCategory C) ϖ).rightOrthogonal K) (a : ℤ) :
    (smulInvertible (DerivedCategory C) ϖ).rightOrthogonal ((TStructure.t.truncGE a).obj K) := by
  refine rightOrthogonal_smulInvertible_of_homology ϖ (fun n ↦ ?_) hK
  by_cases hn : a ≤ n
  · have := isIso_homologyFunctor_map_truncGEπ_app K a n hn
    exact Or.inr ⟨(asIso ((homologyFunctor C n).map ((TStructure.t.truncGEπ a).app K))).symm⟩
  · exact Or.inl (isZero_of_isGE _ a n (by lia))

end DerivedCategory
