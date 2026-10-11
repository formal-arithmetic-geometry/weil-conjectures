/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Principal

/-!
# The derived completion functor

Let `(C, J)` be an essentially small site, `R` a commutative ring and `ϖ ∈ R` a nonzerodivisor
generating the ideal `I`. The derived complete objects of `D(J, R)` form a reflective full
subcategory: the *derived completion* `K ↦ K^ = R lim_n (K ⊗ᴸ R/ϖⁿ)` is left adjoint to the
inclusion (Stacks, Tag 091V). The unit `K ⟶ K^` extends the reduction maps and its mapping
cone is an object on which `ϖ` acts invertibly, so that every morphism from `K` to a derived
complete object factors uniquely through `K^`.

## Main definitions

- `DerivedCategory.derivedCompletion`: the derived completion functor from `D(J, R)` to the
  full subcategory of derived complete objects.
- `DerivedCategory.derivedCompletionAdjunction`: the derived completion is left adjoint to the
  inclusion of derived complete objects.

## Main results

- `DerivedCategory.smulInvertible_of_derivedCompletionUnit`: `ϖ` acts invertibly on the mapping
  cone of the unit `K ⟶ K^`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Pretriangulated

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  {J : GrothendieckTopology C} {R : Type (u + 1)} [CommRing R]
  {I : Ideal R} {ϖ : R} (hϖ : ϖ ∈ nonZeroDivisors R) (hI : I = Ideal.span {ϖ})

/-- If `ϖ` acts invertibly on every mapping cone of `φ : K ⟶ F`, then precomposition with `φ` is
a bijection onto the morphisms `K ⟶ L`, for every `L` receiving no nonzero morphism from an
object on which `ϖ` acts invertibly. -/
lemma bijective_comp_of_smulInvertible_cone
    {K F L : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))}
    (φ : K ⟶ F) (hφ : ∀ ⦃X⦄ (g : F ⟶ X) (h : X ⟶ K⟦(1 : ℤ)⟧), Triangle.mk φ g h ∈ distTriang _ →
      smulInvertible J ϖ X)
    (hL : (smulInvertible J ϖ).rightOrthogonal L) :
    Function.Bijective fun f : F ⟶ L ↦ φ ≫ f := by
  obtain ⟨X, g, h, hT⟩ := distinguished_cocone_triangle φ
  have hX := hφ g h hT
  have hX' : smulInvertible J ϖ (X⟦(-1 : ℤ)⟧) := ObjectProperty.le_shift _ (-1) X hX
  constructor
  · intro f₁ f₂ hf
    rw [← sub_eq_zero]
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ _ hT (f₁ - f₂)
      (by simp only [Triangle.mk_mor₁, Preadditive.comp_sub]; exact sub_eq_zero.2 hf)
    rw [hk, hL k hX, comp_zero]
  · intro f
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hT) f (hL _ hX')
    exact ⟨k, hk.symm⟩

include hϖ hI

/-- Every object `K` maps to a derived complete object `F` by a morphism on whose mapping cones
`ϖ` acts invertibly. -/
lemma exists_derivedComplete_smulInvertible_cone
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ∃ (F : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) (φ : K ⟶ F),
      derivedComplete J I F ∧ (smulInvertible J ϖ).rightOrthogonal F ∧
      ∀ ⦃X⦄ (g : F ⟶ X) (h : X ⟶ K⟦(1 : ℤ)⟧), Triangle.mk φ g h ∈ distTriang _ →
        smulInvertible J ϖ X := by
  obtain ⟨F, φ, -, -, -, -, -, -, hF, hcone⟩ := exists_derivedCompletion hϖ hI K
  exact ⟨F, φ, derivedComplete_of_rightOrthogonal hϖ hI hF, hF, hcone⟩

/-- The derived completion of an object of `D(J, R)`, a derived complete object. -/
noncomputable def derivedCompletionObj (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    (derivedComplete J I).FullSubcategory :=
  ⟨(exists_derivedComplete_smulInvertible_cone hϖ hI K).choose,
    (exists_derivedComplete_smulInvertible_cone hϖ hI K).choose_spec.choose_spec.1⟩

/-- The completion map `K ⟶ K^`. -/
noncomputable def derivedCompletionMap (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    K ⟶ (derivedCompletionObj hϖ hI K).obj :=
  (exists_derivedComplete_smulInvertible_cone hϖ hI K).choose_spec.choose

/-- `ϖ` acts invertibly on the mapping cones of the completion map `K ⟶ K^`. -/
lemma smulInvertible_of_derivedCompletionMap
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) ⦃X⦄
    (g : (derivedCompletionObj hϖ hI K).obj ⟶ X) (h : X ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (derivedCompletionMap hϖ hI K) g h ∈ distTriang _) :
    smulInvertible J ϖ X :=
  (exists_derivedComplete_smulInvertible_cone hϖ hI K).choose_spec.choose_spec.2.2 g h hT

/-- Precomposition with the completion map `K ⟶ K^` is a bijection onto the morphisms from `K`
to a derived complete object. -/
noncomputable def derivedCompletionHomEquiv (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))
    (L : (derivedComplete J I).FullSubcategory) :
    (derivedCompletionObj hϖ hI K ⟶ L) ≃ (K ⟶ (derivedComplete J I).ι.obj L) :=
  InducedCategory.homEquiv.trans
    (Equiv.ofBijective _ (bijective_comp_of_smulInvertible_cone (derivedCompletionMap hϖ hI K)
      (smulInvertible_of_derivedCompletionMap hϖ hI K)
      ((derivedComplete_iff_rightOrthogonal hϖ hI L.obj).1 L.property)))

/-- The **derived completion** functor `K ↦ K^` from `D(J, R)` to its derived complete objects,
left adjoint to the inclusion. -/
noncomputable def derivedCompletion :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) ⥤ (derivedComplete J I).FullSubcategory :=
  Adjunction.leftAdjointOfEquiv (derivedCompletionHomEquiv hϖ hI) fun _ _ _ _ _ ↦ by
    simp [derivedCompletionHomEquiv, InducedCategory.homEquiv]

/-- The derived completion is left adjoint to the inclusion of the derived complete objects. -/
noncomputable def derivedCompletionAdjunction :
    derivedCompletion hϖ hI ⊣ (derivedComplete J I).ι :=
  Adjunction.adjunctionOfEquivLeft _ _

lemma derivedCompletionAdjunction_unit_app (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    (derivedCompletionAdjunction hϖ hI).unit.app K = derivedCompletionMap hϖ hI K := by
  simp [derivedCompletionAdjunction, derivedCompletion, derivedCompletionHomEquiv,
    InducedCategory.homEquiv]

end DerivedCategory
