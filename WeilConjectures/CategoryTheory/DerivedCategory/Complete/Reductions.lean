/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Objects whose reductions lie in a triangulated subcategory, uniformly bounded

Let `(C, J)` be an essentially small site, `R` a commutative ring, `I` an ideal of `R` and `P` a
triangulated subcategory of `D(J, R)`. This file defines the property of an object `K` of
`D(J, R)` that all its reductions `K ⊗ᴸ R/Iⁿ` lie in `P` and have homology concentrated in one
common interval `[a, b]` (`DerivedCategory.reductionsIn`), and shows that it is again a
triangulated subcategory (`DerivedCategory.isTriangulated_reductionsIn`): the reduction functors
`- ⊗ᴸ R/Iⁿ` are triangulated.

For the pro-étale site and `P` the bounded constructible complexes (those of étale origin), this
is the condition on the reduction tower in the definition of `D^b_c(T_proét, 𝒪_E)`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Opposite Pretriangulated ZeroObject

namespace DerivedCategory

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]

attribute [-instance] commShift₂CurriedTensor commShiftTensorLeft commShiftTensorRight
  isTriangulated_tensorLeft isTriangulated_tensorRight monoidalPreadditive monoidalLinear

noncomputable local instance (priority := high) :
    MonoidalCategory (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalCategory

noncomputable local instance (priority := high) :
    MonoidalPreadditive (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  (sheafTensorStructure J R).monoidalPreadditive

noncomputable local instance (priority := high) :
    (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).CommShift₂Int :=
  (sheafTensorStructure J R).commShift₂

noncomputable local instance (priority := high)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :
    ((curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj K).IsTriangulated :=
  (sheafTensorStructure J R).isTriangulated_tensorRight K

variable (I : Ideal R) (P : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))))

/-- The objects `K` of `D(J, R)` all of whose reductions `K ⊗ᴸ R/Iⁿ` lie in `P` and have
homology concentrated in one common interval `[a, b]`. -/
def reductionsIn : ObjectProperty (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  fun K ↦ ∃ a b : ℤ, ∀ n : ℕ, P ((derivedCompletionDiagram J I K).obj (op n)) ∧
    homologyConcentratedIn a b ((derivedCompletionDiagram J I K).obj (op n))

/-- The reduction functor `- ⊗ᴸ R/Iⁿ`. -/
noncomputable abbrev reductionFunctor (n : ℕ) :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  (curriedTensor (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))).flip.obj
    ((quotPowFunctor J I).obj (op n))

lemma derivedCompletionDiagram_obj (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)))
    (n : ℕ) : (derivedCompletionDiagram J I K).obj (op n) = (reductionFunctor J I n).obj K :=
  rfl

variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]

/-- If `P` is a triangulated subcategory, so are the objects whose reductions lie in `P`,
with homology in a common interval. -/
instance isTriangulated_reductionsIn : (reductionsIn J I P).IsTriangulated := by
  have hiso : (reductionsIn J I P).IsClosedUnderIsomorphisms := ⟨fun {K K'} e ⟨a, b, h⟩ ↦
    ⟨a, b, fun n ↦ by
      let e' := (reductionFunctor J I n).mapIso e
      have : TStructure.t.IsGE ((reductionFunctor J I n).obj K) a := (h n).2.1
      have : TStructure.t.IsLE ((reductionFunctor J I n).obj K) b := (h n).2.2
      exact ⟨P.prop_of_iso e' (h n).1, ⟨TStructure.t.isGE_of_iso e' a,
        TStructure.t.isLE_of_iso e' b⟩⟩⟩⟩
  have hshift : (reductionsIn J I P).IsStableUnderShift ℤ := ⟨fun k ↦ ⟨fun K ⟨a, b, h⟩ ↦
    ⟨a - k, b - k, fun n ↦ by
      let e := ((reductionFunctor J I n).commShiftIso k).app K
      have : TStructure.t.IsGE ((reductionFunctor J I n).obj K) a := (h n).2.1
      have : TStructure.t.IsLE ((reductionFunctor J I n).obj K) b := (h n).2.2
      have : TStructure.t.IsGE ((reductionFunctor J I n ⋙ shiftFunctor _ k).obj K) (a - k) :=
        TStructure.t.isGE_shift _ a k (a - k) (by lia)
      have : TStructure.t.IsLE ((reductionFunctor J I n ⋙ shiftFunctor _ k).obj K) (b - k) :=
        TStructure.t.isLE_shift _ b k (b - k) (by lia)
      exact ⟨P.prop_of_iso e.symm (P.le_shift k _ (h n).1),
        ⟨TStructure.t.isGE_of_iso e.symm (a - k), TStructure.t.isLE_of_iso e.symm (b - k)⟩⟩⟩⟩⟩
  have hext : (reductionsIn J I P).IsTriangulatedClosed₂ :=
    ObjectProperty.IsTriangulatedClosed₂.mk' fun T hT ⟨a₁, b₁, h₁⟩ ⟨a₃, b₃, h₃⟩ ↦
      ⟨min a₁ a₃, max b₁ b₃, fun n ↦ by
        have hT' := (reductionFunctor J I n).map_distinguished T hT
        have : TStructure.t.IsGE ((reductionFunctor J I n).obj T.obj₁) a₁ := (h₁ n).2.1
        have : TStructure.t.IsGE ((reductionFunctor J I n).obj T.obj₃) a₃ := (h₃ n).2.1
        have : TStructure.t.IsLE ((reductionFunctor J I n).obj T.obj₁) b₁ := (h₁ n).2.2
        have : TStructure.t.IsLE ((reductionFunctor J I n).obj T.obj₃) b₃ := (h₃ n).2.2
        have g₁ : TStructure.t.IsGE ((reductionFunctor J I n).obj T.obj₁) (min a₁ a₃) :=
          TStructure.t.isGE_of_ge _ _ a₁ (min_le_left _ _)
        have g₃ : TStructure.t.IsGE ((reductionFunctor J I n).obj T.obj₃) (min a₁ a₃) :=
          TStructure.t.isGE_of_ge _ _ a₃ (min_le_right _ _)
        have l₁ : TStructure.t.IsLE ((reductionFunctor J I n).obj T.obj₁) (max b₁ b₃) :=
          TStructure.t.isLE_of_le _ b₁ _ (le_max_left _ _)
        have l₃ : TStructure.t.IsLE ((reductionFunctor J I n).obj T.obj₃) (max b₁ b₃) :=
          TStructure.t.isLE_of_le _ b₃ _ (le_max_right _ _)
        exact ⟨P.ext_of_isTriangulatedClosed₂ _ hT' (h₁ n).1 (h₃ n).1,
          TStructure.t.isGE₂ _ hT' _ g₁ g₃, TStructure.t.isLE₂ _ hT' _ l₁ l₃⟩⟩
  exact { exists_zero := ⟨0, isZero_zero _, 0, 0, fun n ↦ by
    have hz : IsZero ((reductionFunctor J I n).obj 0) := (reductionFunctor J I n).map_isZero
      (isZero_zero _)
    exact ⟨P.prop_of_isZero hz, TStructure.t.isGE_of_isZero hz 0,
      TStructure.t.isLE_of_isZero hz 0⟩⟩ }

end DerivedCategory
