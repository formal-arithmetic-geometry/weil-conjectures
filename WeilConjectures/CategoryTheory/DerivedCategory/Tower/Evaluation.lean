/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.Injective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Evaluation of towers preserves K-injective complexes

Let `A` be an abelian category. The left adjoint `Lₙ = evaluationLeftAdjoint A (op n)` of the
evaluation functor `evₙ : (ℕᵒᵖ ⥤ A) ⥤ A` sends `X` to the tower whose level `m` is the coproduct
of copies of `X` indexed by the subsingleton `op n ⟶ op m`, i.e. `X` or `0`. It is therefore
exact (`CategoryTheory.preservesFiniteLimits_evaluationLeftAdjoint`), and its right adjoint
`evₙ` preserves K-injective complexes
(`CategoryTheory.preservesKInjectiveComplexes_evaluation`): the levels of a K-injective complex
of towers are K-injective complexes.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

variable {A : Type*} [Category A] [Abelian A]

/-- The left adjoint of the evaluation `evₙ : (ℕᵒᵖ ⥤ A) ⥤ A` of towers preserves finite limits:
each of its levels is either the identity (up to the coproduct over a one-element set) or zero. -/
instance preservesFiniteLimits_evaluationLeftAdjoint (c : ℕᵒᵖ) :
    PreservesFiniteLimits (evaluationLeftAdjoint A c) := by
  refine preservesFiniteLimits_of_evaluation _ fun m ↦ ?_
  by_cases hm : Nonempty (c ⟶ m)
  · obtain ⟨g₀⟩ := hm
    letI : Unique (c ⟶ m) := uniqueOfSubsingleton g₀
    let α : 𝟭 A ⟶ evaluationLeftAdjoint A c ⋙ (evaluation ℕᵒᵖ A).obj m :=
      { app X := Sigma.ι (fun _ : c ⟶ m ↦ X) g₀
        naturality X Y f := by
          change f ≫ _ = Sigma.ι (fun _ : c ⟶ m ↦ X) g₀ ≫ (Sigma.desc fun h ↦ f ≫ Sigma.ι (fun _ : c ⟶ m ↦ Y) h)
          erw [Sigma.ι_desc] }
    have (X : A) : IsIso (α.app X) := by
      change IsIso (Sigma.ι (fun _ : c ⟶ m ↦ X) g₀)
      rw [Subsingleton.elim g₀ default, ← coproductUniqueIso_inv]
      infer_instance
    have : IsIso α := NatIso.isIso_of_isIso_app α
    exact preservesFiniteLimits_of_natIso (asIso α)
  · have : IsEmpty (c ⟶ m) := not_nonempty_iff.mp hm
    have hZ (X : A) : IsZero ((evaluationLeftAdjoint A c ⋙ (evaluation ℕᵒᵖ A).obj m).obj X) :=
      (IsZero.iff_id_eq_zero _).mpr (Sigma.hom_ext _ _ fun g ↦ isEmptyElim g)
    exact ⟨fun _ _ _ ↦ ⟨fun {_} ↦ ⟨fun {_} _ ↦
      ⟨IsLimit.ofIsZero _ (Functor.isZero _ fun _ ↦ hZ _) (hZ _)⟩⟩⟩⟩

instance (c : ℕᵒᵖ) : PreservesFiniteColimits (evaluationLeftAdjoint A c) :=
  have := (evaluationAdjunctionRight A c).leftAdjoint_preservesColimits
  inferInstance

instance (c : ℕᵒᵖ) : (evaluationLeftAdjoint A c).Additive :=
  (evaluationAdjunctionRight A c).left_adjoint_additive

/-- The evaluation of towers at a level preserves K-injective complexes, being right adjoint to
the exact functor `evaluationLeftAdjoint A c`. -/
instance preservesKInjectiveComplexes_evaluation (c : ℕᵒᵖ) :
    ((evaluation ℕᵒᵖ A).obj c).PreservesKInjectiveComplexes :=
  (evaluationAdjunctionRight A c).preservesKInjectiveComplexes

end CategoryTheory
