/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-!
# Injective towers have split surjective transition maps

Let `A` be a category with zero morphisms and finite coproducts. A *tower* in `A` is a functor
`E : ℕᵒᵖ ⥤ A`, with transition maps `Eₙ₊₁ ⟶ Eₙ`. The evaluation functor `E ↦ Eₙ` has a left
adjoint `Lₙ = evaluationLeftAdjoint A (op n)`, sending `X` to the tower which is `X` in levels
`≤ n` (with identity transitions) and `0` in levels `> n`. The canonical map
`Lₙ X ⟶ Lₙ₊₁ X` (`CategoryTheory.towerLeftAdjointSucc`) is a monomorphism, and maps out of it
into a tower `E` correspond to the transition `Eₙ₊₁ ⟶ Eₙ`. Hence if `E` is an injective object
of the category of towers, every transition map `Eₙ₊₁ ⟶ Eₙ` is a split epimorphism
(`CategoryTheory.isSplitEpi_map_of_injective`).

This is the input that makes the Roos sequence `0 ⟶ lim E ⟶ ∏ Eₙ ⟶ ∏ Eₙ ⟶ 0` exact on the
right for injective towers.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

variable {A : Type*} [Category A] [HasZeroMorphisms A] [HasFiniteCoproducts A]

instance (a b : ℕᵒᵖ) : Finite (a ⟶ b) := Finite.of_subsingleton

variable (A) in
/-- The canonical map `Lₙ X ⟶ Lₙ₊₁ X` between the values at `X` of the left adjoints of the
evaluation functors at `n` and `n + 1`: it corresponds under the adjunction `Lₙ ⊣ evₙ` to the
inclusion of `X` as the summand of `(Lₙ₊₁ X)ₙ` indexed by the transition `op (n + 1) ⟶ op n`. -/
noncomputable def towerLeftAdjointSucc (n : ℕ) (X : A) :
    (evaluationLeftAdjoint A (op n)).obj X ⟶ (evaluationLeftAdjoint A (op (n + 1))).obj X :=
  ((evaluationAdjunctionRight A (op n)).homEquiv _ _).symm
    (Sigma.ι (fun _ : op (n + 1) ⟶ op n ↦ X) (homOfLE n.le_succ).op)

omit [HasZeroMorphisms A] in
lemma evaluationAdjunctionRight_homEquiv_apply (c : ℕᵒᵖ) (X : A) (E : ℕᵒᵖ ⥤ A)
    (f : (evaluationLeftAdjoint A c).obj X ⟶ E) :
    (evaluationAdjunctionRight A c).homEquiv X E f = Sigma.ι (fun _ ↦ X) (𝟙 c) ≫ f.app c := by
  simp [evaluationAdjunctionRight]

omit [HasZeroMorphisms A] in
lemma towerLeftAdjointSucc_app (n : ℕ) (X : A) (m : ℕᵒᵖ) :
    (towerLeftAdjointSucc A n X).app m =
      Sigma.desc fun g ↦ Sigma.ι (fun _ ↦ X) ((homOfLE n.le_succ).op ≫ g) := by
  refine Sigma.hom_ext _ _ fun g ↦ ?_
  simp only [towerLeftAdjointSucc, evaluationAdjunctionRight]
  simp only [Adjunction.mkOfHomEquiv_homEquiv, Equiv.coe_fn_symm_mk]
  erw [Sigma.ι_desc, Sigma.ι_desc, Sigma.ι_desc]

instance mono_towerLeftAdjointSucc (n : ℕ) (X : A) : Mono (towerLeftAdjointSucc A n X) := by
  suffices ∀ m, Mono ((towerLeftAdjointSucc A n X).app m) from NatTrans.mono_of_mono_app _
  intro m
  rw [towerLeftAdjointSucc_app]
  by_cases hm : Nonempty (op n ⟶ m)
  · obtain ⟨g₀⟩ := hm
    exact SplitMono.mono
      ⟨Sigma.desc fun (_ : op (n + 1) ⟶ m) ↦ Sigma.ι (fun _ : op n ⟶ m ↦ X) g₀,
        Sigma.hom_ext _ _ fun g ↦ by
          erw [Sigma.ι_desc_assoc, Sigma.ι_desc, Subsingleton.elim g g₀]; exact (Category.comp_id _).symm⟩
  · have : IsEmpty (op n ⟶ m) := not_nonempty_iff.mp hm
    have hZ : IsZero (∐ fun _ : op n ⟶ m ↦ X) :=
      (IsZero.iff_id_eq_zero _).mpr (Sigma.hom_ext _ _ fun g ↦ isEmptyElim g)
    exact ⟨fun _ _ _ ↦ hZ.eq_of_tgt _ _⟩

/-- In an injective tower `E : ℕᵒᵖ ⥤ A`, every transition map `Eₙ₊₁ ⟶ Eₙ` is a split
epimorphism: the identity of `Eₙ`, viewed as a map `Lₙ Eₙ ⟶ E`, extends along the monomorphism
`towerLeftAdjointSucc A n Eₙ : Lₙ Eₙ ⟶ Lₙ₊₁ Eₙ`, and the extension corresponds to a section
`Eₙ ⟶ Eₙ₊₁` of the transition. -/
lemma isSplitEpi_map_of_injective (E : ℕᵒᵖ ⥤ A) [Injective E] (n : ℕ) :
    IsSplitEpi (E.map (homOfLE n.le_succ).op) := by
  let f := ((evaluationAdjunctionRight A (op n)).homEquiv _ _).symm (𝟙 (E.obj (op n)))
  let g := Injective.factorThru f (towerLeftAdjointSucc A n (E.obj (op n)))
  have hg : towerLeftAdjointSucc A n (E.obj (op n)) ≫ g = f := Injective.comp_factorThru _ _
  refine IsSplitEpi.mk' ⟨Sigma.ι (fun _ ↦ E.obj (op n)) (𝟙 (op (n + 1))) ≫ g.app _, ?_⟩
  have h := congr_arg (fun φ ↦ ((evaluationAdjunctionRight A (op n)).homEquiv _ _) φ) hg
  simp only [f, Equiv.apply_symm_apply, evaluationAdjunctionRight_homEquiv_apply,
    NatTrans.comp_app, towerLeftAdjointSucc_app] at h
  have hn := g.naturality (homOfLE n.le_succ).op
  rw [← h]
  simp only [Category.assoc]
  rw [← hn]
  erw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc]
  congr 2
  exact Subsingleton.elim _ _

end CategoryTheory
