/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# Composition of relative tensor actions

Source: Stacks Project, `sites-cohomology.tex`, Tags 0B56
(`equation-projection-formula-map`) and 0GL1 (`lemma-j-shriek-and-tensor`), and the
abstract composition calculation in the DAG
(blueprint: lem-pur-composite-relative-tensor-action).
The ambient monoidal conventions are Stacks Tags 0FFK and 0FFL.

## Main declarations

- `CategoryTheory.compositeRelativeTensorAction`: the specified composite map `τ`.
- `CategoryTheory.composite_relative_tensor_action`: its naturality, action identity,
  and explicit two-step factorization.
-/

@[expose] public section

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory

open MonoidalCategory

/-- The composite `τ = π ≫ R.map δ` for relative right tensor actions.
This is the actual composite, without any invertibility or adjunction assumption.
Source: the abstract proper/open composition calculation motivated by Stacks Tags
0B56 and 0GL1 (blueprint: lem-pur-composite-relative-tensor-action). -/
def compositeRelativeTensorAction
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (P : E ⥤ D) (Q : D ⥤ C) (J : C ⥤ D) (R : D ⥤ E)
    (π : ∀ (A : D) (N : E), R.obj A ⊗ N ⟶ R.obj (A ⊗ P.obj N))
    (δ : ∀ (M : C) (B : D), J.obj M ⊗ B ⟶ J.obj (M ⊗ Q.obj B))
    (M : C) (N : E) :
    R.obj (J.obj M) ⊗ N ⟶ R.obj (J.obj (M ⊗ Q.obj (P.obj N))) :=
  π (J.obj M) N ≫ R.map (δ M (P.obj N))

/-- Composition preserves relative right tensor-action identities, including the
explicit factorization through `π` at `JM ⊗ PN`. The inverse comparison of `QP` is
`Q.map (p.μIso N T).inv ≫ (q.μIso (P.obj N) (P.obj T)).inv`.
Source: the abstract composition calculation motivated by Stacks Tags 0B56 and 0GL1,
using the monoidal conventions of Tags 0FFK and 0FFL
(blueprint: lem-pur-composite-relative-tensor-action).

Proof plan (the seven DAG steps):
1. Apply naturality of `δ` at `(a, P.map b)` inside `R`, then naturality of `π`
   at `(J.map a, b)`, to obtain joint naturality of the composite.
2. Put `A = JM`, `X = PN`, `Y = PT`, `V = P(N ⊗ T)`, and
   `u = (p.μIso N T).inv`. Define `b_A` by whiskering `u` and then applying the
   inverse associator. Define `c` similarly with the inverse comparison of `Q`.
   The composite `b_M = (1 ⊗ Q(u)) ≫ c` uses exactly the stated comparison of `QP`.
3. Expand both composite actions. Naturality of `π` in its first argument along
   `δ M X` gives the explicit factorization, using tensor bifunctoriality and
   the composition law of `R`.
4. Substitute the action equation for `π` at `(A, N, T)` into that factorization.
5. Substitute the action equation for `δ` at `(M, X, Y)`, then cancel the adjacent
   associator and inverse associator in its composition with `b_A`.
6. Naturality of `δ` in its second argument along `u` identifies the remaining
   inner composite with `δ M V ≫ J.map b_M`.
7. Apply functoriality of `R` and expand `b_M` as in step 2. This gives precisely
   the composite action identity. These steps use only the monoidal-category and
   strong-monoidal-functor definitions; no unit equation for `π` or `δ` is used. -/
theorem composite_relative_tensor_action
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (P : E ⥤ D) (Q : D ⥤ C) (p : P.CoreMonoidal) (q : Q.CoreMonoidal)
    (J : C ⥤ D) (R : D ⥤ E)
    (π : ∀ (A : D) (N : E), R.obj A ⊗ N ⟶ R.obj (A ⊗ P.obj N))
    (δ : ∀ (M : C) (B : D), J.obj M ⊗ B ⟶ J.obj (M ⊗ Q.obj B))
    (hπ : ∀ (A A' : D) (N N' : E) (a : A ⟶ A') (b : N ⟶ N'),
      (R.map a ⊗ₘ b) ≫ π A' N' = π A N ≫ R.map (a ⊗ₘ P.map b))
    (hδ : ∀ (M M' : C) (B B' : D) (a : M ⟶ M') (b : B ⟶ B'),
      (J.map a ⊗ₘ b) ≫ δ M' B' = δ M B ≫ J.map (a ⊗ₘ Q.map b))
    (hπ_action : ∀ (A : D) (N T : E),
      (α_ (R.obj A) N T).hom ≫ π A (N ⊗ T) ≫
          R.map ((𝟙 A ⊗ₘ (p.μIso N T).inv) ≫ (α_ A (P.obj N) (P.obj T)).inv) =
        (π A N ⊗ₘ 𝟙 T) ≫ π (A ⊗ P.obj N) T)
    (hδ_action : ∀ (M : C) (B B' : D),
      (α_ (J.obj M) B B').hom ≫ δ M (B ⊗ B') ≫
          J.map ((𝟙 M ⊗ₘ (q.μIso B B').inv) ≫ (α_ M (Q.obj B) (Q.obj B')).inv) =
        (δ M B ⊗ₘ 𝟙 B') ≫ δ (M ⊗ Q.obj B) B') :
    (∀ (M M' : C) (N N' : E) (a : M ⟶ M') (b : N ⟶ N'),
      (R.map (J.map a) ⊗ₘ b) ≫ compositeRelativeTensorAction P Q J R π δ M' N' =
        compositeRelativeTensorAction P Q J R π δ M N ≫
          R.map (J.map (a ⊗ₘ Q.map (P.map b)))) ∧
    (∀ (M : C) (N T : E),
      (α_ (R.obj (J.obj M)) N T).hom ≫
          compositeRelativeTensorAction P Q J R π δ M (N ⊗ T) ≫
          R.map (J.map
            ((𝟙 M ⊗ₘ (Q.map (p.μIso N T).inv ≫
                (q.μIso (P.obj N) (P.obj T)).inv)) ≫
              (α_ M (Q.obj (P.obj N)) (Q.obj (P.obj T))).inv)) =
        (compositeRelativeTensorAction P Q J R π δ M N ⊗ₘ 𝟙 T) ≫
          compositeRelativeTensorAction P Q J R π δ (M ⊗ Q.obj (P.obj N)) T) ∧
    (∀ (M : C) (N₁ N₂ : E),
      (compositeRelativeTensorAction P Q J R π δ M N₁ ⊗ₘ 𝟙 N₂) ≫
          compositeRelativeTensorAction P Q J R π δ (M ⊗ Q.obj (P.obj N₁)) N₂ =
        (π (J.obj M) N₁ ⊗ₘ 𝟙 N₂) ≫ π (J.obj M ⊗ P.obj N₁) N₂ ≫
          R.map ((δ M (P.obj N₁) ⊗ₘ 𝟙 (P.obj N₂)) ≫
            δ (M ⊗ Q.obj (P.obj N₁)) (P.obj N₂))) := by
  have factor (M : C) (N T : E) :
      (compositeRelativeTensorAction P Q J R π δ M N ⊗ₘ 𝟙 T) ≫
          compositeRelativeTensorAction P Q J R π δ (M ⊗ Q.obj (P.obj N)) T =
        (π (J.obj M) N ⊗ₘ 𝟙 T) ≫ π (J.obj M ⊗ P.obj N) T ≫
          R.map ((δ M (P.obj N) ⊗ₘ 𝟙 (P.obj T)) ≫
            δ (M ⊗ Q.obj (P.obj N)) (P.obj T)) := by
    have hn := hπ _ _ T T (δ M (P.obj N)) (𝟙 T)
    simp only [P.map_id] at hn
    simp only [compositeRelativeTensorAction, tensorHom_id, comp_whiskerRight,
      Functor.map_comp, Category.assoc]
    simpa only [tensorHom_id, Category.assoc] using
      congrArg (fun f ↦ (π (J.obj M) N ⊗ₘ 𝟙 T) ≫ f ≫
        R.map (δ (M ⊗ Q.obj (P.obj N)) (P.obj T))) hn
  refine ⟨?_, ?_, factor⟩
  · intro M M' N N' a b
    dsimp only [compositeRelativeTensorAction]
    rw [← Category.assoc, hπ, Category.assoc, ← R.map_comp, hδ, R.map_comp]
    simp only [Category.assoc]
  · intro M N T
    rw [factor]
    let X := P.obj N
    let Y := P.obj T
    let V := P.obj (N ⊗ T)
    let u : V ⟶ X ⊗ Y := (p.μIso N T).inv
    let c : M ⊗ Q.obj (X ⊗ Y) ⟶ (M ⊗ Q.obj X) ⊗ Q.obj Y :=
      (𝟙 M ⊗ₘ (q.μIso X Y).inv) ≫ (α_ M (Q.obj X) (Q.obj Y)).inv
    have hd : δ M (X ⊗ Y) ≫ J.map c =
        (α_ (J.obj M) X Y).inv ≫
          (δ M X ⊗ₘ 𝟙 Y) ≫ δ (M ⊗ Q.obj X) Y := by
      rw [← hδ_action]
      simp only [Iso.inv_hom_id_assoc]
      rfl
    have hn := hδ M M V (X ⊗ Y) (𝟙 M) u
    simp only [J.map_id] at hn
    have inner : δ M V ≫ J.map
        ((𝟙 M ⊗ₘ (Q.map u ≫ (q.μIso X Y).inv)) ≫
          (α_ M (Q.obj X) (Q.obj Y)).inv) =
        ((𝟙 (J.obj M) ⊗ₘ u) ≫ (α_ (J.obj M) X Y).inv) ≫
          (δ M X ⊗ₘ 𝟙 Y) ≫ δ (M ⊗ Q.obj X) Y := by
      have split :
          ((𝟙 M ⊗ₘ (Q.map u ≫ (q.μIso X Y).inv)) ≫
            (α_ M (Q.obj X) (Q.obj Y)).inv) = (𝟙 M ⊗ₘ Q.map u) ≫ c := by
        simp only [c, id_tensorHom, whiskerLeft_comp, Category.assoc]
      rw [split, J.map_comp, ← Category.assoc, ← hn, Category.assoc, hd]
      simp only [Category.assoc]
    rw [← Category.assoc (π (J.obj M) N ⊗ₘ 𝟙 T), ← hπ_action]
    simp only [compositeRelativeTensorAction, Category.assoc, ← R.map_comp]
    simpa only [Category.assoc] using
      congrArg (fun f ↦ (α_ (R.obj (J.obj M)) N T).hom ≫
        π (J.obj M) (N ⊗ T) ≫ R.map f) inner

end CategoryTheory
