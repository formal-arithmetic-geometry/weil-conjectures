/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.KunnethMap

/-!

# Projection morphisms of composite adjunctions

Let `R' ⊣ R` and `S' ⊣ S` be adjunctions with oplax monoidal left adjoints, and `Q' ⊣ Q` an
adjunction with `Q' ≅ S' ⋙ R'` compatibly with the oplax monoidal structures. Under the
identification `S R ≅ Q` of right adjoints, the projection morphism of `Q' ⊣ Q` at `(A, B)` is
the projection morphism of `S' ⊣ S` at `(R A, B)` followed by `S` applied to the projection
morphism of `R' ⊣ R` at `(A, S' B)` (`CategoryTheory.Adjunction.whiskerRight_projectionMorphism`).
In particular it is an isomorphism if these two are
(`CategoryTheory.Adjunction.isIso_projectionMorphism_of_comp`).

We also record that the invertibility of the projection morphism only depends on its first
argument up to isomorphism, and that it is equivalent to the invertibility of the left projection
morphism for left adjoints compatible with the braidings.

## Main statements

- `CategoryTheory.Adjunction.whiskerRight_projectionMorphism`: the projection morphism of a
  composite.
- `CategoryTheory.Adjunction.isIso_projectionMorphism_of_comp`: the projection morphism of a
  composite is an isomorphism if those of the factors are.

-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory MonoidalCategory Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

section Single

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

/-- The invertibility of the projection morphism `G A ⊗ B ⟶ G (A ⊗ F B)` only depends on `A` up
to isomorphism, by the naturality square (`projectionMorphism_natural_left`)
```
G A ⊗ B ──projection morphism──▶ G (A ⊗ F B)
   │ G φ ▷ B                        │ G (φ ▷ F B)
   ▼                                ▼
G A' ⊗ B ─projection morphism──▶ G (A' ⊗ F B)
```
whose vertical arrows are isomorphisms. -/
lemma isIso_projectionMorphism_iff_of_iso {A A' : C} (φ : A ≅ A') (B : D) :
    IsIso (adj.projectionMorphism A B) ↔ IsIso (adj.projectionMorphism A' B) := by
  have h := adj.projectionMorphism_natural_left φ.hom B
  constructor
  · intro
    rw [← isIso_comp_left_iff (G.map φ.hom ▷ B), h]
    infer_instance
  · intro
    rw [← isIso_comp_right_iff _ (G.map (φ.hom ▷ F.obj B)), ← h]
    infer_instance

variable [BraidedCategory C] [BraidedCategory D]

end Single

section Composite

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃]
  {R' : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} (adjR : R' ⊣ R)
  {S' : C₃ ⥤ C₂} {S : C₂ ⥤ C₃} (adjS : S' ⊣ S)
  {Q' : C₃ ⥤ C₁} {Q : C₁ ⥤ C₃} (adjQ : Q' ⊣ Q)
  [MonoidalCategory C₁] [MonoidalCategory C₂] [MonoidalCategory C₃] [R'.OplaxMonoidal]
  [S'.OplaxMonoidal] [Q'.OplaxMonoidal]

end Composite

end CategoryTheory.Adjunction
