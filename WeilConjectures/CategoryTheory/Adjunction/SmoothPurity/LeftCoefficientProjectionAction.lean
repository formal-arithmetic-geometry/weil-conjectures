/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor

/-!
# Left-coefficient counit projection and its action laws

The right-coefficient map is the existing `Adjunction.rightAdjointProjectionMap`.
The left-coefficient map is its symmetry conjugate, without an invertibility assumption.

## References

* Stacks Project, Tags 0B56, 0037, 0FFK and 0FFL.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

open MonoidalCategory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [SymmetricCategory D]
  {F : C ⥤ D} {R : D ⥤ C} [F.Braided]

/-- The left-coefficient map `B ⊗ R N ⟶ R (F B ⊗ N)` is the symmetry conjugate of the
right-coefficient counit adjunct: first swap `B` and `R N`, apply the existing right projection,
then apply `R` to the swap of `N` and `F B`.

Stacks Project, Tag 0B56. -/
noncomputable def leftCoefficientProjectionMap (adj : F ⊣ R) (B : C) (N : D) :
    B ⊗ R.obj N ⟶ R.obj (F.obj B ⊗ N) :=
  (β_ B (R.obj N)).hom ≫
    ((adj.rightAdjointProjectionMap (Functor.OplaxMonoidal.δNatTrans F)).app N).app B ≫
    R.map (β_ N (F.obj B)).hom

/-- The symmetry-conjugated left projection is natural, its transpose is the inverse tensorator
followed by the counit in the second factor, and it obeys the left coefficient unit and
associativity constraints. Stacks Project, Tag 0B56. -/
theorem leftCoefficientProjectionMap_coherence (adj : F ⊣ R) :
    (∀ (B B' : C) (N N' : D) (f : B ⟶ B') (g : N ⟶ N'),
      leftCoefficientProjectionMap adj B N ≫ R.map (F.map f ⊗ₘ g) =
        (f ⊗ₘ R.map g) ≫ leftCoefficientProjectionMap adj B' N') ∧
    (∀ (B : C) (N : D),
      F.map (leftCoefficientProjectionMap adj B N) ≫ adj.counit.app (F.obj B ⊗ N) =
        Functor.OplaxMonoidal.δ F B (R.obj N) ≫ (𝟙 (F.obj B) ⊗ₘ adj.counit.app N)) ∧
    (∀ (N : D),
      leftCoefficientProjectionMap adj (𝟙_ C) N ≫
        R.map ((Functor.OplaxMonoidal.η F ⊗ₘ 𝟙 N) ≫ (λ_ N).hom) =
          (λ_ (R.obj N)).hom) ∧
    (∀ (B B' : C) (N : D),
      leftCoefficientProjectionMap adj (B ⊗ B') N ≫
        R.map ((Functor.OplaxMonoidal.δ F B B' ⊗ₘ 𝟙 N) ≫
          (α_ (F.obj B) (F.obj B') N).hom) =
        (α_ B B' (R.obj N)).hom ≫
          (𝟙 B ⊗ₘ leftCoefficientProjectionMap adj B' N) ≫
          leftCoefficientProjectionMap adj B (F.obj B' ⊗ N)) := by
  have transpose (B : C) (N : D) :
      F.map (leftCoefficientProjectionMap adj B N) ≫ adj.counit.app _ =
        Functor.OplaxMonoidal.δ F B (R.obj N) ≫
          (𝟙 (F.obj B) ⊗ₘ adj.counit.app N) := by
    unfold leftCoefficientProjectionMap
    simp only [Functor.map_comp, Category.assoc]
    erw [adj.counit_naturality]
    rw [adj.map_rightAdjointProjectionMap_app_app_comp_counit_assoc]
    change F.map (β_ B (R.obj N)).hom ≫
      Functor.OplaxMonoidal.δ F (R.obj N) B ≫
        adj.counit.app N ▷ F.obj B ≫ (β_ N (F.obj B)).hom = _
    rw [← tensorHom_id]
    erw [BraidedCategory.braiding_naturality]
    simp only [Functor.map_braiding, Category.assoc, Functor.Monoidal.μ_δ_assoc,
      Functor.comp_obj, SymmetricCategory.symmetry_assoc]
  refine ⟨?_, transpose, ?_, ?_⟩
  · intro B B' N N' f g
    apply (adj.homEquiv _ _).symm.injective
    rw [homEquiv_naturality_right_symm, homEquiv_naturality_left_symm]
    simp only [homEquiv_counit, transpose]
    rw [← Functor.OplaxMonoidal.δ_natural_assoc]
    simp only [Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    congr 2
    exact (adj.counit.naturality g).symm
  · intro N
    apply (adj.homEquiv _ _).symm.injective
    rw [homEquiv_naturality_right_symm]
    simp only [homEquiv_counit, transpose, Category.assoc]
    rw [tensorHom_comp_tensorHom_assoc]
    simp only [Category.id_comp]
    rw [Functor.OplaxMonoidal.δ_comp_η_tensorHom_assoc]
    simp only [leftUnitor_naturality, Iso.inv_hom_id_assoc]
    erw [Category.comp_id]
  · intro B B' N
    apply (adj.homEquiv _ _).symm.injective
    rw [homEquiv_naturality_right_symm, homEquiv_naturality_left_symm,
      homEquiv_naturality_left_symm]
    simp only [homEquiv_counit, transpose, Category.assoc]
    rw [← Functor.OplaxMonoidal.δ_natural_assoc]
    simp only [Functor.map_id, tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom,
      Category.id_comp, Category.comp_id]
    rw [transpose]
    erw [Category.comp_id]
    simp only [tensorHom_def, id_whiskerRight, Category.id_comp,
      MonoidalCategory.whiskerLeft_comp, Category.assoc]
    rw [associator_naturality_right, Functor.OplaxMonoidal.associativity_assoc]

end CategoryTheory.Adjunction
