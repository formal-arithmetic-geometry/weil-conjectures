/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Recovering the unit comparison from associative tensor comparisons

Source: factors proof (2), coefficient-unit identification; inverse-image context: Stacks 07A4.
(blueprint: lem-sp-associative-tensor-unit-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b c d
open CategoryTheory MonoidalCategory
namespace CategoryTheory

/-- An associative tensor comparison and preservation of the unit object determine
one unit isomorphism satisfying every right-unit equation.
Source: factors proof (2), coefficient-unit identification; elementary tensor-unit cancellation.
(blueprint: lem-sp-associative-tensor-unit-comparison).

Proof: tensoring by the image of the unit is fully faithful because that image
is isomorphic to the target unit. Pull back the composite of the inverse binary
comparison and the two right unitors to define epsilon. Its right-unit equation
at the source unit holds by construction. Associativity, naturality and the
triangle identity give all left-unit equations, then all right-unit equations.
For uniqueness use the right-unit equation at the unit, cancel its invertible
comparison and unitor, and apply faithfulness of tensoring by its image. -/
theorem tensorUnitFromAssociativity
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    (F : C ⥤ D) (μ : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (e : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (ha : ∀ A B M : C,
      F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
          F.obj A ◁ (μ.app (B, M)).hom =
        (μ.app (A ⊗ B, M)).hom ≫ (μ.app (A, B)).hom ▷ F.obj M ≫
          (α_ (F.obj A) (F.obj B) (F.obj M)).hom) :
    ∃! ε : F.obj (𝟙_ C) ≅ 𝟙_ D,
      ∀ M : C, F.map (ρ_ M).hom = (μ.app (M, 𝟙_ C)).hom ≫
        (𝟙 (F.obj M) ⊗ₘ ε.hom) ≫ (ρ_ (F.obj M)).hom := by
  obtain ⟨ε, _, hr⟩ := unit_from_tensor F μ e ha
  refine ⟨ε, fun M ↦ (hr M).symm, ?_⟩
  intro ε' hε'
  apply Iso.ext
  have h := (hε' (𝟙_ C)).symm.trans (hr (𝟙_ C)).symm
  dsimp only [Functor.comp_obj, Functor.prod_obj, tensor_obj] at h
  have hh : F.obj (𝟙_ C) ◁ ε'.hom = F.obj (𝟙_ C) ◁ ε.hom := by
    apply (cancel_epi (μ.app (𝟙_ C, 𝟙_ C)).hom).1
    apply (cancel_mono (ρ_ (F.obj (𝟙_ C))).hom).1
    simpa only [id_tensorHom, Category.assoc] using h
  let t : tensorLeft (F.obj (𝟙_ C)) ≅ 𝟭 D := NatIso.ofComponents
    (fun X ↦ whiskerRightIso e X ≪≫ λ_ X) (by
      intro X Y f
      change F.obj (𝟙_ C) ◁ f ≫ e.hom ▷ Y ≫ (λ_ Y).hom =
        (e.hom ▷ X ≫ (λ_ X).hom) ≫ f
      rw [whisker_exchange_assoc, leftUnitor_naturality]
      simp only [Category.assoc])
  have : (tensorLeft (F.obj (𝟙_ C))).Faithful := Functor.Faithful.of_iso t.symm
  exact (tensorLeft (F.obj (𝟙_ C))).map_injective hh

end CategoryTheory
