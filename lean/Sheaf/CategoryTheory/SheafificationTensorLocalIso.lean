/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.CategoryTheory.PresheafTensorInternalHom
public import Mathlib.CategoryTheory.Sites.Localization

/-!
# Tensoring preserves sheafification-isomorphisms

Source: the Weil conjectures blueprint, `sec-proetale-coefficients`,
`sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-local-iso.md` (blueprint:
det-def-sfb-sheaf-tensor-local-iso).
-/

@[expose] public section

universe uC vC uA vA w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonoidalClosed

namespace CategoryTheory

/--
Source: the Weil conjectures blueprint, `sec-proetale-coefficients`,
`sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-local-iso.md`, setup and clauses 1--3
(blueprint: det-def-sfb-sheaf-tensor-local-iso).
In the setting of the objectwise presheaf tensor, the sheafification-local
morphisms are characterized by both sheafification and the Hom universal
property. They are stable under tensoring on either side and under tensoring
pairs of such morphisms. Tensoring two sheafification units is again local,
and its sheafification is the displayed isomorphism.

Proof (from the blueprint proof file). For a morphism `g : P ⟶ Q`, the
sheafification adjunction identifies precomposition by `g` on maps to a sheaf
with precomposition by its sheafification. This proves the Hom characterization
and its converse by testing against the two sheafifications. The tensor--
internal-hom adjunction from `det-def-sfb-sheaf-tensor-presheaf`, together with
that the internal hom into a sheaf is a sheaf, proves stability under left
tensoring; the presheaf symmetry proves right tensoring. Functoriality and
composition then prove stability for a tensor of two local morphisms. Finally,
the sheafification universal property puts each unit in the local class, so
clause 2 applied to the two units gives the final comparison and its
sheafification isomorphism.
-/
theorem sheafification_tensor_local_iso
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    (J : GrothendieckTopology C)
    {A : Type uA} [Category.{vA} A] [Abelian A]
    [IsGrothendieckAbelian.{w} A] [MonoidalCategory A]
    [SymmetricCategory A] [MonoidalClosed A] [MonoidalPreadditive A]
    [HasWeakSheafify J A] :
    (∀ {F G : Cᵒᵖ ⥤ A} (g : F ⟶ G),
        J.W (A := A) g ↔
          (IsIso ((presheafToSheaf J A).map g) ∧
            ∀ (H : Sheaf J A),
              Function.Bijective
                (fun h : G ⟶ (sheafToPresheaf J A).obj H => g ≫ h))) ∧
      (∀ {F F' : Cᵒᵖ ⥤ A} (g : F ⟶ F') (F₀ : Cᵒᵖ ⥤ A),
        J.W (A := A) g →
          J.W (A := A) (MonoidalCategoryStruct.tensorHom (𝟙 F₀) g) ∧
            J.W (A := A) (MonoidalCategoryStruct.tensorHom g (𝟙 F₀))) ∧
      (∀ {F F' G G' : Cᵒᵖ ⥤ A} (g : F ⟶ F') (h : G ⟶ G'),
        J.W (A := A) g → J.W (A := A) h →
          J.W (A := A) (MonoidalCategoryStruct.tensorHom g h)) ∧
      (∀ (F G : Cᵒᵖ ⥤ A),
        J.W (A := A)
            (MonoidalCategoryStruct.tensorHom (toSheafify J F) (toSheafify J G)) ∧
          IsIso
            ((presheafToSheaf J A).map
              (MonoidalCategoryStruct.tensorHom (toSheafify J F) (toSheafify J G)))) := by
  let e := presheaf_enrichedHoms_exist (C := C) (A := A)
  let : ∀ (F G : Cᵒᵖ ⥤ A), Enriched.FunctorCategory.HasEnrichedHom A F G := e.1
  let : ∀ (F G : Cᵒᵖ ⥤ A), Enriched.FunctorCategory.HasFunctorEnrichedHom A F G := e.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F G g
    constructor
    · intro hg
      exact ⟨(J.W_iff g).1 hg, fun H ↦ hg H.obj H.property⟩
    · intro hg
      exact (J.W_iff g).2 hg.1
  · intro F F' g F₀ hg
    constructor
    · simpa only [MonoidalCategory.id_tensorHom] using hg.whiskerLeft F₀
    · simpa only [MonoidalCategory.tensorHom_id] using hg.whiskerRight F₀
  · intro F F' G G' g h hg hh
    exact J.W.tensorHom_mem g h hg hh
  · intro F G
    have h := J.W.tensorHom_mem (toSheafify J F) (toSheafify J G)
      (J.W_toSheafify F) (J.W_toSheafify G)
    exact ⟨h, (J.W_iff _).1 h⟩

end CategoryTheory
