/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# The transition map of a composite of left adjoints

Let `adj₀₁ : F₀₁ ⊣ G₁₀`, `adj₁₂ : F₁₂ ⊣ G₂₁` and `adj₀₂ : F₀₂ ⊣ G₂₀` be adjunctions and
`φ : F₀₂ ≅ F₀₁ ⋙ F₁₂`. For `K : C₁` there is a transition map `G₁₀ K ⟶ G₂₀ (F₁₂ K)`: the unit
of `adj₀₂` at `G₁₀ K`, followed by `G₂₀` applied to `φ` and to `F₁₂` of the counit of `adj₀₁`
at `K`. It is `G₁₀` applied to the unit of `adj₁₂` at `K`, followed by the conjugate
`G₂₁ ⋙ G₁₀ ≅ G₂₀` of `φ`; in particular it is an isomorphism as soon as the unit of `adj₁₂`
is one at `K`, e.g. when `F₁₂` is fully faithful.

## Main results

- `CategoryTheory.Adjunction.unit_app_comp_map_comp_counit_eq`: the description of the
  transition map through the unit of `adj₁₂`.
- `CategoryTheory.Adjunction.isIso_unit_app_comp_map_comp_counit`: the transition map is an
  isomorphism if the unit of `adj₁₂` is an isomorphism at `K`.
-/

@[expose] public section

namespace CategoryTheory

variable {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]

open CategoryTheory.Functor

namespace Adjunction

variable {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}
  (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀)

/-- The transition map `G₁₀ K ⟶ G₂₀ (F₁₂ K)` attached to `φ : F₀₂ ≅ F₀₁ ⋙ F₁₂` is `G₁₀` of
the unit of `adj₁₂` at `K` followed by the conjugate `G₂₁ ⋙ G₁₀ ⟶ G₂₀` of `φ`. -/
lemma unit_app_comp_map_comp_counit_eq (φ : F₀₂ ⟶ F₀₁ ⋙ F₁₂) (K : C₁) :
    adj₀₂.unit.app (G₁₀.obj K) ≫ G₂₀.map (φ.app (G₁₀.obj K) ≫ F₁₂.map (adj₀₁.counit.app K)) =
      G₁₀.map (adj₁₂.unit.app K) ≫
        (conjugateEquiv (adj₀₁.comp adj₁₂) adj₀₂ φ).app (F₁₂.obj K) := by
  have h := unit_conjugateEquiv (adj₀₁.comp adj₁₂) adj₀₂ φ (G₁₀.obj K)
  have hn := (conjugateEquiv (adj₀₁.comp adj₁₂) adj₀₂ φ).naturality
    (F₁₂.map (adj₀₁.counit.app K))
  have hu := adj₁₂.unit.naturality (adj₀₁.counit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at h hn hu
  rw [G₂₀.map_comp, ← Category.assoc, ← h, Category.assoc, ← hn, comp_unit_app,
    Category.assoc, ← G₁₀.map_comp_assoc, ← hu, G₁₀.map_comp,
    Category.assoc, adj₀₁.right_triangle_components_assoc]

/-- The transition map `G₁₀ K ⟶ G₂₀ (F₁₂ K)` attached to an isomorphism
`φ : F₀₂ ≅ F₀₁ ⋙ F₁₂` is an isomorphism if the unit of `adj₁₂` is an isomorphism at `K`. -/
lemma isIso_unit_app_comp_map_comp_counit (φ : F₀₂ ≅ F₀₁ ⋙ F₁₂) (K : C₁)
    [IsIso (adj₁₂.unit.app K)] :
    IsIso (adj₀₂.unit.app (G₁₀.obj K) ≫
      G₂₀.map (φ.hom.app (G₁₀.obj K) ≫ F₁₂.map (adj₀₁.counit.app K))) := by
  rw [unit_app_comp_map_comp_counit_eq adj₀₁ adj₁₂ adj₀₂]
  have : IsIso (conjugateEquiv (adj₀₁.comp adj₁₂) adj₀₂ φ.hom) :=
    conjugateEquiv_iso _ _ φ.hom
  infer_instance

end Adjunction

end CategoryTheory
