/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Tensoring strict pairs

Source: the tensor formula in the latest blueprint's Tate compatibility lemma.
(blueprint: lem-wf-strict-pair-tensor)
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v u' v'
open CategoryTheory MonoidalCategory

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  (P : C ⥤ C) [P.Monoidal] {L : C} (τ : P.obj L ≅ L)

/-- Tensor with a fixed strict pair, using the inverse tensorator.
Source: latest blueprint, Tate twist formula (blueprint: lem-wf-strict-pair-tensor).
The morphism equation follows by tensorator naturality and the original strict
morphism equation; tensor bifunctoriality gives the identity and composition laws. -/
def tensorWith : IsoAlgebra P ⥤ IsoAlgebra P where
  obj K := mk (K.carrier ⊗ L) ((Functor.Monoidal.μIso P _ _).symm ≪≫ tensorIso K.str τ)
  map {K K'} f := ObjectProperty.homMk {
    f := f.hom.f ⊗ₘ 𝟙 L
    h := by
      have hf : P.map f.hom.f ≫ K'.str.hom = K.str.hom ≫ f.hom.f := f.hom.h
      change P.map (f.hom.f ⊗ₘ 𝟙 L) ≫
        (Functor.OplaxMonoidal.δ P _ _ ≫ (K'.str.hom ⊗ₘ τ.hom)) =
          (Functor.OplaxMonoidal.δ P _ _ ≫ (K.str.hom ⊗ₘ τ.hom)) ≫
            (f.hom.f ⊗ₘ 𝟙 L)
      rw [← Category.assoc, ← Functor.OplaxMonoidal.δ_natural, Category.assoc,
        tensorHom_comp_tensorHom, P.map_id, Category.id_comp,
        hf]
      simp only [Category.assoc, tensorHom_comp_tensorHom, Category.comp_id] }
  map_id K := ObjectProperty.hom_ext _ (Algebra.Hom.ext (by simp))
  map_comp f g := ObjectProperty.hom_ext _ (Algebra.Hom.ext (by
    change (f.hom.f ≫ g.hom.f) ⊗ₘ 𝟙 L =
      (f.hom.f ⊗ₘ 𝟙 L) ≫ (g.hom.f ⊗ₘ 𝟙 L)
    rw [tensorHom_comp_tensorHom, Category.comp_id]))

@[simp]
lemma tensorRight_obj_carrier (K : IsoAlgebra P) :
    ((tensorWith P τ).obj K).carrier = K.carrier ⊗ L := rfl

@[simp]
lemma tensorRight_map {K K' : IsoAlgebra P} (f : K ⟶ K') :
    ((tensorWith P τ).map f).hom.f = f.hom.f ⊗ₘ 𝟙 L := rfl

end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {P : C ⥤ C} [P.Monoidal] {Q : D ⥤ D} [Q.Monoidal]
  (B : C ⥤ D) [B.Monoidal] (c : B ⋙ Q ≅ P ⋙ B) [c.hom.IsMonoidal]

end CategoryTheory.Endofunctor.IsoAlgebra

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  {P : C ⥤ C} [P.Monoidal] {Q : D ⥤ D} [Q.Monoidal]


end CategoryTheory.Endofunctor.IsoAlgebra
