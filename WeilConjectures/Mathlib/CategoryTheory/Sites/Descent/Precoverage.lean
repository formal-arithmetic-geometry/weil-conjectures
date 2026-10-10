/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Descent.Precoverage

/-!
# Full faithfulness of pulling back descent data, without the prestack assumption

`CategoryTheory.Pseudofunctor.DescentData.fullyFaithfulPullFunctor` asserts that for a prestack
`F` and a covering family `f'` refining a family `f`, the functor
`pullFunctor : F.DescentData f ⥤ F.DescentData f'` is fully faithful. Here we only assume that
the presheaves of morphisms between the objects of the descent data at hand are sheaves; this
applies to pseudofunctors which are prestacks only on a full subcategory, such as quasi-coherent
modules inside all sheaves of modules.
-/

@[expose] public section

universe t t' v' v u' u

namespace CategoryTheory.Pseudofunctor.DescentData

open Opposite Bicategory Limits LocallyDiscreteOpToCat

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})
  {J : GrothendieckTopology C}
  {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
  {ι' : Type t'} {X' : ι' → C} {f' : ∀ j, X' j ⟶ S}
  {α : ι' → ι} {p' : ∀ j, X' j ⟶ X (α j)} (w : ∀ j, p' j ≫ f (α j) = f' j)
  (hf' : Sieve.ofArrows _ f' ∈ J S)

include w hf' in
/-- Variant of `fullyFaithfulPullFunctor`: pulling back descent data to a covering family `f'`
refining `f` is bijective on morphisms `D₁ ⟶ D₂` as soon as the presheaves of morphisms between
the objects of `D₁` and `D₂` are sheaves. -/
lemma bijective_pullFunctor_map_of_isSheaf {D₁ D₂ : F.DescentData f}
    (h : ∀ i, Presheaf.IsSheaf (J.over (X i)) (F.presheafHom (D₁.obj i) (D₂.obj i))) :
    Function.Bijective ((pullFunctor F (f := f) (p := 𝟙 _) (f' := f') (p' := p')
      (by cat_disch)).map : (D₁ ⟶ D₂) → _) := by
  sorry

include w hf' in
/-- Descent data whose pullbacks to a covering family `f'` refining `f` are isomorphic are
isomorphic, as soon as the presheaves of morphisms between their objects are sheaves. -/
lemma nonempty_iso_of_pullFunctor_obj_iso {D₁ D₂ : F.DescentData f}
    (h₁₂ : ∀ i, Presheaf.IsSheaf (J.over (X i)) (F.presheafHom (D₁.obj i) (D₂.obj i)))
    (h₂₁ : ∀ i, Presheaf.IsSheaf (J.over (X i)) (F.presheafHom (D₂.obj i) (D₁.obj i)))
    (h₁₁ : ∀ i, Presheaf.IsSheaf (J.over (X i)) (F.presheafHom (D₁.obj i) (D₁.obj i)))
    (h₂₂ : ∀ i, Presheaf.IsSheaf (J.over (X i)) (F.presheafHom (D₂.obj i) (D₂.obj i)))
    (e : (pullFunctor F (f := f) (p := 𝟙 _) (f' := f') (p' := p') (by cat_disch)).obj D₁ ≅
      (pullFunctor F (f := f) (p := 𝟙 _) (f' := f') (p' := p') (by cat_disch)).obj D₂) :
    Nonempty (D₁ ≅ D₂) := by
  sorry

end CategoryTheory.Pseudofunctor.DescentData
