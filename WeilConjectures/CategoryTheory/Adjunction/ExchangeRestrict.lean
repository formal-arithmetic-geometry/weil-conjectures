/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate

/-!
# Exchange morphisms of restrictions to full subcategories

Let `ad : lf ⊣ rf` and `ad' : lf' ⊣ rf'` be adjunctions and `t : g ⋙ lf' ≅ lf ⋙ g'` a
commutation isomorphism. If all the functors preserve given full subcategories, the adjunctions
restrict to the full subcategories (`Adjunction.restrictFullyFaithful`, along the inclusions,
with the identity comparisons `ObjectProperty.liftCompιIso`). For an isomorphism `θ` of the
restricted functors which is `t` on the ambient categories, the exchange morphism of `θ` is, on
the ambient categories, the exchange morphism of `t`
(`CategoryTheory.Adjunction.exchangeRight_restrictFullyFaithful_app_hom`).
-/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {B A B' A' : Type*} [Category* B] [Category* A] [Category* B'] [Category* A']
  {PB : ObjectProperty B} {PA : ObjectProperty A} {PB' : ObjectProperty B'}
  {PA' : ObjectProperty A'}
  {lf : B ⥤ A} {rf : A ⥤ B} {lf' : B' ⥤ A'} {rf' : A' ⥤ B'} {g : B ⥤ B'} {g' : A ⥤ A'}
  (ad : lf ⊣ rf) (ad' : lf' ⊣ rf') (t : g ⋙ lf' ≅ lf ⋙ g')
  (hlf : ∀ K : PB.FullSubcategory, PA ((PB.ι ⋙ lf).obj K))
  (hrf : ∀ K : PA.FullSubcategory, PB ((PA.ι ⋙ rf).obj K))
  (hlf' : ∀ K : PB'.FullSubcategory, PA' ((PB'.ι ⋙ lf').obj K))
  (hrf' : ∀ K : PA'.FullSubcategory, PB' ((PA'.ι ⋙ rf').obj K))
  (hg : ∀ K : PB.FullSubcategory, PB' ((PB.ι ⋙ g).obj K))
  (hg' : ∀ K : PA.FullSubcategory, PA' ((PA.ι ⋙ g').obj K))

/-- **Exchange morphisms of restrictions.** The exchange morphism of an isomorphism `θ` of the
functors restricted to full subcategories, for the restricted adjunctions, is the exchange
morphism of the ambient isomorphism `t` restricting to `θ`. -/
lemma exchangeRight_restrictFullyFaithful_app_hom
    (θ : PB'.lift (PB.ι ⋙ g) hg ⋙ PA'.lift (PB'.ι ⋙ lf') hlf' ≅
      PA.lift (PB.ι ⋙ lf) hlf ⋙ PA'.lift (PA.ι ⋙ g') hg')
    (hθ : ∀ K, (θ.hom.app K).hom = t.hom.app K.obj) (K : PA.FullSubcategory) :
    ((exchangeRight
        (ad.restrictFullyFaithful PB.fullyFaithfulι PA.fullyFaithfulι
          (PA.liftCompιIso (PB.ι ⋙ lf) hlf).symm (PB.liftCompιIso (PA.ι ⋙ rf) hrf).symm)
        (ad'.restrictFullyFaithful PB'.fullyFaithfulι PA'.fullyFaithfulι
          (PA'.liftCompιIso (PB'.ι ⋙ lf') hlf').symm (PB'.liftCompιIso (PA'.ι ⋙ rf') hrf').symm)
        θ).app K).hom =
      (exchangeRight ad ad' t).app K.obj := by
  rw [exchangeRight_app, exchangeRight_app, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.comp_hom, ← ObjectProperty.ι_map,
    map_restrictFullyFaithful_unit_app, ← ObjectProperty.ι_map, ← ObjectProperty.ι_map,
    ObjectProperty.ι_obj_lift_map, ObjectProperty.ι_obj_lift_map]
  simp only [Functor.comp_map, ObjectProperty.ι_map, hθ]
  rw [← ObjectProperty.ι_map, ObjectProperty.ι_obj_lift_map, Functor.comp_map,
    map_restrictFullyFaithful_counit_app]
  simp [ObjectProperty.liftCompιIso]

end CategoryTheory.Adjunction
