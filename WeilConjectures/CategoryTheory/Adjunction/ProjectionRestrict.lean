/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.KunnethMap
public import WeilConjectures.PoincareDuality.Abstract

/-!

# Projection morphisms of restricted adjunctions

Let `L ⊣ R` be an adjunction between monoidal categories and `P`, `Q` full monoidal subcategories
preserved by `L` and `R`. The projection comparison of the restricted adjunction
(`CategoryTheory.Adjunction.restrictFullyFaithful`) is the projection comparison of `L ⊣ R`
(`CategoryTheory.Adjunction.ι_map_projectionComparison_restrictFullyFaithful`); the companion
statement for projection morphisms is
`CategoryTheory.Adjunction.ι_map_projectionMorphism_restrictFullyFaithful`.

For a composite `i_! ⋙ p_*` of a left adjoint `i_! ⊣ i^*` and a right adjoint `p^* ⊣ p_*` and
an identification `f^* ≅ p^* ⋙ i^*`, the composite of the projection morphism of `p^* ⊣ p_*`, of
the inverse of the projection comparison of `i_! ⊣ i^*` and of the identification is therefore
computed on the full subcategories as on the ambient categories
(`CategoryTheory.Adjunction.ι_map_exceptionalProjection_restrictFullyFaithful`). This is the
exceptional projection morphism of a compactification `f = p ∘ i`, restricted to bounded
constructible complexes.

-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Adjunction

section Restrict

variable {C D : Type*} [Category C] [MonoidalCategory C] [Category D] [MonoidalCategory D]
  {P : ObjectProperty C} [P.IsMonoidal] {Q : ObjectProperty D} [Q.IsMonoidal]
  {L : C ⥤ D} {R : D ⥤ C} [R.Monoidal] (adj : L ⊣ R)
  (hL : ∀ X : P.FullSubcategory, Q (L.obj X.obj)) (hR : ∀ X : Q.FullSubcategory, P (R.obj X.obj))

/-- The projection comparison of the restriction of an adjunction `L ⊣ R` to full monoidal
subcategories is the projection comparison of `L ⊣ R`. -/
lemma ι_map_projectionComparison_restrictFullyFaithful (M : P.FullSubcategory)
    (N : Q.FullSubcategory) :
    Q.ι.map ((adj.restrictFullyFaithful P.fullyFaithfulι Q.fullyFaithfulι
      (Q.liftCompιIso (P.ι ⋙ L) hL).symm (P.liftCompιIso (Q.ι ⋙ R) hR).symm).projectionComparison
        M N) = adj.projectionComparison M.obj N.obj := by
  have hu := adj.map_restrictFullyFaithful_unit_app P.fullyFaithfulι Q.fullyFaithfulι
    (Q.liftCompιIso (P.ι ⋙ L) hL).symm (P.liftCompιIso (Q.ι ⋙ R) hR).symm M
  have hc := adj.map_restrictFullyFaithful_counit_app P.fullyFaithfulι Q.fullyFaithfulι
    (Q.liftCompιIso (P.ι ⋙ L) hL).symm (P.liftCompιIso (Q.ι ⋙ R) hR).symm
    ((Q.lift (P.ι ⋙ L) hL).obj M ⊗ N)
  simp only [ObjectProperty.liftCompιIso, Iso.symm_hom, Iso.symm_inv, Iso.refl_hom,
    Iso.refl_inv, NatTrans.id_app, Category.id_comp] at hu hc ⊢
  rw [projectionComparison, projectionComparison, homEquiv_counit, homEquiv_counit,
    Functor.map_comp, hc]
  erw [Functor.map_id, Category.id_comp]
  congr 1
  change L.map (P.ι.map (_ ≫ _)) = _
  congr 1
  rw [Functor.map_comp]
  congr 1
  rw [ObjectProperty.ι_map, ObjectProperty.whiskerRight_hom, ← ObjectProperty.ι_map, hu]
  erw [Functor.map_id, Category.comp_id, Category.comp_id]
  rfl

end Restrict


section Exceptional

variable {𝒳 𝒵 𝒴 : Type*} [Category 𝒳] [Category 𝒵] [Category 𝒴] [MonoidalCategory 𝒳]
  [MonoidalCategory 𝒵] [MonoidalCategory 𝒴]
  {PX : ObjectProperty 𝒳} [PX.IsMonoidal] {PZ : ObjectProperty 𝒵} [PZ.IsMonoidal]
  {PY : ObjectProperty 𝒴} [PY.IsMonoidal]
  {I : 𝒳 ⥤ 𝒵} {Is : 𝒵 ⥤ 𝒳} {_ : Is.Monoidal} (bi : I ⊣ Is)
  (hI : ∀ X : PX.FullSubcategory, PZ (I.obj X.obj))
  (hIs : ∀ X : PZ.FullSubcategory, PX (Is.obj X.obj))
  {Gs : 𝒴 ⥤ 𝒵} {G : 𝒵 ⥤ 𝒴} {_ : Gs.Monoidal} (ag : Gs ⊣ G)
  (hGs : ∀ X : PY.FullSubcategory, PZ (Gs.obj X.obj))
  (hG : ∀ X : PZ.FullSubcategory, PY (G.obj X.obj))
  {Fs : 𝒴 ⥤ 𝒳} (hFs : ∀ X : PY.FullSubcategory, PX (Fs.obj X.obj)) (e : Fs ≅ Gs ⋙ Is)


end Exceptional

end CategoryTheory.Adjunction
