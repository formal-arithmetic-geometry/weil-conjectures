/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The cocycle condition for composition isomorphisms of functors induced on derived categories

For exact functors `A : C ⥤ D`, `B : D ⥤ E` and `F : C ⥤ E` with an isomorphism
`e : F ≅ A ⋙ B`, the functors induced on derived categories are related by the isomorphism
`Functor.mapDerivedCategoryCompIsoOfIso e : D(A) ⋙ D(B) ≅ D(F)`. These isomorphisms satisfy
the cocycle condition whenever the underlying isomorphisms `e` do
(`Functor.mapDerivedCategoryCompIsoOfIso_cocycle`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']

section

variable {A : C ⥤ D} {B : D ⥤ E} {F : C ⥤ E} [A.Additive] [B.Additive] [F.Additive]
  [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [PreservesFiniteLimits B] [PreservesFiniteColimits B]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The isomorphism `D(A) ⋙ D(B) ≅ D(F)` induced by an isomorphism `F ≅ A ⋙ B` of exact
functors. -/
noncomputable def mapDerivedCategoryCompIsoOfIso (e : F ≅ A ⋙ B) :
    A.mapDerivedCategory ⋙ B.mapDerivedCategory ≅ F.mapDerivedCategory :=
  (mapDerivedCategoryCompIso A B).symm ≪≫ (mapDerivedCategoryNatIso e).symm

omit [HasDerivedCategory E'] in
private lemma mapDerivedCategoryCompIso_hom_app_factors' (K : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIso A B).hom.app (DerivedCategory.Q.obj K) ≫
      B.mapDerivedCategory.map (A.mapDerivedCategoryFactors.hom.app K) ≫
      B.mapDerivedCategoryFactors.hom.app ((A.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
    (A ⋙ B).mapDerivedCategoryFactors.hom.app K := by
  rw [← mapDerivedCategoryCompIso_fac]
  have : (Functor.mapHomologicalComplexCompIso (Iso.refl (A ⋙ B)) (ComplexShape.up ℤ)).hom.app K =
      𝟙 _ := by
    ext n
    simp
    rfl
  rw [this]
  erw [DerivedCategory.Q.map_id, Category.comp_id]

omit [HasDerivedCategory E'] in
/-- The isomorphism `Functor.mapDerivedCategoryCompIsoOfIso e` on the image of a complex. -/
@[reassoc]
lemma mapDerivedCategoryCompIsoOfIso_hom_app_factors (e : F ≅ A ⋙ B)
    (K : CochainComplex C ℤ) :
    (mapDerivedCategoryCompIsoOfIso e).hom.app (DerivedCategory.Q.obj K) ≫
        F.mapDerivedCategoryFactors.hom.app K =
      B.mapDerivedCategory.map (A.mapDerivedCategoryFactors.hom.app K) ≫
        B.mapDerivedCategoryFactors.hom.app
          ((A.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app K) := by
  have h₁ := mapDerivedCategoryNatIso_fac e K
  have h₂ := mapDerivedCategoryCompIso_hom_app_factors' (A := A) (B := B) K
  simp only [mapDerivedCategoryCompIsoOfIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  rw [← cancel_epi ((mapDerivedCategoryCompIso A B).hom.app (DerivedCategory.Q.obj K)),
    Iso.hom_inv_id_app_assoc, reassoc_of% h₂,
    ← cancel_epi ((mapDerivedCategoryNatIso e).hom.app (DerivedCategory.Q.obj K)),
    Iso.hom_inv_id_app_assoc, reassoc_of% h₁, ← DerivedCategory.Q.map_comp]
  have : (NatTrans.mapHomologicalComplex e.hom (ComplexShape.up ℤ)).app K ≫
      (NatTrans.mapHomologicalComplex e.inv (ComplexShape.up ℤ)).app K = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, e.hom_inv_id,
      NatTrans.mapHomologicalComplex_id, NatTrans.id_app]
  rw [this, CategoryTheory.Functor.map_id, Category.comp_id]

end

variable {A : C ⥤ D} {B : D ⥤ E} {B' : E ⥤ E'} {F₁ : C ⥤ E} {F₂ : C ⥤ E'} {H : D ⥤ E'}
  [A.Additive] [B.Additive] [B'.Additive] [F₁.Additive] [F₂.Additive] [H.Additive]
  [PreservesFiniteLimits A] [PreservesFiniteColimits A]
  [PreservesFiniteLimits B] [PreservesFiniteColimits B]
  [PreservesFiniteLimits B'] [PreservesFiniteColimits B']
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- **The cocycle condition** for the isomorphisms `Functor.mapDerivedCategoryCompIsoOfIso`:
given isomorphisms `e₁ : F₁ ≅ A ⋙ B`, `e₂ : F₂ ≅ F₁ ⋙ B'`, `e₃ : H ≅ B ⋙ B'` and
`e₄ : F₂ ≅ A ⋙ H` of exact functors satisfying the cocycle condition, the induced isomorphisms
of functors on derived categories satisfy the cocycle condition. -/
lemma mapDerivedCategoryCompIsoOfIso_cocycle (e₁ : F₁ ≅ A ⋙ B) (e₂ : F₂ ≅ F₁ ⋙ B')
    (e₃ : H ≅ B ⋙ B') (e₄ : F₂ ≅ A ⋙ H)
    (h : ∀ X, e₄.hom.app X ≫ e₃.hom.app (A.obj X) = e₂.hom.app X ≫ B'.map (e₁.hom.app X))
    (K : DerivedCategory C) :
    (mapDerivedCategoryNatIso e₃ ≪≫ mapDerivedCategoryCompIso B B').hom.app
          (A.mapDerivedCategory.obj K) ≫
        B'.mapDerivedCategory.map ((mapDerivedCategoryCompIsoOfIso e₁).hom.app K) ≫
        (mapDerivedCategoryCompIsoOfIso e₂).hom.app K =
      (mapDerivedCategoryCompIsoOfIso e₄).hom.app K := by
  obtain ⟨L, ⟨eL⟩⟩ : ∃ L : CochainComplex C ℤ, Nonempty (DerivedCategory.Q.obj L ≅ K) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  suffices hL : (mapDerivedCategoryNatIso e₃ ≪≫ mapDerivedCategoryCompIso B B').hom.app
          (A.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) ≫
        B'.mapDerivedCategory.map
          ((mapDerivedCategoryCompIsoOfIso e₁).hom.app (DerivedCategory.Q.obj L)) ≫
        (mapDerivedCategoryCompIsoOfIso e₂).hom.app (DerivedCategory.Q.obj L) =
      (mapDerivedCategoryCompIsoOfIso e₄).hom.app (DerivedCategory.Q.obj L) by
    have n₁ := (mapDerivedCategoryNatIso e₃ ≪≫ mapDerivedCategoryCompIso B B').hom.naturality
      (A.mapDerivedCategory.map eL.hom)
    have n₂ := (mapDerivedCategoryCompIsoOfIso e₁).hom.naturality eL.hom
    have n₃ := (mapDerivedCategoryCompIsoOfIso e₂).hom.naturality eL.hom
    have n₄ := (mapDerivedCategoryCompIsoOfIso e₄).hom.naturality eL.hom
    simp only [Functor.comp_obj, Functor.comp_map] at n₁ n₂ n₃ n₄
    rw [← cancel_epi (H.mapDerivedCategory.map (A.mapDerivedCategory.map eL.hom)), n₄,
      ← hL, reassoc_of% n₁, ← Functor.map_comp_assoc, n₂, Functor.map_comp_assoc, n₃]
    simp only [Category.assoc]
  rw [← cancel_mono (F₂.mapDerivedCategoryFactors.hom.app L),
    mapDerivedCategoryCompIsoOfIso_hom_app_factors, Category.assoc, Category.assoc,
    mapDerivedCategoryCompIsoOfIso_hom_app_factors, ← Functor.map_comp_assoc,
    mapDerivedCategoryCompIsoOfIso_hom_app_factors]
  simp only [Functor.map_comp, Category.assoc]
  erw [mapDerivedCategoryFactors_hom_naturality_assoc]
  have n := (mapDerivedCategoryNatIso e₃ ≪≫ mapDerivedCategoryCompIso B B').hom.naturality
    (A.mapDerivedCategoryFactors.hom.app L)
  simp only [Functor.comp_obj, Functor.comp_map] at n
  rw [← reassoc_of% n]
  congr 1
  have hρ := mapDerivedCategoryNatIso_fac e₃ ((A.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
  have hc := mapDerivedCategoryCompIso_hom_app_factors' (A := B) (B := B')
    ((A.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% hc]
  erw [reassoc_of% hρ]
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 2
  ext n
  have := h (L.X n)
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f]
  rw [← cancel_epi (e₄.hom.app (L.X n)), Iso.hom_inv_id_app, reassoc_of% this,
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id, Category.id_comp,
    Iso.hom_inv_id_app]

end CategoryTheory.Functor
