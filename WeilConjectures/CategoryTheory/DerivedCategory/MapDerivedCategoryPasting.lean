/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Pasting of squares induced on derived categories

A square `τ : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂` of exact functors between abelian categories induces a square
`D(F₁) ⋙ D(F₂) ≅ D(G₁) ⋙ D(G₂)` of the functors induced on the derived categories
(`CategoryTheory.Functor.mapDerivedCategorySquareIso`). This file shows that equalities between
pastings of such squares can be checked on the underived squares: for a cube of exact functors
whose two pastings of underived squares agree, the two pastings of the induced squares agree
(`CategoryTheory.Functor.mapDerivedCategorySquareIso_cube`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Factors

variable {C₀ C₁ C₂ C₃ C₄ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₄] [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory C₃] [HasDerivedCategory C₄]

/-- The identification `D(G)(D(F)(Q K)) ⟶ Q(G(F K))` for exact functors `F` and `G`. -/
noncomputable def mapDerivedCategoryFactors₂ (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (K : CochainComplex C₀ ℤ) :
    G.mapDerivedCategory.obj (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ⟶
      DerivedCategory.Q.obj ((G.mapHomologicalComplex _).obj
        ((F.mapHomologicalComplex _).obj K)) :=
  G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
    G.mapDerivedCategoryFactors.hom.app _

/-- The identification `D(H)(D(G)(D(F)(Q K))) ⟶ Q(H(G(F K)))` for exact functors `F`, `G`
and `H`. -/
noncomputable def mapDerivedCategoryFactors₃ (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₂ ⥤ C₃)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H] (K : CochainComplex C₀ ℤ) :
    H.mapDerivedCategory.obj (G.mapDerivedCategory.obj
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K))) ⟶
      DerivedCategory.Q.obj ((H.mapHomologicalComplex _).obj ((G.mapHomologicalComplex _).obj
        ((F.mapHomologicalComplex _).obj K))) :=
  H.mapDerivedCategory.map (mapDerivedCategoryFactors₂ F G K) ≫
    H.mapDerivedCategoryFactors.hom.app _

section

variable (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₂ ⥤ C₃)
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] [H.Additive]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H] (K : CochainComplex C₀ ℤ)

instance : IsIso (mapDerivedCategoryFactors₂ F G K) := by
  dsimp [mapDerivedCategoryFactors₂]; infer_instance

instance : IsIso (mapDerivedCategoryFactors₃ F G H K) := by
  dsimp [mapDerivedCategoryFactors₃]; infer_instance

lemma mapDerivedCategoryFactors₃_eq :
    mapDerivedCategoryFactors₃ F G H K =
      H.mapDerivedCategory.map (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K)) ≫
        mapDerivedCategoryFactors₂ G H ((F.mapHomologicalComplex _).obj K) := by
  simp [mapDerivedCategoryFactors₃, mapDerivedCategoryFactors₂]

end

variable {F₁ : C₀ ⥤ C₁} {F₂ : C₁ ⥤ C₂} {G₁ : C₀ ⥤ C₃} {G₂ : C₃ ⥤ C₂}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]

/-- On the image `Q K` of a complex, the square induced by `τ` on derived categories is `τ`
applied to `K`. -/
@[reassoc]
lemma mapDerivedCategorySquareIso_hom_app_Q_obj (τ : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (K : CochainComplex C₀ ℤ) :
    (mapDerivedCategorySquareIso τ).hom.app (DerivedCategory.Q.obj K) ≫
        mapDerivedCategoryFactors₂ G₁ G₂ K =
      mapDerivedCategoryFactors₂ F₁ F₂ K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ.hom _).app K) := by
  have hF := mapDerivedCategoryCompIso_fac F₁ F₂ K
  have hG := mapDerivedCategoryCompIso_fac G₁ G₂ K
  have he := mapDerivedCategoryNatIso_fac τ K
  have hF₀ : (mapHomologicalComplexCompIso (Iso.refl (F₁ ⋙ F₂)) (ComplexShape.up ℤ)).hom.app K =
    𝟙 _ := rfl
  have hG₀ : (mapHomologicalComplexCompIso (Iso.refl (G₁ ⋙ G₂)) (ComplexShape.up ℤ)).hom.app K =
    𝟙 _ := rfl
  rw [hF₀, CategoryTheory.Functor.map_id, Category.comp_id] at hF
  rw [hG₀, CategoryTheory.Functor.map_id, Category.comp_id] at hG
  simp only [mapDerivedCategoryFactors₂, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  rw [hG, he, ← hF, Iso.inv_hom_id_app_assoc]

variable {F₀ : C₄ ⥤ C₀} [F₀.Additive] [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
  {H : C₂ ⥤ C₄} [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The square induced by `τ`, followed by an outer functor `D(H)`, on the image of a complex. -/
@[reassoc]
lemma map_mapDerivedCategorySquareIso_hom_app_Q_obj (τ : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂)
    (K : CochainComplex C₀ ℤ) :
    H.mapDerivedCategory.map ((mapDerivedCategorySquareIso τ).hom.app (DerivedCategory.Q.obj K)) ≫
        mapDerivedCategoryFactors₃ G₁ G₂ H K =
      mapDerivedCategoryFactors₃ F₁ F₂ H K ≫
        DerivedCategory.Q.map ((H.mapHomologicalComplex _).map
          ((NatTrans.mapHomologicalComplex τ.hom _).app K)) := by
  simp only [mapDerivedCategoryFactors₃, Category.assoc]
  rw [← Functor.map_comp_assoc, mapDerivedCategorySquareIso_hom_app_Q_obj, Functor.map_comp,
    Category.assoc, mapDerivedCategoryFactors_hom_naturality]

/-- The square induced by `τ`, preceded by an inner functor `D(F₀)`, on the image of a
complex. -/
@[reassoc]
lemma mapDerivedCategorySquareIso_hom_app_mapDerivedCategory_obj_Q_obj
    (τ : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (K : CochainComplex C₄ ℤ) :
    (mapDerivedCategorySquareIso τ).hom.app
        (F₀.mapDerivedCategory.obj (DerivedCategory.Q.obj K)) ≫
        mapDerivedCategoryFactors₃ F₀ G₁ G₂ K =
      mapDerivedCategoryFactors₃ F₀ F₁ F₂ K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ.hom _).app
          ((F₀.mapHomologicalComplex _).obj K)) := by
  have h := (mapDerivedCategorySquareIso τ).hom.naturality
    (F₀.mapDerivedCategoryFactors.hom.app K)
  simp only [Functor.comp_map] at h
  rw [mapDerivedCategoryFactors₃_eq, mapDerivedCategoryFactors₃_eq, ← reassoc_of% h,
    mapDerivedCategorySquareIso_hom_app_Q_obj, Category.assoc]

end Factors

section Cube

variable {Y Y' X X' Ỹ Ỹ' X̃ X̃' : Type*} [Category* Y] [Category* Y'] [Category* X]
  [Category* X'] [Category* Ỹ] [Category* Ỹ'] [Category* X̃] [Category* X̃']
  [Abelian Y] [Abelian Y'] [Abelian X] [Abelian X'] [Abelian Ỹ] [Abelian Ỹ'] [Abelian X̃]
  [Abelian X̃'] [HasDerivedCategory Y] [HasDerivedCategory Y'] [HasDerivedCategory X]
  [HasDerivedCategory X'] [HasDerivedCategory Ỹ] [HasDerivedCategory Ỹ'] [HasDerivedCategory X̃]
  [HasDerivedCategory X̃']
  {a : Y ⥤ Y'} {b : Y' ⥤ X'} {c : Y ⥤ X} {e : X ⥤ X'}
  {a' : Ỹ ⥤ Ỹ'} {b' : Ỹ' ⥤ X̃'} {c' : Ỹ ⥤ X̃} {e' : X̃ ⥤ X̃'}
  {νY : Y ⥤ Ỹ} {νY' : Y' ⥤ Ỹ'} {νX : X ⥤ X̃} {νX' : X' ⥤ X̃'}
  [a.Additive] [PreservesFiniteLimits a] [PreservesFiniteColimits a]
  [b.Additive] [PreservesFiniteLimits b] [PreservesFiniteColimits b]
  [c.Additive] [PreservesFiniteLimits c] [PreservesFiniteColimits c]
  [e.Additive] [PreservesFiniteLimits e] [PreservesFiniteColimits e]
  [a'.Additive] [PreservesFiniteLimits a'] [PreservesFiniteColimits a']
  [b'.Additive] [PreservesFiniteLimits b'] [PreservesFiniteColimits b']
  [c'.Additive] [PreservesFiniteLimits c'] [PreservesFiniteColimits c']
  [e'.Additive] [PreservesFiniteLimits e'] [PreservesFiniteColimits e']
  [νY.Additive] [PreservesFiniteLimits νY] [PreservesFiniteColimits νY]
  [νY'.Additive] [PreservesFiniteLimits νY'] [PreservesFiniteColimits νY']
  [νX.Additive] [PreservesFiniteLimits νX] [PreservesFiniteColimits νX]
  [νX'.Additive] [PreservesFiniteLimits νX'] [PreservesFiniteColimits νX']

/-- **Pasting of induced squares.** Consider a cube of exact functors between abelian
categories, with top face `θ' : a' ⋙ b' ≅ c' ⋙ e'`, bottom face `θ : a ⋙ b ≅ c ⋙ e` and side
faces `τ_a`, `τ_b`, `τ_c`, `τ_e` relating them through the vertical functors `ν`. If the two
pastings of the underived faces agree, then so do the two pastings of the induced squares on
derived categories. -/
lemma mapDerivedCategorySquareIso_cube (θ : a ⋙ b ≅ c ⋙ e) (θ' : a' ⋙ b' ≅ c' ⋙ e')
    (τa : a ⋙ νY' ≅ νY ⋙ a') (τb : b ⋙ νX' ≅ νY' ⋙ b') (τc : c ⋙ νX ≅ νY ⋙ c')
    (τe : e ⋙ νX' ≅ νX ⋙ e')
    (h : ∀ k : Y, νX'.map (θ.hom.app k) ≫ τe.hom.app (c.obj k) ≫ e'.map (τc.hom.app k) =
      τb.hom.app (a.obj k) ≫ b'.map (τa.hom.app k) ≫ θ'.hom.app (νY.obj k))
    (K : DerivedCategory Y) :
    νX'.mapDerivedCategory.map ((mapDerivedCategorySquareIso θ).hom.app K) ≫
        (mapDerivedCategorySquareIso τe).hom.app (c.mapDerivedCategory.obj K) ≫
        e'.mapDerivedCategory.map ((mapDerivedCategorySquareIso τc).hom.app K) =
      (mapDerivedCategorySquareIso τb).hom.app (a.mapDerivedCategory.obj K) ≫
        b'.mapDerivedCategory.map ((mapDerivedCategorySquareIso τa).hom.app K) ≫
        (mapDerivedCategorySquareIso θ').hom.app (νY.mapDerivedCategory.obj K) := by
  let lhs : a.mapDerivedCategory ⋙ b.mapDerivedCategory ⋙ νX'.mapDerivedCategory ⟶
      νY.mapDerivedCategory ⋙ c'.mapDerivedCategory ⋙ e'.mapDerivedCategory :=
    (Functor.associator _ _ _).inv ≫
      whiskerRight (mapDerivedCategorySquareIso θ).hom νX'.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft c.mapDerivedCategory (mapDerivedCategorySquareIso τe).hom ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (mapDerivedCategorySquareIso τc).hom e'.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom
  let rhs : a.mapDerivedCategory ⋙ b.mapDerivedCategory ⋙ νX'.mapDerivedCategory ⟶
      νY.mapDerivedCategory ⋙ c'.mapDerivedCategory ⋙ e'.mapDerivedCategory :=
    whiskerLeft a.mapDerivedCategory (mapDerivedCategorySquareIso τb).hom ≫
      (Functor.associator _ _ _).inv ≫
      whiskerRight (mapDerivedCategorySquareIso τa).hom b'.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom ≫
      whiskerLeft νY.mapDerivedCategory (mapDerivedCategorySquareIso θ').hom
  suffices hlr : lhs = rhs by
    simpa [lhs, rhs] using congr_app hlr K
  refine Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso Y (.up ℤ))
    (fun k ↦ ?_)
  rw [← cancel_mono (mapDerivedCategoryFactors₃ νY c' e' k)]
  have hk : νX'.mapHomologicalComplex _ |>.map
        ((NatTrans.mapHomologicalComplex θ.hom _).app k) ≫
      (NatTrans.mapHomologicalComplex τe.hom _).app ((c.mapHomologicalComplex _).obj k) ≫
      (e'.mapHomologicalComplex _).map ((NatTrans.mapHomologicalComplex τc.hom _).app k) =
    (NatTrans.mapHomologicalComplex τb.hom _).app ((a.mapHomologicalComplex _).obj k) ≫
      (b'.mapHomologicalComplex _).map ((NatTrans.mapHomologicalComplex τa.hom _).app k) ≫
      (NatTrans.mapHomologicalComplex θ'.hom _).app ((νY.mapHomologicalComplex _).obj k) := by
    ext i
    simpa using h (k.X i)
  simp only [lhs, rhs, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.associator_inv_app, whiskerRight_app, whiskerLeft_app, Category.id_comp,
    Category.assoc]
  rw [map_mapDerivedCategorySquareIso_hom_app_Q_obj τc,
    mapDerivedCategorySquareIso_hom_app_mapDerivedCategory_obj_Q_obj_assoc τe,
    map_mapDerivedCategorySquareIso_hom_app_Q_obj_assoc θ,
    mapDerivedCategorySquareIso_hom_app_mapDerivedCategory_obj_Q_obj θ',
    map_mapDerivedCategorySquareIso_hom_app_Q_obj_assoc τa,
    mapDerivedCategorySquareIso_hom_app_mapDerivedCategory_obj_Q_obj_assoc τb]
  simp only [← Functor.map_comp]
  erw [hk]

end Cube

end CategoryTheory.Functor
