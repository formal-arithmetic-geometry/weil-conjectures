/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded

/-!
# The unbounded derived base change map restricts to the bounded below one

For a commutative square of schemes `sq : CommSq g' f' f g`, the derived base change map
`AlgebraicGeometry.Etale.derivedBaseChangeMap sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` on the unbounded
derived categories restricts on bounded below objects to the bounded below derived base change
map `AlgebraicGeometry.Etale.derivedBaseChangeMapPlus sq`, modulo the compatibility isomorphisms
of the derived functors with the inclusions `DerivedCategory.Plus.ι`
(`AlgebraicGeometry.Etale.derivedBaseChangeMap_app_ι_obj`). In particular, the unbounded map is
an isomorphism on a bounded below object as soon as the bounded below one is
(`AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_app_of_isIso_derivedBaseChangeMapPlus`).

The proof is a general fact on mates (`CategoryTheory.mateEquiv_app_of_restrict`): mates are
compatible with restricting adjunctions along fully faithful functors, applied to the bounded
below derived adjunctions, which are restrictions of the unbounded ones
(`CategoryTheory.Adjunction.derivedAdjunctionPlus`), together with the comparison of the
composition isomorphisms of derived pullbacks on `D` and on `D⁺`
(`AlgebraicGeometry.Etale.ι_map_upperStarCompDerivedPlus_hom_app`).
-/

@[expose] public section

universe u' u

open CategoryTheory Category

namespace CategoryTheory

section Restrict

variable {C₁ D₁ C₂ D₂ C₁' D₁' C₂' D₂' : Type*} [Category C₁] [Category D₁] [Category C₂]
  [Category D₂] [Category C₁'] [Category D₁'] [Category C₂'] [Category D₂']
  {iC₁ : C₁' ⥤ C₁} {iD₁ : D₁' ⥤ D₁} {iC₂ : C₂' ⥤ C₂} {iD₂ : D₂' ⥤ D₂}
  {L₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {L₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
  {L₁' : C₁' ⥤ D₁'} {R₁' : D₁' ⥤ C₁'} {L₂' : C₂' ⥤ D₂'} {R₂' : D₂' ⥤ C₂'}
  {G : C₁ ⥤ C₂} {H : D₁ ⥤ D₂} {G' : C₁' ⥤ C₂'} {H' : D₁' ⥤ D₂'}

/-- The components of the mate of a 2-square: unit, the square, and the counit. -/
lemma mateEquiv_natTrans_app (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H)
    (Y : D₁) :
    (mateEquiv adj₁ adj₂ α).natTrans.app Y =
      adj₂.unit.app (G.obj (R₁.obj Y)) ≫ R₂.map (α.natTrans.app (R₁.obj Y)) ≫
        R₂.map (H.map (adj₁.counit.app Y)) := by
  simp [mateEquiv_apply]

/-- **Mates commute with restriction along fully faithful functors.** Let `adj₁' : L₁' ⊣ R₁'`
and `adj₂' : L₂' ⊣ R₂'` be restrictions of `adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂` along functors
`iC₁, iD₁, iC₂, iD₂`, in the sense that their counit, respectively unit, is given in terms of the
one of `adj₁`, respectively `adj₂`, by the formula of `Adjunction.restrictFullyFaithful`, and let
`α'` be a 2-square restricting `α`. Then the mate of `α'` restricts the mate of `α`. -/
lemma mateEquiv_app_of_restrict (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₁' : L₁' ⊣ R₁')
    (adj₂' : L₂' ⊣ R₂') (c₁L : iC₁ ⋙ L₁ ≅ L₁' ⋙ iD₁) (c₁R : iD₁ ⋙ R₁ ≅ R₁' ⋙ iC₁)
    (c₂L : iC₂ ⋙ L₂ ≅ L₂' ⋙ iD₂) (c₂R : iD₂ ⋙ R₂ ≅ R₂' ⋙ iC₂)
    (eG : iC₁ ⋙ G ≅ G' ⋙ iC₂) (eH : iD₁ ⋙ H ≅ H' ⋙ iD₂)
    (α : TwoSquare G L₁ L₂ H) (α' : TwoSquare G' L₁' L₂' H')
    (h₁ : ∀ Y, iD₁.map (adj₁'.counit.app Y) =
      c₁L.inv.app (R₁'.obj Y) ≫ L₁.map (c₁R.inv.app Y) ≫ adj₁.counit.app (iD₁.obj Y))
    (h₂ : ∀ X, iC₂.map (adj₂'.unit.app X) =
      adj₂.unit.app (iC₂.obj X) ≫ R₂.map (c₂L.hom.app X) ≫ c₂R.hom.app (L₂'.obj X))
    (hα : ∀ X, iD₂.map (α'.natTrans.app X) =
      c₂L.inv.app (G'.obj X) ≫ L₂.map (eG.inv.app X) ≫ α.natTrans.app (iC₁.obj X) ≫
        H.map (c₁L.hom.app X) ≫ eH.hom.app (L₁'.obj X))
    (Y : D₁') :
    iC₂.map ((mateEquiv adj₁' adj₂' α').natTrans.app Y) =
      eG.inv.app (R₁'.obj Y) ≫ G.map (c₁R.inv.app Y) ≫
        (mateEquiv adj₁ adj₂ α).natTrans.app (iD₁.obj Y) ≫ R₂.map (eH.hom.app Y) ≫
        c₂R.hom.app (H'.obj Y) := by
  have hR : ∀ {Z Z' : D₂'} (φ : Z ⟶ Z'),
      iC₂.map (R₂'.map φ) = c₂R.inv.app Z ≫ R₂.map (iD₂.map φ) ≫ c₂R.hom.app Z' := by
    intro Z Z' φ
    have := c₂R.hom.naturality φ
    dsimp at this
    rw [this, Iso.inv_hom_id_app_assoc]
  have hH : ∀ {Z Z' : D₁'} (φ : Z ⟶ Z'),
      iD₂.map (H'.map φ) = eH.inv.app Z ≫ H.map (iD₁.map φ) ≫ eH.hom.app Z' := by
    intro Z Z' φ
    have := eH.hom.naturality φ
    dsimp at this
    rw [this, Iso.inv_hom_id_app_assoc]
  rw [mateEquiv_natTrans_app, mateEquiv_natTrans_app, Functor.map_comp, Functor.map_comp, h₂,
    hR, hR, hα, hH, h₁]
  have hη := adj₂.unit.naturality (eG.inv.app (R₁'.obj Y) ≫ G.map (c₁R.inv.app Y))
  have hαn := α.natTrans.naturality (c₁R.inv.app Y)
  dsimp at hη hαn
  simp only [Functor.map_comp, assoc, Iso.hom_inv_id_app_assoc] at hη ⊢
  rw [reassoc_of% hη]
  congr 1
  simp only [← Functor.map_comp_assoc]
  congr 2
  simp only [Functor.map_comp, assoc, Iso.hom_inv_id_app_assoc, Functor.comp_obj]
  rw [← Functor.map_comp_assoc (H) (c₁L.hom.app _), Iso.hom_inv_id_app, Functor.map_id,
    id_comp, reassoc_of% hαn]
  rfl

end Restrict

end CategoryTheory

namespace AlgebraicGeometry

open Scheme DerivedCategory.Plus

open scoped CategoryTheory.Functor

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The composition isomorphism of the bounded below pullbacks
`AlgebraicGeometry.Etale.upperStarCompDerivedPlus` is the restriction of the composition
isomorphism `AlgebraicGeometry.Etale.leftDerivedUpperStarComp` of the unbounded derived
pullbacks, modulo the identifications `Lh^* ≅ D(h^*)`. -/
lemma ι_map_upperStarCompDerivedPlus_hom_app {T S R : Scheme.{u}} (h₁ : T ⟶ S)
    (h₂ : S ⟶ R) (h₁₂ : T ⟶ R) (hh₁₂ : h₁₂ = h₁ ≫ h₂)
    (K : DerivedCategory.Plus (Sheaf R.smallEtaleTopology A)) :
    ι.map ((upperStarCompDerivedPlus A h₁ h₂ h₁₂ hh₁₂).hom.app K) =
      (leftDerivedUpperStarIsoMapDerivedCategory A h₁₂).inv.app (ι.obj K) ≫
        (leftDerivedUpperStarComp A h₁ h₂ h₁₂ hh₁₂).hom.app (ι.obj K) ≫
        (L((h₁)^*[A])).map
          ((leftDerivedUpperStarIsoMapDerivedCategory A h₂).hom.app (ι.obj K)) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A h₁).hom.app
          ((D((h₂)^*[A])).obj (ι.obj K)) := by
  simp only [Etale.upperStarCompDerivedPlus, Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
    Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
    Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, Etale.leftDerivedUpperStarComp,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    Etale.leftDerivedUpperStarIsoMapDerivedCategory, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app, assoc,
    Iso.inv_hom_id_app_assoc]
  have h := ((h₁)^*[A]).leftDerivedFunctorIsoMapDerivedCategory.inv.naturality
    (((h₂)^*[A]).leftDerivedFunctorIsoMapDerivedCategory.hom.app (ι.obj K))
  rw [← reassoc_of% h, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    id_comp, Iso.inv_hom_id_app]
  erw [Category.comp_id]

end Etale

end AlgebraicGeometry
