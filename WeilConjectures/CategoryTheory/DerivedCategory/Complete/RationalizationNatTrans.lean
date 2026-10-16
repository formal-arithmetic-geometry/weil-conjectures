/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationRecollement

/-!
# Unique transport of natural transformations to the rationalization

Let `M` be a submonoid of a commutative ring `R` and let `F G : C ⥤ D` be `R`-linear triangulated
functors between `R`-linear triangulated categories. They induce triangulated functors
`Rationalization.map M F`, `Rationalization.map M G` between the rationalizations, and a natural
transformation `τ : F ⟶ G` induces `Rationalization.mapNatTrans M τ`
(`WeilConjectures.CategoryTheory.DerivedCategory.RationalizationRecollement`). We
complete this functoriality:

* `mapNatTrans M τ` is the *unique* natural transformation compatible with `τ` through the
  factorizations `Q ⋙ map M F ≅ F ⋙ Q` (`CategoryTheory.Rationalization.mapNatTrans_unique`);
* it commutes with the shifts when `τ` does
  (`CategoryTheory.Rationalization.commShift_mapNatTrans`);
* it is an isomorphism when `τ` is, and more precisely its component at an object `X` of `C` is
  an isomorphism as soon as `τ.app X` is
  (`CategoryTheory.Rationalization.isIso_mapNatTrans_app`); hence `mapNatTrans M τ` is an
  isomorphism as soon as all components of `τ` are
  (`CategoryTheory.Rationalization.isIso_mapNatTrans_of_isIso_app`).

This is blueprint `prop-weil-pbc-rational-transport`: the integral data (direct image, completed
pullback, exchange transformation) descend uniquely to the rationalized categories
`D^b_c(-, E) = D^b_c(-, 𝒪_E)[1/ϖ]` of blueprint `def-weil-pbc-rational-category`, and an
integral isomorphism stays an isomorphism.
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

open CategoryTheory Category Limits Pretriangulated

namespace CategoryTheory.Rationalization

variable {R : Type w} [CommRing R] (M : Submonoid R)
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [Pretriangulated C] [IsTriangulated C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D] [HasZeroObject D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [∀ n : ℤ, (shiftFunctor D n).Linear R]
  [Pretriangulated D] [IsTriangulated D]
  {F G : C ⥤ D} [F.CommShift ℤ] [F.IsTriangulated] [F.Linear R]
  [G.CommShift ℤ] [G.IsTriangulated] [G.Linear R]

omit [IsTriangulated C] [IsTriangulated D] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] in
/-- Blueprint `prop-weil-pbc-rational-transport` (uniqueness): a natural transformation
`map M F ⟶ map M G` compatible with `τ : F ⟶ G` through the factorizations `mapFac` is
`mapNatTrans M τ`. -/
lemma mapNatTrans_unique (τ : F ⟶ G) (σ : map M F ⟶ map M G)
    (h : ∀ X : C, σ.app ((Q M C).obj X) ≫ (mapFac M G).hom.app X =
      (mapFac M F).hom.app X ≫ (Q M D).map (τ.app X)) :
    σ = mapNatTrans M τ :=
  Localization.natTrans_ext (Q M C) (W M C) fun X ↦ by
    rw [← cancel_mono ((mapFac M G).hom.app X), h, mapFac_hom_naturality]

/-- Blueprint `prop-weil-pbc-rational-transport` (isomorphisms): the component of
`mapNatTrans M τ` at an object `X` of `C` is an isomorphism as soon as `τ.app X` is. -/
instance isIso_mapNatTrans_app (τ : F ⟶ G) (X : C) [IsIso (τ.app X)] :
    IsIso ((mapNatTrans M τ).app ((Q M C).obj X)) := by
  rw [mapNatTrans_app]
  infer_instance

omit [IsTriangulated C] [IsTriangulated D] [∀ n : ℤ, (shiftFunctor C n).Linear R]
  [∀ n : ℤ, (shiftFunctor D n).Linear R] in
/-- Blueprint `prop-weil-pbc-rational-transport` (isomorphisms): if all components of
`τ : F ⟶ G` are isomorphisms, so is the induced natural transformation on rationalizations. -/
lemma isIso_mapNatTrans_of_isIso_app (τ : F ⟶ G) (h : ∀ X : C, IsIso (τ.app X)) :
    IsIso (mapNatTrans M τ) :=
  isIso_of_isIso_app_Q _ fun X ↦ by
    have := h X
    infer_instance

instance isIso_mapNatTrans (τ : F ⟶ G) [IsIso τ] : IsIso (mapNatTrans M τ) :=
  isIso_mapNatTrans_of_isIso_app M τ inferInstance

/-- Blueprint `prop-weil-pbc-rational-transport`: the natural transformation induced on
rationalizations by a natural transformation which commutes with the shifts commutes with the
shifts. -/
instance commShift_mapNatTrans (τ : F ⟶ G) [NatTrans.CommShift τ ℤ] :
    NatTrans.CommShift (mapNatTrans M τ) ℤ := ⟨fun a ↦ by
  refine Localization.natTrans_ext (Q M C) (W M C) fun X ↦ ?_
  have nat := (mapNatTrans M τ).naturality (((Q M C).commShiftIso a).hom.app X)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  rw [← cancel_epi ((map M F).map (((Q M C).commShiftIso a).hom.app X)), reassoc_of% nat]
  erw [Functor.commShiftOfLocalization_iso_hom_app, Functor.commShiftOfLocalization_iso_hom_app]
  have hF : Localization.Lifting.iso (Q M C) (W M C) (F ⋙ Q M D) (map M F) = mapFac M F := rfl
  have hG : Localization.Lifting.iso (Q M C) (W M C) (G ⋙ Q M D) (map M G) = mapFac M G := rfl
  simp only [hF, hG, mapNatTrans_app, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.map_id, id_comp, assoc]
  simp only [Functor.commShiftIso_comp_hom_app, Functor.map_comp, assoc]
  erw [Functor.map_id, id_comp]
  rw [Iso.inv_hom_id_app_assoc,
    ← Functor.map_comp_assoc (shiftFunctor _ a) ((mapFac M F).inv.app X), Iso.inv_hom_id_app]
  erw [Functor.map_id, id_comp]
  rw [← Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp_assoc,
    NatTrans.shift_app_comm, Functor.map_comp_assoc]⟩

end CategoryTheory.Rationalization
