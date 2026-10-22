/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J6
-/
module

public import Sheaf.Paper.SemilinearGeometryDerived
import all Sheaf.Paper.SemilinearSystemModels
import Sheaf.CategoryTheory.DerivedExactSquareComposition

/-! # Scalar-association cocycle for geometric coefficient systems

Source: Stacks Project, Tags 03EL, 0D6D and 07A4.
(blueprint: lem-pur-geometric-scalar-association-cocycle)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] WeilConjectures.SemilinearSections.hasDerived
  HasDerivedCategory.standard CategoryTheory.Functor.mapDerivedCategory
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
section ScalarCocycleCalculation
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [Category C₀] [Category C₁] [Category C₂]
  [Category D₀] [Category D₁] [Category D₂]
  {T₁ : C₂ ⥤ C₁} {R₁ : C₁ ⥤ C₂} {T₂ : C₁ ⥤ C₀} {R₂ : C₀ ⥤ C₁}
  {T₃ : C₂ ⥤ C₀} {R₃ : C₀ ⥤ C₂}
  {S₁ : D₂ ⥤ D₁} {Q₁ : D₁ ⥤ D₂} {S₂ : D₁ ⥤ D₀} {Q₂ : D₀ ⥤ D₁}
  {S₃ : D₂ ⥤ D₀} {Q₃ : D₀ ⥤ D₂}
  (a₁ : T₁ ⊣ R₁) (a₂ : T₂ ⊣ R₂) (a₃ : T₃ ⊣ R₃)
  (b₁ : S₁ ⊣ Q₁) (b₂ : S₂ ⊣ Q₂) (b₃ : S₃ ⊣ Q₃)
  (F₀ : C₀ ⥤ D₀) (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂)
  (c : T₁ ⋙ T₂ ≅ T₃) (d : S₁ ⋙ S₂ ≅ S₃)
  (r : R₂ ⋙ R₁ ≅ R₃) (q : Q₂ ⋙ Q₁ ≅ Q₃)
  (c_transpose : ∀ P N (f : T₃.obj P ⟶ N),
    a₁.homEquiv _ _ (a₂.homEquiv _ _ (c.hom.app P ≫ f)) =
      a₃.homEquiv _ _ f ≫ r.inv.app N)
  (d_transpose : ∀ P N (f : S₃.obj P ⟶ N),
    b₁.homEquiv _ _ (b₂.homEquiv _ _ (d.hom.app P ≫ f)) =
      b₃.homEquiv _ _ f ≫ q.inv.app N)
  (κ₁ : T₁ ⋙ F₁ ≅ F₂ ⋙ S₁) (κ₂ : T₂ ⋙ F₀ ≅ F₁ ⋙ S₂)
  (κ₃ : T₃ ⋙ F₀ ≅ F₂ ⋙ S₃)
  (β₁ : R₁ ⋙ F₂ ≅ F₁ ⋙ Q₁) (β₂ : R₂ ⋙ F₁ ≅ F₀ ⋙ Q₂)
  (β₃ : R₃ ⋙ F₂ ≅ F₀ ⋙ Q₃)
  (h₁ : ∀ P, b₁.homEquiv _ _ (κ₁.inv.app P) =
    F₂.map (a₁.unit.app P) ≫ β₁.hom.app (T₁.obj P))
  (h₂ : ∀ P, b₂.homEquiv _ _ (κ₂.inv.app P) =
    F₁.map (a₂.unit.app P) ≫ β₂.hom.app (T₂.obj P))
  (h₃ : ∀ P, b₃.homEquiv _ _ (κ₃.inv.app P) =
    F₂.map (a₃.unit.app P) ≫ β₃.hom.app (T₃.obj P))
  (hβ : ∀ N, F₂.map (r.inv.app N) ≫ β₁.hom.app (R₂.obj N) ≫
      Q₁.map (β₂.hom.app N) = β₃.hom.app N ≫ q.inv.app (F₀.obj N))

include a₁ a₂ a₃ b₁ b₂ b₃ F₁ r q c_transpose d_transpose β₁ β₂ β₃ h₁ h₂ h₃ hβ in
private theorem scalar_cocycle_calculation (P : C₂) :
    F₀.map (c.hom.app P) ≫ κ₃.hom.app P =
      κ₂.hom.app (T₁.obj P) ≫ S₂.map (κ₁.hom.app P) ≫ d.hom.app (F₂.obj P) := by
  have hi : d.hom.app (F₂.obj P) ≫ κ₃.inv.app P ≫ F₀.map (c.inv.app P) =
      S₂.map (κ₁.inv.app P) ≫ κ₂.inv.app (T₁.obj P) := by
    dsimp only [Functor.comp_obj] at *
    apply (b₂.homEquiv _ _).injective
    apply (b₁.homEquiv _ _).injective
    rw [d_transpose]
    rw [b₃.homEquiv_naturality_right, h₃]
    rw [b₂.homEquiv_naturality_left, h₂,
      b₁.homEquiv_naturality_right, h₁]
    have hn₃ := β₃.hom.naturality (c.inv.app P)
    dsimp only [Functor.comp_map] at hn₃
    simp only [Category.assoc]
    rw [← reassoc_of% hn₃]
    rw [← F₂.map_comp_assoc]
    have hc := c_transpose P (T₂.obj (T₁.obj P)) (c.inv.app P)
    rw [Iso.hom_inv_id_app] at hc
    dsimp only [Functor.comp_obj] at hc
    rw [Adjunction.homEquiv_id, Adjunction.homEquiv_unit] at hc
    have hh := hβ (T₂.obj (T₁.obj P))
    have hn₁ := β₁.hom.naturality (a₂.unit.app (T₁.obj P))
    dsimp only [Functor.comp_map] at hn₁
    rw [Adjunction.homEquiv_unit] at hc
    simp only [Category.assoc] at hc
    simp only [Functor.map_comp, Category.assoc]
    rw [← hh]
    simp only [← F₂.map_comp_assoc]
    rw [← hc, F₂.map_comp_assoc]
    rw [reassoc_of% hn₁]
  let L := F₀.mapIso (c.app P) ≪≫ κ₃.app P
  let R := κ₂.app (T₁.obj P) ≪≫ S₂.mapIso (κ₁.app P) ≪≫ d.app (F₂.obj P)
  have hi' : L.inv = R.inv := by
    apply (cancel_epi (d.hom.app (F₂.obj P))).mp
    simpa only [L, R, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc,
      Iso.hom_inv_id_app_assoc] using hi
  have he : L.symm = R.symm := Iso.ext hi'
  exact congrArg Iso.hom (congrArg Iso.symm he)

end ScalarCocycleCalculation

namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush) (A : Data.{c, v, r} J B τ)
  (G : Geometry.{c, v, r} J B τ A J' uInv uPush adjSet)

private def ordinaryRestrictionComposition {k m n : ℕ} (h : n ≤ m) (j : m ≤ k) :=
  (restrictionComposition_existsUnique.{c, v, max c v r} J B τ h j).exists.choose

set_option backward.isDefEq.respectTransparency true in
private theorem ordinaryRestrictionComposition_hom_underlying
    {k m n : ℕ} (h : n ≤ m) (j : m ≤ k) (M : Mod.{c, v, max c v r} J (B n)) :
    (underlying.{c, v, r} J (B k)).map
      ((ordinaryRestrictionComposition.{c, v, r} J B τ h j).hom.app M) =
      𝟙 ((underlying.{c, v, r} J (B n)).obj M) := by
  ext U x
  exact congrFun (eq_of_heq
    ((restrictionComposition_existsUnique.{c, v, max c v r} J B τ h j).exists.choose_spec
      M U)) x

set_option backward.isDefEq.respectTransparency true in
private theorem ordinaryRestrictionComposition_inv_underlying
    {k m n : ℕ} (h : n ≤ m) (j : m ≤ k) (M : Mod.{c, v, max c v r} J (B n)) :
    (underlying.{c, v, r} J (B k)).map
      ((ordinaryRestrictionComposition.{c, v, r} J B τ h j).inv.app M) =
      𝟙 ((underlying.{c, v, r} J (B n)).obj M) := by
  have he := (underlying.{c, v, r} J (B k)).mapIso
    ((ordinaryRestrictionComposition.{c, v, r} J B τ h j).app M) |>.hom_inv_id
  change (underlying.{c, v, r} J (B k)).map
      ((ordinaryRestrictionComposition.{c, v, r} J B τ h j).hom.app M) ≫ _ = _ at he
  erw [ordinaryRestrictionComposition_hom_underlying, Category.id_comp] at he
  exact he

set_option backward.isDefEq.respectTransparency true in
private theorem ordinary_restriction_cocycle {k m n : ℕ} (h : n ≤ m) (j : m ≤ k)
    (M : Mod.{c, v, max c v r} J (B n)) :
    (G.inverseImage k).modules.map
        ((ordinaryRestrictionComposition.{c, v, r} J B τ h j).inv.app M) ≫
      (G.restrictionPullback j).hom.app ((res (coefficientMap J B τ h)).obj M) ≫
      (res (coefficientMap J' G.coefficients G.coefficientTransition j)).map
        ((G.restrictionPullback h).hom.app M) =
    (G.restrictionPullback (h.trans j)).hom.app M ≫
      (ordinaryRestrictionComposition.{c, v, r} J' G.coefficients
        G.coefficientTransition h j).inv.app
        ((G.inverseImage n).modules.obj M) := by
  apply (underlying.{c, v, r} J' (G.coefficients k)).map_injective
  apply (cancel_mono ((G.inverseImage n).moduleUnderlying.hom.app M)).mp
  simp only [Functor.map_comp]
  erw [Category.assoc, Category.assoc]
  have hh := G.restrictionPullback_underlying h M
  have hj := G.restrictionPullback_underlying j ((res (coefficientMap J B τ h)).obj M)
  have hq := ordinaryRestrictionComposition_inv_underlying.{c, v, r} J' G.coefficients
    G.coefficientTransition h j ((G.inverseImage n).modules.obj M)
  have he : (underlying.{c, v, r} J' (G.coefficients k)).map
      ((res (coefficientMap J' G.coefficients G.coefficientTransition j)).map
        ((G.restrictionPullback h).hom.app M)) =
      (underlying.{c, v, r} J' (G.coefficients m)).map
        ((G.restrictionPullback h).hom.app M) := rfl
  rw [he]
  erw [hh, hj]
  rw [hq]
  have hn := (G.inverseImage k).moduleUnderlying.hom.naturality
    ((ordinaryRestrictionComposition.{c, v, r} J B τ h j).inv.app M)
  dsimp only [Functor.comp_map] at hn
  have hmap : uInv.map ((underlying.{c, v, r} J (B k)).map
      ((ordinaryRestrictionComposition.{c, v, r} J B τ h j).inv.app M)) =
      𝟙 (uInv.obj ((underlying.{c, v, r} J (B n)).obj M)) := by
    rw [ordinaryRestrictionComposition_inv_underlying]
    exact uInv.map_id _
  have hn' := hn.trans (congrArg
    ((G.inverseImage k).moduleUnderlying.hom.app
      ((res (coefficientMap J B τ (h.trans j))).obj M) ≫ ·) hmap)
  have hn'' : (underlying.{c, v, r} J' (G.coefficients k)).map
      ((G.inverseImage k).modules.map
        ((ordinaryRestrictionComposition.{c, v, r} J B τ h j).inv.app M)) ≫
      (G.inverseImage k).moduleUnderlying.hom.app
        ((res (coefficientMap J B τ j)).obj ((res (coefficientMap J B τ h)).obj M)) =
      (G.inverseImage k).moduleUnderlying.hom.app
        ((res (coefficientMap J B τ (h.trans j))).obj M) := by
    exact hn'.trans (Category.comp_id _)
  refine hn''.trans ?_
  refine (G.restrictionPullback_underlying (h.trans j) M).symm.trans ?_
  exact congrArg (fun f ↦ f ≫ (G.inverseImage n).moduleUnderlying.hom.app M)
    (Category.comp_id _).symm

private def derivedRestrictionPullback {m n : ℕ} (h : n ≤ m) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (G.restrictionPullback h) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

set_option backward.isDefEq.respectTransparency true in
private theorem derived_restriction_cocycle {k m n : ℕ} (h : n ≤ m) (j : m ≤ k)
    (M : D.{c, v, max c v r} J (B n)) :
    (derivedExact.{c, v, max c v r, c, v} J J' (B k) (G.coefficients k)
        (G.inverseImage k).modules).map
        ((restrictionComposition.{c, v, max c v r} J B τ h j).inv.app M) ≫
      (derivedRestrictionPullback.{c, v, r} J B τ J' uInv uPush adjSet A G j).hom.app
        ((resD (coefficientMap J B τ h)).obj M) ≫
      (resD (coefficientMap J' G.coefficients G.coefficientTransition j)).map
        ((derivedRestrictionPullback.{c, v, r} J B τ J' uInv uPush adjSet A G h).hom.app M) =
    (derivedRestrictionPullback.{c, v, r} J B τ J' uInv uPush adjSet A G (h.trans j)).hom.app M ≫
      (restrictionComposition.{c, v, max c v r} J' G.coefficients
        G.coefficientTransition h j).inv.app
        ((derivedExact.{c, v, max c v r, c, v} J J' (B n) (G.coefficients n)
          (G.inverseImage n).modules).obj M) := by
  have hd := Functor.mapDerivedCategorySquareIso_comp
    (res (coefficientMap J B τ h)) (res (coefficientMap J B τ j))
    (res (coefficientMap J B τ (h.trans j)))
    (res (coefficientMap J' G.coefficients G.coefficientTransition h))
    (res (coefficientMap J' G.coefficients G.coefficientTransition j))
    (res (coefficientMap J' G.coefficients G.coefficientTransition (h.trans j)))
    (G.inverseImage n).modules (G.inverseImage m).modules (G.inverseImage k).modules
    (G.restrictionPullback h) (G.restrictionPullback j)
    (G.restrictionPullback (h.trans j))
    (ordinaryRestrictionComposition.{c, v, r} J B τ h j).symm
    (ordinaryRestrictionComposition.{c, v, r} J' G.coefficients G.coefficientTransition h j).symm
    (ordinary_restriction_cocycle.{c, v, r} J B τ J' uInv uPush adjSet A G h j)
  have he := congrArg (fun e ↦ e.hom.app M) hd
  simpa only [derivedRestrictionPullback, restrictionComposition, ordinaryRestrictionComposition,
    Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc, derivedExact, resD] using he

/-- The scalar-association comparisons respect direct and successive quotient maps.
Source: Stacks 03EL, 0D6D and 07A4
(blueprint: lem-pur-geometric-scalar-association-cocycle).

Proof: the ordinary restriction-composition comparison is the identity on section
carriers. The inverse-image/restriction comparison is the identity under the
specified underlying-sheaf identifications. Therefore its direct and two successive
paths agree with restriction composition: apply the faithful underlying-sheaf
functor, substitute the three underlying equations and cancel the inverse-image
identifications. Localizing this equality on the ordinary module categories gives
the same equality of derived restriction comparisons. Transpose it under the two
scalar adjunctions. The scalarComposition_transpose equations identify the source
and target reassociations, and coefficientPullback_transpose identifies each
inverse scalar-association map. Naturality of the units and of restriction pullback
makes these the two transposed paths; cancel the adjunction bijections and the
invertible association maps. This gives the displayed equality. The argument
uses actual natural transformations before localization, so it does not require
faithfulness of derived evaluation. Equal indices and zero rings obey the same
identity-on-underlying-sheaves calculation. -/
theorem geometricScalarAssociationCocycle : ∀ {k m n : ℕ} (h : n ≤ m) (j : m ≤ k)
    (P : D.{c, v, max c v r} J (B k)),
    (derivedExact.{c, v, max c v r, c, v} J J' (B n) (G.coefficients n) (G.inverseImage
      n).modules).map
        ((A.scalarComposition h j).hom.app P) ≫
        (G.coefficientPullback (h.trans j)).hom.app P =
      (G.coefficientPullback h).hom.app ((A.scalar j).T.obj P) ≫
        (G.target.scalar h).T.map ((G.coefficientPullback j).hom.app P) ≫
        (G.target.scalarComposition h j).hom.app
          ((derivedExact.{c, v, max c v r, c, v} J J' (B k) (G.coefficients k) (G.inverseImage
            k).modules).obj P) := by
  intro k m n h j P
  exact scalar_cocycle_calculation
    (A.scalar j).adjunction (A.scalar h).adjunction (A.scalar (h.trans j)).adjunction
    (G.target.scalar j).adjunction (G.target.scalar h).adjunction
    (G.target.scalar (h.trans j)).adjunction
    (derivedExact J J' (B n) (G.coefficients n) (G.inverseImage n).modules)
    (derivedExact J J' (B m) (G.coefficients m) (G.inverseImage m).modules)
    (derivedExact J J' (B k) (G.coefficients k) (G.inverseImage k).modules)
    (A.scalarComposition h j) (G.target.scalarComposition h j)
    (restrictionComposition J B τ h j)
    (restrictionComposition J' G.coefficients G.coefficientTransition h j)
    (A.scalarComposition_transpose h j) (G.target.scalarComposition_transpose h j)
    (G.coefficientPullback j) (G.coefficientPullback h)
    (G.coefficientPullback (h.trans j))
    (derivedRestrictionPullback.{c, v, r} J B τ J' uInv uPush adjSet A G j)
    (derivedRestrictionPullback.{c, v, r} J B τ J' uInv uPush adjSet A G h)
    (derivedRestrictionPullback.{c, v, r} J B τ J' uInv uPush adjSet A G (h.trans j))
    (G.coefficientPullback_transpose j) (G.coefficientPullback_transpose h)
    (G.coefficientPullback_transpose (h.trans j))
    (derived_restriction_cocycle.{c, v, r} J B τ J' uInv uPush adjSet A G h j) P

end WeilConjectures.SemilinearSections
