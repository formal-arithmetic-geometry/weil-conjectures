/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Composition of base change for unbounded module exchange

Source: blueprint, sec-smooth-purity, sk-prop-sf-cbc,
lem-fin-radicial-exchange-descent, proof, compatibility with composition;
main-20261015, sec-six-functors-basics, the same proof;
Stacks Project, Tags 07A7 and 0E46
(blueprint: lem-fin-module-exchange-composite-base-change).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The module inverse-image composition isomorphism `c^Λ_{a,b}` of the node.
It is the inverse of `upperStarComp`, applied termwise and descended to the unbounded
localizations, with `mapDerivedCategoryCompIso` identifying the two termwise functors.
Thus its direction is `b⁻¹ a⁻¹ ≅ (b ≫ a)⁻¹`.
Source: blueprint, lem-fin-radicial-exchange-descent, composition compatibility;
Stacks Project, Tag 07A7 (blueprint: lem-fin-module-exchange-composite-base-change). -/
noncomputable def moduleInverseImageCompIso
    (Λ : Type (u + 1)) [CommRing Λ] {U V W : Scheme.{u}}
    (a : V ⟶ W) (b : U ⟶ V) :
    D(upperStar (ModuleCat.{u + 1} Λ) a) ⋙ D(upperStar (ModuleCat.{u + 1} Λ) b) ≅
      D(upperStar (ModuleCat.{u + 1} Λ) (b ≫ a)) :=
  (Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} Λ) b a) ≪≫
    Functor.mapDerivedCategoryCompIso _ _).symm

namespace ModuleExchangePasting

-- Keep the pasting calculation abstract so it never unfolds a derived inverse image.
-- This is the calculus of EtaleDerivedBaseChangeLocalTransport, specialized below to modules.

universe v

variable {C : Scheme.{u} → Type v} [∀ X, Category.{u + 1} (C X)]

private structure DerivedSystem (C : Scheme.{u} → Type v) [∀ X, Category.{u + 1} (C X)] where
  L : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → (C Y ⥤ C X)
  R : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → (C X ⥤ C Y)
  adj : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), L f ⊣ R f
  ucomp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (_hfg : fg = f ≫ g), L fg ≅ L g ⋙ L f
  assoc : ∀ {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h),
    (ucomp f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom ≫
      Functor.whiskerRight (ucomp g h gh hgh).hom (L f) =
    (ucomp fg h fgh hfgh).hom ≫ Functor.whiskerLeft (L h) (ucomp f g fg hfg).hom

private noncomputable abbrev upperComp (sys : DerivedSystem C) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :=
  sys.ucomp f g fg hfg

private theorem comp_assoc' (sys : DerivedSystem C) {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z) (hfg : fg = f ≫ g) (hgh : gh = g ≫ h)
    (hfgh : fgh = fg ≫ h) :
    (upperComp sys f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom ≫
        Functor.whiskerRight (upperComp sys g h gh hgh).hom (sys.L f) =
      (upperComp sys fg h fgh hfgh).hom ≫
        Functor.whiskerLeft (sys.L h) (upperComp sys f g fg hfg).hom := by
  exact sys.assoc f g h fg gh fgh hfg hgh hfgh

@[reassoc]
private theorem map_comp_hom_app_upperStarComp_inv_app
    (sys : DerivedSystem C) {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (G : C Z) :
    (sys.L f).map ((upperComp sys g h gh hgh).hom.app G) ≫
        (upperComp sys f g fg hfg).inv.app ((sys.L h).obj G) =
      (upperComp sys f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).inv.app G ≫
        (upperComp sys fg h fgh hfgh).hom.app G := by
  have key := NatTrans.congr_app (comp_assoc' sys f g h fg gh fgh hfg hgh hfgh) G
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj] at key
  simpa using CategoryTheory.comp_inv_eq_inv_comp_of_eq _ _ _ _ key

@[reassoc]
private theorem comp_hom_app_map_upperStarComp_inv_app
    (sys : DerivedSystem C) {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (G : C Z) :
    (upperComp sys f g fg hfg).hom.app ((sys.L h).obj G) ≫
        (sys.L f).map ((upperComp sys g h gh hgh).inv.app G) =
      (upperComp sys fg h fgh hfgh).inv.app G ≫
        (upperComp sys f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app G := by
  have key := NatTrans.congr_app (comp_assoc' sys f g h fg gh fgh hfg hgh hfgh) G
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj] at key
  have := CategoryTheory.comp_inv_eq_inv_comp_of_eq _ _ _ _ key.symm
  rwa [NatIso.inv_hom_app, ← Functor.map_inv, NatIso.inv_hom_app] at this

@[irreducible]
private noncomputable def square (sys : DerivedSystem C)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) : sys.L g ⋙ sys.L f' ≅ sys.L f ⋙ sys.L g' :=
  (upperComp sys f' g (g' ≫ f) sq.w).symm ≪≫ upperComp sys g' f (g' ≫ f) rfl

private noncomputable abbrev bcSquare (sys : DerivedSystem C)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) : TwoSquare (sys.R f) (sys.L g') (sys.L g) (sys.R f') :=
  mateEquiv (sys.adj f) (sys.adj f')
    (TwoSquare.mk (sys.L g) (sys.L f) (sys.L f') (sys.L g') (square sys sq).hom)

@[irreducible]
private noncomputable def bc (sys : DerivedSystem C)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) : sys.R f ⋙ sys.L g ⟶ sys.L g' ⋙ sys.R f' :=
  (bcSquare sys sq).natTrans

variable {X'' X' X Y'' Y' Y : Scheme.{u}} {g'' : X'' ⟶ X'} {g' : X' ⟶ X}
  {f'' : X'' ⟶ Y''} {f' : X' ⟶ Y'} {f : X ⟶ Y} {h : Y'' ⟶ Y'} {g : Y' ⟶ Y}

open scoped TwoSquare in
private theorem square_paste_horiz (sys : DerivedSystem C) (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g'' f'' f' h) (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) :
    (square sys sq).hom =
      Functor.whiskerRight (upperComp sys h g (h ≫ g) rfl).hom (sys.L f'') ≫
        (TwoSquare.mk (sys.L g) (sys.L f) (sys.L f') (sys.L g') (square sys sq₁).hom ≫ₕ
          TwoSquare.mk (sys.L h) (sys.L f') (sys.L f'') (sys.L g'') (square sys sq₂).hom).natTrans ≫
        Functor.whiskerLeft (sys.L f) (upperComp sys g'' g' (g'' ≫ g') rfl).inv := by
  refine NatTrans.ext (funext fun F => ?_)
  simp only [square, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.comp_obj, TwoSquare.hComp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [map_comp_hom_app_upperStarComp_inv_app_assoc sys f'' h g (g'' ≫ f')
    (h ≫ g) ((g'' ≫ g') ≫ f) sq₂.w rfl (by rw [Category.assoc, sq₁.w, Category.assoc]),
    comp_hom_app_map_upperStarComp_inv_app_assoc sys g'' f' g (g'' ≫ f')
    (g' ≫ f) ((g'' ≫ g') ≫ f) rfl sq₁.w (by rw [Category.assoc, sq₁.w, Category.assoc]),
    map_comp_hom_app_upperStarComp_inv_app sys g'' g' f (g'' ≫ g') (g' ≫ f)
    ((g'' ≫ g') ≫ f) rfl rfl rfl, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]

open scoped TwoSquare in
private theorem bcSquare_paste_horiz (sys : DerivedSystem C) (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g'' f'' f' h)
    (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) :
    bcSquare sys sq =
      ((bcSquare sys sq₁ ≫ᵥ bcSquare sys sq₂).whiskerRight
        (upperComp sys h g (h ≫ g) rfl).hom).whiskerLeft
        (upperComp sys g'' g' (g'' ≫ g') rfl).inv := by
  have h1 : TwoSquare.mk (sys.L (h ≫ g)) (sys.L f) (sys.L f'') (sys.L (g'' ≫ g'))
      (square sys sq).hom =
      ((TwoSquare.mk (sys.L g) (sys.L f) (sys.L f') (sys.L g') (square sys sq₁).hom ≫ₕ
        TwoSquare.mk (sys.L h) (sys.L f') (sys.L f'') (sys.L g'') (square sys sq₂).hom).whiskerTop
          (upperComp sys h g (h ≫ g) rfl).hom).whiskerBottom
          (upperComp sys g'' g' (g'' ≫ g') rfl).inv := by
    refine TwoSquare.ext _ _ fun F => ?_
    have := NatTrans.congr_app (square_paste_horiz sys sq₁ sq₂ sq) F
    simpa only [TwoSquare.whiskerBottom_app, TwoSquare.whiskerTop_app, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] using this
  rw [bcSquare, h1, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp]

private theorem bc_paste_horiz_app (sys : DerivedSystem C) (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g'' f'' f' h)
    (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) (F : C X) :
    (bc sys sq).app F =
      (upperComp sys h g (h ≫ g) rfl).hom.app ((sys.R f).obj F) ≫
        (sys.L h).map ((bc sys sq₁).app F) ≫
        (bc sys sq₂).app ((sys.L g').obj F) ≫
        (sys.R f'').map ((upperComp sys g'' g' (g'' ≫ g') rfl).inv.app F) := by
  have := NatTrans.congr_app (bcSquare_paste_horiz sys sq₁ sq₂ sq) F
  simp only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.vComp_app,
    Functor.comp_obj, Category.assoc] at this
  simp only [bc]
  exact this

private noncomputable def L (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  D(upperStar (ModuleCat.{u + 1} Λ) f)
private noncomputable def R (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  R(lowerStar (ModuleCat.{u + 1} Λ) f)
private noncomputable def adj (Λ : Type (u + 1)) [CommRing Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : L Λ f ⊣ R Λ f :=
  mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
private noncomputable def comp (Λ : Type (u + 1)) [CommRing Λ]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) : L Λ fg ≅ L Λ g ⋙ L Λ f :=
  Functor.mapDerivedCategoryNatIso (upperStarComp (ModuleCat.{u + 1} Λ) f g fg hfg) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

-- Derive the ordinary associativity equation using the localization coherence API.
private theorem comp_assoc (Λ : Type (u + 1)) [CommRing Λ] {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h) :
    (comp Λ f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom ≫
      Functor.whiskerRight (comp Λ g h gh hgh).hom (L Λ f) =
    (comp Λ fg h fgh hfgh).hom ≫ Functor.whiskerLeft (L Λ h) (comp Λ f g fg hfg).hom := by
  let A := ModuleCat.{u + 1} Λ
  let α₁ := upperStarComp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])
  let α₂ := upperStarComp A g h gh hgh
  let α₃ := upperStarComp A fg h fgh hfgh
  let α₄ := upperStarComp A f g fg hfg
  have heq : α₁ ≪≫ Functor.isoWhiskerRight α₂ (upperStar A f) =
      α₃ ≪≫ Functor.isoWhiskerLeft (upperStar A h) α₄ := by
    ext : 1
    exact upperStarComp_assoc' A f g h fg gh fgh hfg hgh hfgh
  have hmap := congrArg (fun e => (Functor.mapDerivedCategoryNatIso e).hom) heq
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hmap
  simp only [comp, Iso.trans_hom, Functor.whiskerRight_comp, Functor.whiskerLeft_comp,
    Category.assoc]
  simp only [L]
  change (Functor.mapDerivedCategoryNatIso α₁).hom ≫ _ =
    (Functor.mapDerivedCategoryNatIso α₃).hom ≫ _
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerRight
      α₂ (upperStar A f)),
    ← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft
      (upperStar A h) α₄)]
  rw [← (Functor.mapDerivedCategoryCompIso_assoc
    (upperStar A h) (upperStar A g) (upperStar A f))]
  rw [← Category.assoc, hmap, Category.assoc]

private noncomputable def sys (Λ : Type (u + 1)) [CommRing Λ] : DerivedSystem
    (fun X : Scheme.{u} => DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) where
  L := @L Λ _
  R := @R Λ _
  adj := @adj Λ _
  ucomp := @comp Λ _
  assoc := @comp_assoc Λ _

private theorem square_eq (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) :
    square (sys Λ) sq = exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq := by
  apply Iso.ext
  simp only [square, upperComp, sys, comp, exactDerivedSquareUpperStarIso,
    squareUpperStarIso, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    Category.assoc]

private theorem bc_eq (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) :
    bc (sys Λ) sq = exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq := by
  unfold bc bcSquare
  rw [square_eq]
  rfl

end ModuleExchangePasting

/-- Horizontal pasting for the canonical unbounded module exchange, together with its
componentwise isomorphism criterion. The two given squares are Cartesian with chosen
pullback identifications; their outer rectangle is the horizontal composite of their
underlying commutative squares. The comparison maps are exactly `c^Λ` above.
Source: blueprint, lem-fin-radicial-exchange-descent, composition compatibility;
Stacks Project, Tags 07A7 and 0E46
(blueprint: lem-fin-module-exchange-composite-base-change).

Proof: On module sheaves the inverse-image square comparison for the pasted rectangle
is the composite of the two comparisons, conjugated by the composition isomorphisms
`upperStarComp`. Apply these isomorphisms termwise to complexes. Naturality makes them
cochain maps, and exactness preserves quasi-isomorphisms, so localization descends the
same pasting identity, using `mapDerivedCategoryCompIso`. Take mates under the canonical
derived adjunctions for f, f₁ and f₂. Horizontal composition of mates identifies the mate
of this pasted comparison with the two exchanges, whiskered by inverse image on the
left and on the right. The two outside comparisons give precisely the inverse of
`c^Λ_{g,k}` and `c^Λ_{g₁,k₁}` in the formula. This proves equality of natural
transformations, not just equality on objects. Evaluating at K gives the displayed
four-arrow composite. Its outside arrows are isomorphisms, also after applying Rf₂*,
so cancelling them proves the equivalence of isomorphism assertions. The outer square
is Cartesian by pullback pasting, although the mate identity itself only uses its
underlying commutative square. -/
theorem moduleExchange_composite_baseChange
    (Λ : Type (u + 1)) [CommRing Λ]
    {X X₁ X₂ Y Y₁ Y₂ : Scheme.{u}}
    {f : X ⟶ Y} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    {g : Y₁ ⟶ Y} {g₁ : X₁ ⟶ X} {k : Y₂ ⟶ Y₁} {k₁ : X₂ ⟶ X₁}
    (sq₁ : ChosenCartesianSquare g₁ f₁ f g)
    (sq₂ : ChosenCartesianSquare k₁ f₂ f₁ k) :
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ)
        (sq₂.toCommSq.horiz_comp sq₁.toCommSq) =
      Functor.whiskerLeft R(lowerStar (ModuleCat.{u + 1} Λ) f)
          (moduleInverseImageCompIso Λ g k).inv ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq₁.toCommSq)
          D(upperStar (ModuleCat.{u + 1} Λ) k) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft D(upperStar (ModuleCat.{u + 1} Λ) g₁)
          (exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq₂.toCommSq) ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (moduleInverseImageCompIso Λ g₁ k₁).hom
          R(lowerStar (ModuleCat.{u + 1} Λ) f₂)) ∧
    ∀ K : DerivedCategoryModule Λ X,
      IsIso ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ)
          (sq₂.toCommSq.horiz_comp sq₁.toCommSq)).app K) ↔
        IsIso (D(upperStar (ModuleCat.{u + 1} Λ) k).map
            ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq₁.toCommSq).app K) ≫
          (exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq₂.toCommSq).app
            (D(upperStar (ModuleCat.{u + 1} Λ) g₁).obj K)) := by
  have happ (K : DerivedCategoryModule Λ X) :=
    ModuleExchangePasting.bc_paste_horiz_app (ModuleExchangePasting.sys Λ)
      sq₁.toCommSq sq₂.toCommSq (sq₂.toCommSq.horiz_comp sq₁.toCommSq) K
  simp only [ModuleExchangePasting.bc_eq] at happ
  constructor
  · refine NatTrans.ext (funext fun K ↦ ?_)
    rw [happ K]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Functor.associator_hom_app, Category.id_comp,
      Functor.comp_obj]
    rfl
  · intro K
    rw [happ K]
    rw [isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff]
    rfl

end AlgebraicGeometry.Etale
