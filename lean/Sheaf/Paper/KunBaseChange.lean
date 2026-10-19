/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition
public import WeilConjectures.SixFunctors.BaseChange.Derived
import Sheaf.Paper.ExchangeIdentityPasting
import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Horizontal

/-!
# Further base change of the derived exchange map

Source: blueprint sec-smooth-purity, sk-prop-sf-kunneth-ordinary,
node lem-kun-bc-base-change; Stacks Project, Remark 0E47
(blueprint: lem-kun-bc-base-change).

The auxiliary maps are the actual maps of fibre products and the inverse-image
composition comparisons appearing in clause (2), with abelian-group coefficients.
The three statements give clause (1), the square in clause (2), and its conditional
identification when both vertical arrows are invertible.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The induced right-hand map of the base-change cube, with its actual fibre-product data.
Source: blueprint lem-kun-bc-base-change, clause (2), the arrow `f̃'`
(blueprint: lem-kun-bc-base-change). -/
noncomputable def kunBaseChangeRightMap
    {X' Y' Y Z : Scheme.{u}} (f' : X' ⟶ Y') (g : Y' ⟶ Y) (w : Z ⟶ Y) :
    pullback (f' ≫ g) w ⟶ pullback g w :=
  pullback.map (f' ≫ g) w g w f' (𝟙 Z) (𝟙 Y)
    (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The induced top map of the base-change cube, from the original square's equality.
Source: blueprint lem-kun-bc-base-change, clause (2), the arrow `g̃'`
(blueprint: lem-kun-bc-base-change). -/
noncomputable def kunBaseChangeTopMap
    {X' X Y' Y Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) (w : Z ⟶ Y) :
    pullback (f' ≫ g) w ⟶ pullback f w :=
  pullback.map (f' ≫ g) w f w g' (𝟙 Z) (𝟙 Y)
    ((Category.comp_id _).trans sq.w.symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- The comparison square `C`, using the first projection equation for `pullback.map`.
Source: blueprint lem-kun-bc-base-change, clause (2)
(blueprint: lem-kun-bc-base-change). -/
noncomputable abbrev kunBaseChangeComparisonSquare
    {X' Y' Y Z : Scheme.{u}} (f' : X' ⟶ Y') (g : Y' ⟶ Y) (w : Z ⟶ Y) :
    CommSq (pullback.fst (f' ≫ g) w) (kunBaseChangeRightMap f' g w)
      f' (pullback.fst g w) :=
  ⟨(pullback.lift_fst _ _ _).symm⟩

/-- The base-changed square; its commutativity is the two second-projection equations.
Source: blueprint lem-kun-bc-base-change, clause (2)
(blueprint: lem-kun-bc-base-change). -/
noncomputable abbrev kunBaseChangedSquare
    {X' X Y' Y Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) (w : Z ⟶ Y) :
    CommSq (kunBaseChangeTopMap sq w) (kunBaseChangeRightMap f' g w)
      (pullback.snd f w) (pullback.snd g w) :=
  ⟨(pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm⟩

/-- The canonical source comparison `s`, using `gb = w g̃` from the fibre product.
The upstream composition isomorphism is the inverse of the node's `cᴰ`.
Source: blueprint lem-kun-bc-base-change, clause (2)
(blueprint: lem-kun-bc-base-change). -/
noncomputable def kunBaseChangeSourceIso
    {Y' Y Z : Scheme.{u}} (g : Y' ⟶ Y) (w : Z ⟶ Y) :
    (g)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus ⋙
        (pullback.fst g w)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus ≅
      (w)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus ⋙
        (pullback.snd g w)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus :=
  (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} (pullback.fst g w) g).symm ≪≫
    upperStarCompDerivedPlus AddCommGrpCat.{u + 1} (pullback.snd g w) w
      (pullback.fst g w ≫ g) (pullback.condition (f := g) (g := w))

/-- The canonical target comparison `t`, using `g' c = a g̃'` from `pullback.map`.
Source: blueprint lem-kun-bc-base-change, clause (2)
(blueprint: lem-kun-bc-base-change). -/
noncomputable def kunBaseChangeTargetIso
    {X' X Y' Y Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) (w : Z ⟶ Y) :
    (g')^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus ⋙
        (pullback.fst (f' ≫ g) w)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus ≅
      (pullback.fst f w)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus ⋙
        (kunBaseChangeTopMap sq w)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus :=
  (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} (pullback.fst (f' ≫ g) w) g').symm ≪≫
    upperStarCompDerivedPlus AddCommGrpCat.{u + 1} (kunBaseChangeTopMap sq w)
      (pullback.fst f w) (pullback.fst (f' ≫ g) w ≫ g')
      (pullback.lift_fst _ _ _).symm

/-- The left vertical comparison, namely `g̃⁻¹(Ex_B) ∘ s`.
Source: blueprint lem-kun-bc-base-change, clause (2)
(blueprint: lem-kun-bc-base-change). -/
noncomputable def kunBaseChangeLeft
    {X Y' Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (w : Z ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  (kunBaseChangeSourceIso g w).hom.app
      ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj K) ≫
    (pullback.snd g w)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus.map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (IsPullback.of_hasPullback f w).toCommSq).app K)

/-- The right vertical comparison, namely `Rf̃'_*(t) ∘ Ex_C`.
Source: blueprint lem-kun-bc-base-change, clause (2)
(blueprint: lem-kun-bc-base-change). -/
noncomputable def kunBaseChangeRight
    {X' X Y' Y Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) (w : Z ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (kunBaseChangeComparisonSquare f' g w)).app
      ((g')^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus.obj K) ≫
    (kunBaseChangeRightMap f' g w)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map
      ((kunBaseChangeTargetIso sq w).hom.app K)

/-- Clause (1): the exchange map for a successive base change is the pasted composite.
Source: blueprint lem-kun-bc-base-change; Stacks Project, Remark 0E47
(blueprint: lem-kun-bc-base-change).

Proof (node steps 1 and 2). The two fibre-product universal properties identify
`X'' = X' ×_{Y'} Y''` with `X ×_Y Y''`, with top projection `v ≫ g'`.
Use the chosen Cartesian identification to apply horizontal pasting, clause (2) of
lem-weil-pbc-exchange-identity-pasting, to the original and the further squares.
Evaluate at K. The inverse of cᴰ at Rf_*K, pullback of the first exchange, the
second exchange at g'⁻¹K, and Rf''_* of cᴰ are exactly the four displayed factors.
No exchange factor is cancelled or assumed to be invertible. -/
theorem kun_bc_base_change
    {X' X Y' Y Y'' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) (u₀ : Y'' ⟶ Y')
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      ((IsPullback.of_hasPullback f' u₀).paste_horiz
        (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback
          sq.hom_fst sq.hom_snd)).toCommSq).app K =
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} u₀ g).hom.app
          ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj K) ≫
        (u₀)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus.map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K) ≫
        (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
          (IsPullback.of_hasPullback f' u₀).toCommSq).app
          ((g')^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus.obj K) ≫
        (pullback.snd f' u₀)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map
          ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
            (pullback.fst f' u₀) g').inv.app K) := by
  have h := derivedExchange_identity_pasting.{u}.2.1
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)
    (IsPullback.of_hasPullback f' u₀)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] using NatTrans.congr_app h K

private lemma derivedBaseChangeMapPlus_paste_horiz_app_eq
    {X'' X' X Y'' Y' Y : Scheme.{u}} {g'' : X'' ⟶ X'} {g' : X' ⟶ X}
    {f'' : X'' ⟶ Y''} {f' : X' ⟶ Y'} {f : X ⟶ Y}
    {h : Y'' ⟶ Y'} {g : Y' ⟶ Y}
    (sq₁ : CommSq g' f' f g) (sq₂ : CommSq g'' f'' f' h)
    (r : X'' ⟶ X) (hr : r = g'' ≫ g')
    (k : Y'' ⟶ Y) (hk : k = h ≫ g) (sq : CommSq r f'' f k)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K =
      (upperStarCompDerivedPlus AddCommGrpCat.{u + 1} h g k hk).hom.app
          ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj K) ≫
        (h)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus.map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₁).app K) ≫
        (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq₂).app
          ((g')^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus.obj K) ≫
        (f'')_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.map
          ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} g'' g' r hr).inv.app K) := by
  subst r
  subst k
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] using NatTrans.congr_app
      (derivedBaseChangeMapPlus_paste_horiz AddCommGrpCat.{u + 1} sq₁ sq₂ sq) K

private lemma cancel_pasting_comparisons
    {C D : Type*} [Category C] [Category D] (F : D ⥤ C)
    {U V W P R : C} {L M N : D}
    (c : U ≅ V) (e : U ≅ W) (d : L ≅ M) (t : L ≅ N)
    (p : V ⟶ P) (q : P ⟶ F.obj M) (r : W ⟶ R) (s : R ⟶ F.obj N)
    (h : c.hom ≫ p ≫ q ≫ F.map d.inv = e.hom ≫ r ≫ s ≫ F.map t.inv) :
    p ≫ q ≫ F.map (d.inv ≫ t.hom) = (c.inv ≫ e.hom ≫ r) ≫ s := by
  have hc := congrArg (fun z ↦ c.inv ≫ z ≫ F.map t.hom) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, ← F.map_comp,
    Iso.inv_hom_id, F.map_id, Category.comp_id] using hc

set_option maxHeartbeats 800000 in
-- Elaborating the two pasting equations involves several concrete derived functors.
/-- Clause (2): the four-corner base-change diagram commutes with both comparison arrows.
Source: blueprint lem-kun-bc-base-change; Stacks Project, Remark 0E47
(blueprint: lem-kun-bc-base-change).

Proof (node steps 3 and 4). The fibre-product universal properties show that B, C,
and the base-changed square are Cartesian, including empty fibre products. They
identify both outer rectangles, using gb = w g̃ and g'c = a g̃'. Apply the horizontal
pasting identity first to (square,C) and then to (B,base-changed square).
The outer exchange maps agree, since the chosen identifications have the same
projections. Postcompose by Rf̃'_* of the inverse of cᴰ for (a,g̃'), and precompose
by cᴰ for (g,b). Naturality, functoriality and the composition-isomorphism inverse
identities give Ex_C followed by Rf̃'_*(t) on the right, and s followed by g̃⁻¹(Ex_B)
and Ex of the base-changed square on the left. This is the asserted CommSq.
Neither vertical comparison is assumed invertible. -/
theorem kun_bc_base_change_cube
    {X' X Y' Y Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) (w : Z ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    CommSq
      ((pullback.fst g w)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K))
      (kunBaseChangeLeft f g w K) (kunBaseChangeRight sq w K)
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} (kunBaseChangedSquare sq w)).app
        ((pullback.fst f w)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus.obj K)) := by
  let outer : CommSq (pullback.fst (f' ≫ g) w ≫ g')
      (kunBaseChangeRightMap f' g w) f (pullback.fst g w ≫ g) :=
    ⟨by rw [Category.assoc, sq.w, ← Category.assoc,
      (kunBaseChangeComparisonSquare f' g w).w, Category.assoc]⟩
  have h₁ := derivedBaseChangeMapPlus_paste_horiz_app_eq sq.toCommSq
    (kunBaseChangeComparisonSquare f' g w) _ rfl _ rfl outer K
  have h₂ := derivedBaseChangeMapPlus_paste_horiz_app_eq
    (IsPullback.of_hasPullback f w).toCommSq (kunBaseChangedSquare sq w)
    _ (pullback.lift_fst _ _ _).symm _ (pullback.condition (f := g) (g := w)) outer K
  have h := h₁.symm.trans h₂
  have hc := cancel_pasting_comparisons
    (kunBaseChangeRightMap f' g w)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus
    ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} (pullback.fst g w) g).app
      ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj K))
    ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} (pullback.snd g w) w
      (pullback.fst g w ≫ g) (pullback.condition (f := g) (g := w))).app
      ((f)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj K))
    ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
      (pullback.fst (f' ≫ g) w) g').app K)
    ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} (kunBaseChangeTopMap sq w)
      (pullback.fst f w) (pullback.fst (f' ≫ g) w ≫ g')
      (pullback.lift_fst _ _ _).symm).app K) _ _ _ _ h
  constructor
  simpa only [kunBaseChangeLeft, kunBaseChangeRight, kunBaseChangeSourceIso,
    kunBaseChangeTargetIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Iso.app_hom, Iso.app_inv, Category.assoc] using hc

/-- The conditional identification in clause (2), when both vertical comparisons are isos.
Source: blueprint lem-kun-bc-base-change, final paragraph
(blueprint: lem-kun-bc-base-change).

Proof (node step 4, final sentences). Write the commutative square as top ≫ V = L ≫ H.
If L and V are isomorphisms, compose with V⁻¹ and cancel V ≫ V⁻¹. This yields
top = L ≫ H ≫ V⁻¹, the specified identification. In particular no invertibility
assumption is used in kun_bc_base_change_cube. -/
theorem kun_bc_base_change_identification
    {X' X Y' Y Z : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g) (w : Z ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    [IsIso (kunBaseChangeLeft f g w K)] [IsIso (kunBaseChangeRight sq w K)] :
    (pullback.fst g w)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K) =
      kunBaseChangeLeft f g w K ≫
        (derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} (kunBaseChangedSquare sq w)).app
          ((pullback.fst f w)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus.obj K) ≫
        inv (kunBaseChangeRight sq w K) := by
  apply (cancel_mono (kunBaseChangeRight sq w K)).1
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using
    (kun_bc_base_change_cube sq w K).w

end AlgebraicGeometry.Etale
