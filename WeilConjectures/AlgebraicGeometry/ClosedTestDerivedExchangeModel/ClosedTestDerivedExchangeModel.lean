/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedTestDerivedExchangeModel.ClosedTestDerivedExchangeMaps

import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction

import WeilConjectures.AlgebraicGeometry.ClosedTestSectionSteps.ClosedTestSectionLocalization
import WeilConjectures.AlgebraicGeometry.ClosedTestSectionSteps.ClosedTestClosedEvaluation
import WeilConjectures.AlgebraicGeometry.NonaffineClosedTestExchangeIdentification.NonaffineClosedTestExchangeIdentification

/-!
# The canonical derived exchange on closed lifted tests

Source: Stacks Project, Tags 09BL and 0D6F, and the unit--counit calculation
(blueprint: lem-sfb-closed-test-derived-exchange-model).

## Main definitions

* `exchange`: the specified derived adjunction mate.
* `testRestriction`: restriction along the actual closed test-fibre map.
* `restrictPush`: the coefficient comparison induced by the ordinary section identity.

## Main statements

* `closed_test_derived_exchange_model`: the two normalized derived isomorphisms.
* `closed_test_test_naturality`: compatibility with admissible test maps.
* `section_comparison_base_change_naturality`: compatibility with localization cubes.
* `derived_restriction_localization`: localization of canonical restriction.
* `closed_test_coefficient_naturality`: compatibility with actual coefficient maps.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The two section comparisons and the closed evaluation comparison respect every map
of admissible affine tests, with the maps induced by the specified closed-site functor.
Source: Tag 09BL (2), natural evaluation
(blueprint: lem-sfb-closed-test-derived-exchange-model).

Proof (step 8): the ordinary unit-section isomorphism commutes with affine-site maps.
The chain-section identity, the K-injective comparison units and the derived composition
constraints commute with these restrictions. Thus the same equality descends to D(Ab).
The defining normalizations of eLeft and eRight then give their test naturality. -/
theorem closed_test_test_naturality
    (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
    (V V' : (Spec (.of (A ⧸ I))).AffineProEt) (r : V' ⟶ V)
    [IsWContractibleRing Γ(V.left, ⊤)] [IsWContractibleRing Γ(V'.left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V').left, ⊤)] :
    TestNaturality Λ f ((Scheme.AffineProEt.closedSiteLift A I).map r).left
        (MorphismProperty.Over.w ((Scheme.AffineProEt.closedSiteLift A I).map r)) ∧
      TestNaturality Λ fZ r.left (MorphismProperty.Over.w r) ∧
      (∀ K : DerivedCategory.Plus
          (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of A))) Ab.{u + 1})
            (condensedRingObj Λ (Spec (.of A)))),
        (closedComparison Λ A I V).app K.obj ≫
            (sectionsArrow Λ r.left (MorphismProperty.Over.w r)).app
              ((pull Λ (closedMap A I)).obj K.obj) =
          (sectionsArrow Λ ((Scheme.AffineProEt.closedSiteLift A I).map r).left
              (MorphismProperty.Over.w ((Scheme.AffineProEt.closedSiteLift A I).map r))).app
                K.obj ≫ (closedComparison Λ A I V').app K.obj) := by
  have hw (T : (Spec (.of (A ⧸ I))).AffineProEt) : WeaklyEtale T.hom :=
    proAffineEtale_le_weaklyEtale _ T.prop
  have hwLift (T : (Spec (.of (A ⧸ I))).AffineProEt) :
      WeaklyEtale ((Scheme.AffineProEt.closedSiteLift A I).obj T).hom :=
    proAffineEtale_le_weaklyEtale _ ((Scheme.AffineProEt.closedSiteLift A I).obj T).prop
  have := hw V
  have := hw V'
  have := hwLift V
  have := hwLift V'
  refine ⟨?_, ?_, ?_⟩
  · exact ClosedTestSectionSteps.proetale_section_localization Λ f
      ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom
      ((Scheme.AffineProEt.closedSiteLift A I).obj V').hom
      ((Scheme.AffineProEt.closedSiteLift A I).map r).left
      (MorphismProperty.Over.w ((Scheme.AffineProEt.closedSiteLift A I).map r))
  · exact ClosedTestSectionSteps.proetale_section_localization Λ fZ V.hom V'.hom
      r.left (MorphismProperty.Over.w r)
  · intro K
    exact ClosedTestSectionSteps.closed_derived_evaluation Λ A I V V' r K.obj

/-- Canonical section comparison commutes with pro-etale base change and isomorphisms
of squares. All maps of the cube, including its test-fibre face, are retained.
Source: Tags 0D6E--0D6F and the statement's localization clause
(blueprint: lem-sfb-closed-test-derived-exchange-model).

Proof (step 9): Localized direct images are given by the same fibre-product section
formula. Localization preserves units and counits, and exact pullback composition is
coherent. Both composites therefore give the same ordinary restriction on a K-injective
representative; the canonical derived composition units descend that equality. This
includes isomorphisms, since their base morphisms are pro-etale. -/
theorem section_comparison_base_change_naturality
    {X U T W X' U' T' W' : Scheme.{u}}
    {f : X ⟶ U} {b : W ⟶ U} {h : T ⟶ X} {fW : T ⟶ W}
    {f' : X' ⟶ U'} {b' : W' ⟶ U'} {h' : T' ⟶ X'} {fW' : T' ⟶ W'}
    (a : X' ⟶ X) (v : U' ⟶ U) (t : T' ⟶ T) (k : W' ⟶ W)
    [WeaklyEtale v] [WeaklyEtale b] [WeaklyEtale b']
    (w : IsPullback h fW f b) (w' : IsPullback h' fW' f' b')
    (wf : IsPullback a f' f v) (wb : IsPullback k b' b v)
    (wh : IsPullback t h' h a) (_wW : IsPullback t fW' fW k)
    (K : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (sectionComparison Λ w.toCommSq).app K.obj ≫
        (sectionsArrow Λ t wh.w).app K.obj ≫
        (condensedModuleSections Λ T').rightDerivedFunctor.map
          ((pullComp Λ h' a).hom.app K.obj) =
      (sectionsArrow Λ k wb.w).app
          ((CondensedRing.moduleObjectDerivedPushforward Λ f).obj K.obj) ≫
        (condensedModuleSections Λ W').rightDerivedFunctor.map
          ((pullComp Λ b' v).hom.app
            ((CondensedRing.moduleObjectDerivedPushforward Λ f).obj K.obj)) ≫
        (sectionsOver Λ b').map ((exchange Λ wf.toCommSq).app K.obj) ≫
        (sectionComparison Λ w'.toCommSq).app ((pull Λ a).obj K.obj) := by
  sorry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
omit [IsCommMonObj Λ] in
private theorem pushSectionsIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.whiskerRight (CondensedRing.lowerStarComp Λ f g).hom
        (condensedModuleSections Λ Z) ≫ (pushSectionsIso Λ (f ≫ g)).hom =
      Functor.whiskerLeft (CondensedRing.lowerStar Λ f) (pushSectionsIso Λ g).hom ≫
        (pushSectionsIso Λ f).hom := by
  apply NatTrans.ext
  funext M
  let σZ := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology Z) Ab.{u + 1}
    (Scheme.ProEt.isTerminalMkId Z)
  let σY := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology Y) Ab.{u + 1}
    (Scheme.ProEt.isTerminalMkId Y)
  let σX := Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology X) Ab.{u + 1}
    (Scheme.ProEt.isTerminalMkId X)
  change ((sheafSections (Scheme.ProEt.topology Z) Ab.{u + 1}).obj
      (op (Scheme.ProEt.mk (𝟙 Z)))).map
        ((CondensedRing.lowerStarComp Λ f g).hom.app M).hom ≫
      (σZ.inv.app ((CondensedRing.lowerStar Λ (f ≫ g)).obj M).X ≫
        (ProEtale.globalSectionsLowerStarIso Ab.{u + 1} (f ≫ g)).hom.app M.X ≫
          σX.hom.app M.X) =
    (σZ.inv.app ((CondensedRing.lowerStar Λ g).obj
        ((CondensedRing.lowerStar Λ f).obj M)).X ≫
      (ProEtale.globalSectionsLowerStarIso Ab.{u + 1} g).hom.app
        ((CondensedRing.lowerStar Λ f).obj M).X ≫
      σY.hom.app ((CondensedRing.lowerStar Λ f).obj M).X) ≫
        (σY.inv.app ((CondensedRing.lowerStar Λ f).obj M).X ≫
          (ProEtale.globalSectionsLowerStarIso Ab.{u + 1} f).hom.app M.X ≫
            σX.hom.app M.X)
  rw [reassoc_of% σZ.inv.naturality]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [CondensedRing.lowerStarComp_hom_app_hom,
    reassoc_of% ProEtale.globalSectionsLowerStarIso_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem derivedPushComp_eq_conjugate {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.rightDerivedFunctorCompIso' (CondensedRing.lowerStar Λ f)
        (CondensedRing.lowerStar Λ g) (CondensedRing.lowerStarComp Λ f g) =
      conjugateIsoEquiv ((adj Λ g).comp (adj Λ f)) (adj Λ (f ≫ g))
        (pullComp Λ f g) := by
  apply Iso.ext
  apply Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (CondensedRing.upperStarLowerStarAdjunction Λ f)
    (CondensedRing.upperStarLowerStarAdjunction Λ g)
    (CondensedRing.upperStarLowerStarAdjunction Λ (f ≫ g))
  exact congrArg Iso.hom (CondensedRing.conjugateIsoEquiv_upperStarComp Λ f g).symm

set_option backward.isDefEq.respectTransparency false in
private theorem derived_unit_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (adj Λ (f ≫ g)).unit.app M ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ (f ≫ g)).map
          ((pullComp Λ f g).hom.app M) =
      (adj Λ g).unit.app M ≫
        (CondensedRing.moduleObjectDerivedPushforward Λ g).map
          ((adj Λ f).unit.app ((pull Λ g).obj M)) ≫
        (Functor.rightDerivedFunctorCompIso' (CondensedRing.lowerStar Λ f)
          (CondensedRing.lowerStar Λ g) (CondensedRing.lowerStarComp Λ f g)).hom.app
            ((pull Λ f).obj ((pull Λ g).obj M)) := by
  have hu := unit_conjugateEquiv ((adj Λ g).comp (adj Λ f)) (adj Λ (f ≫ g))
    (pullComp Λ f g).hom M
  rw [← conjugateIsoEquiv_apply_hom, ← derivedPushComp_eq_conjugate,
    Adjunction.comp_unit_app] at hu
  rw [← hu, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem pushDerivedSectionsIso_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    Functor.whiskerRight
        (Functor.rightDerivedFunctorCompIso' (CondensedRing.lowerStar Λ f)
          (CondensedRing.lowerStar Λ g) (CondensedRing.lowerStarComp Λ f g)).hom
        (condensedModuleSections Λ Z).rightDerivedFunctor ≫
        (pushDerivedSectionsIso Λ (f ≫ g)).hom =
      Functor.whiskerLeft (CondensedRing.moduleObjectDerivedPushforward Λ f)
          (pushDerivedSectionsIso Λ g).hom ≫ (pushDerivedSectionsIso Λ f).hom := by
  exact Functor.rightDerivedFunctorCompIso'_assoc
    (CondensedRing.lowerStar Λ f) (CondensedRing.lowerStar Λ g)
    (condensedModuleSections Λ Z) (CondensedRing.lowerStar Λ (f ≫ g))
    (condensedModuleSections Λ Y) (condensedModuleSections Λ X)
    (CondensedRing.lowerStarComp Λ f g) (pushSectionsIso Λ g)
    (pushSectionsIso Λ (f ≫ g)) (pushSectionsIso Λ f) (pushSectionsIso_comp Λ f g)

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))) :
    (restriction Λ (f ≫ g)).app M ≫
        (condensedModuleSections Λ X).rightDerivedFunctor.map
          ((pullComp Λ f g).hom.app M) =
      (restriction Λ g).app M ≫ (restriction Λ f).app ((pull Λ g).obj M) := by
  let GZ := (condensedModuleSections Λ Z).rightDerivedFunctor
  let GY := (condensedModuleSections Λ Y).rightDerivedFunctor
  let GX := (condensedModuleSections Λ X).rightDerivedFunctor
  let Rf := CondensedRing.moduleObjectDerivedPushforward Λ f
  let Rg := CondensedRing.moduleObjectDerivedPushforward Λ g
  let Rfg := CondensedRing.moduleObjectDerivedPushforward Λ (f ≫ g)
  let P := (pull Λ f).obj ((pull Λ g).obj M)
  let d := Functor.rightDerivedFunctorCompIso' (CondensedRing.lowerStar Λ f)
    (CondensedRing.lowerStar Λ g) (CondensedRing.lowerStarComp Λ f g)
  have hη := congrArg GZ.map (derived_unit_comp Λ f g M)
  have hd := NatTrans.congr_app (pushDerivedSectionsIso_comp Λ f g) P
  have hn := (pushDerivedSectionsIso Λ g).hom.naturality
    ((adj Λ f).unit.app ((pull Λ g).obj M))
  have hn' := (pushDerivedSectionsIso Λ (f ≫ g)).hom.naturality
    ((pullComp Λ f g).hom.app M)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hd hn hn'
  dsimp only [restriction, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  change (GZ.map ((adj Λ (f ≫ g)).unit.app M) ≫
      (pushDerivedSectionsIso Λ (f ≫ g)).hom.app ((pull Λ (f ≫ g)).obj M)) ≫
        GX.map ((pullComp Λ f g).hom.app M) =
    (GZ.map ((adj Λ g).unit.app M) ≫
      (pushDerivedSectionsIso Λ g).hom.app ((pull Λ g).obj M)) ≫
        GY.map ((adj Λ f).unit.app ((pull Λ g).obj M)) ≫
          (pushDerivedSectionsIso Λ f).hom.app P
  simp only [Category.assoc]
  rw [← hn']
  rw [← GZ.map_comp_assoc, hη]
  simp only [Functor.map_comp, Category.assoc] at hd ⊢
  change GZ.map ((adj Λ g).unit.app M) ≫
      GZ.map (Rg.map ((adj Λ f).unit.app ((pull Λ g).obj M))) ≫
        GZ.map (d.hom.app P) ≫ (pushDerivedSectionsIso Λ (f ≫ g)).hom.app P = _
  rw [hd]
  rw [← reassoc_of% hn]

/-- The derived restriction appearing in the closed-test normalization commutes with
pro-etale localization, using the specified composition constraints.
Source: Tags 09T5 and 0D6E--0D6F
(blueprint: lem-sfb-closed-test-derived-exchange-model).

Proof (steps 7 and 9): Composition of the two adjunction units is the unit of the
composite adjunction. The section comparison is normalized by the ordinary identity.
Apply this twice to the two equal composites in the localization square. Pullback
composition identifies their coefficients and gives precisely the displayed equation. -/
theorem derived_restriction_localization
    {T W T' W' : Scheme.{u}} (a : W ⟶ T) (a' : W' ⟶ T')
    (t : T' ⟶ T) (k : W' ⟶ W) [WeaklyEtale t]
    (w : IsPullback k a' a t)
    (K : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T))) :
    (restriction Λ a).app K.obj ≫
        (restriction Λ k).app ((pull Λ a).obj K.obj) ≫
        (condensedModuleSections Λ W').rightDerivedFunctor.map
          ((pullComp Λ k a).inv.app K.obj) ≫
        (condensedModuleSections Λ W').rightDerivedFunctor.map
          ((eqToIso (congrArg (fun q : W' ⟶ T ↦ pull Λ q) w.w)).hom.app K.obj) =
      (restriction Λ t).app K.obj ≫
        (restriction Λ a').app ((pull Λ t).obj K.obj) ≫
        (condensedModuleSections Λ W').rightDerivedFunctor.map
          ((pullComp Λ a' t).inv.app K.obj) := by
  let G := (condensedModuleSections Λ W').rightDerivedFunctor
  have hc₁ := restriction_comp Λ k a K.obj
  have hc₂ := restriction_comp Λ a' t K.obj
  have restriction_congr (p q : W' ⟶ T) (hpq : p = q) :
      (restriction Λ p).app K.obj ≫
          G.map ((eqToIso (congrArg (fun r : W' ⟶ T ↦ pull Λ r) hpq)).hom.app K.obj) =
        (restriction Λ q).app K.obj := by
    cases hpq
    change (restriction Λ p).app K.obj ≫ G.map (𝟙 _) = _
    rw [G.map_id]
    exact Category.comp_id ((restriction Λ p).app K.obj)
  have he := restriction_congr (k ≫ a) (a' ≫ t) w.w
  calc
    _ = (restriction Λ (k ≫ a)).app K.obj ≫
        G.map ((eqToIso (congrArg (fun q : W' ⟶ T ↦ pull Λ q) w.w)).hom.app K.obj) := by
      simp only [← Category.assoc]
      rw [← hc₁]
      change (((restriction Λ (k ≫ a)).app K.obj ≫ G.map _) ≫ G.map _) ≫ G.map _ = _
      simp only [Category.assoc, ← G.map_comp, Iso.hom_inv_id_app, G.map_id]
      dsimp only [G]
      exact (Category.assoc _ _ _).symm.trans
        (congrArg (fun q ↦ q ≫ G.map
          ((eqToIso (congrArg (fun q : W' ⟶ T ↦ pull Λ q) w.w)).hom.app K.obj))
          (Category.comp_id ((restriction Λ (k ≫ a)).app K.obj)))
    _ = (restriction Λ (a' ≫ t)).app K.obj := he
    _ = _ := by
      simp only [← Category.assoc]
      rw [← hc₂]
      change _ = ((restriction Λ (a' ≫ t)).app K.obj ≫ G.map _) ≫ G.map _
      simp only [Category.assoc, ← G.map_comp, Iso.hom_inv_id_app, G.map_id]
      dsimp only [G]
      exact (Category.comp_id ((restriction Λ (a' ≫ t)).app K.obj)).symm

section Coefficients

variable {Λ} {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ'] (c : Λ ⟶ Λ') [IsMonHom c]

/-- The existing exact restriction of scalars on ordinary unbounded derived categories.
Source: scalar clause and Tag 0D6E
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def restrict (X : Scheme.{u}) :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ' X)) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) :=
  (Mod.comap (coefficientMap c X)).mapDerivedCategory

/-- The canonical right-derived direct-image coefficient comparison. Its direction is fixed
by the ordinary section identity; no preservation of injectives by restriction is assumed.
Source: the statement's coefficient clause and proof step 10
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def restrictPush {X Y : Scheme.{u}} (f : X ⟶ Y) :
    CondensedRing.moduleObjectDerivedPushforward Λ' f ⋙ restrict c Y ⟶
      restrict c X ⋙ CondensedRing.moduleObjectDerivedPushforward Λ f :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
      (CondensedRing.lowerStar Λ' f) (Mod.comap (coefficientMap c Y))).inv ≫
    Functor.rightDerivedPullback (Mod.comap (coefficientMap c X))
      (CondensedRing.comapLowerStarIso c f).hom

/-- The derived coefficient map on global sections, induced by the literal underlying
section identity and the universal right-derived unit.
Source: coefficient clause, proof step 10
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def restrictSections (X : Scheme.{u}) :
    (condensedModuleSections Λ' X).rightDerivedFunctor ⟶
      restrict c X ⋙ (condensedModuleSections Λ X).rightDerivedFunctor :=
  Functor.rightDerivedPullback (Mod.comap (coefficientMap c X)) (𝟙 _)

/-- Coefficient restriction on localized sections uses the existing exact pullback comparison.
Source: coefficient clause and Tag 0D6F
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def restrictSectionsOver {X W : Scheme.{u}} (b : W ⟶ X) :
    sectionsOver Λ' b ⟶ restrict c X ⋙ sectionsOver Λ b :=
  Functor.whiskerLeft (pull Λ' b) (restrictSections c W) ≫
    Functor.whiskerRight (CondensedRing.derivedComapUpperStarIso c b).hom
      (condensedModuleSections Λ W).rightDerivedFunctor

/-- The actual ordinary extension unit in degree zero, with exact restriction of scalars.
Source: the final sentence of the item, x ↦ 1 tensor x
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def scalarUnit (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (DerivedCategory.singleFunctor _ 0).obj M ⟶
      (restrict c X).obj ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.extendScalars (coefficientMap c X)).obj M)) :=
  (DerivedCategory.singleFunctor _ 0).map
      ((Mod.extendRestrictAdjunction (coefficientMap c X)).unit.app M) ≫
    ((Mod.comap (coefficientMap c X)).mapDerivedCategorySingleFunctor 0).inv.app
      ((Mod.extendScalars (coefficientMap c X)).obj M)

/-- Commutativity of the section-comparison square for the actual coefficient map.
Source: coefficient clause, proof steps 10--11
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def CoefficientSectionComparison {X U T W : Scheme.{u}} {f : X ⟶ U} {b : W ⟶ U}
    {h : T ⟶ X} {fW : T ⟶ W} (w : CommSq h fW f b)
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))) : Prop :=
  (restrictSectionsOver c b).app
        ((CondensedRing.moduleObjectDerivedPushforward Λ' f).obj N) ≫
      (sectionsOver Λ b).map ((restrictPush c f).app N) ≫
      (sectionComparison Λ w).app ((restrict c X).obj N) =
    (sectionComparison Λ' w).app N ≫ (restrictSectionsOver c h).app N

/-- Commutativity of the closed-test unit square under restriction of scalars.
Source: coefficient clause, proof step 10
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def CoefficientClosedComparison (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    (N : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of A))) Ab.{u + 1})
      (condensedRingObj Λ' (Spec (.of A))))) : Prop :=
  (closedComparison Λ' A I V).app N ≫
      (restrictSectionsOver c V.hom).app ((pull Λ' (closedMap A I)).obj N) ≫
      (sectionsOver Λ V.hom).map
        ((CondensedRing.derivedComapUpperStarIso c (closedMap A I)).hom.app N) =
    (restrictSectionsOver c ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom).app N ≫
      (closedComparison Λ A I V).app ((restrict c (Spec (.of A))).obj N)

/-- Commutativity of derived restriction and the actual coefficient section map.
Source: coefficient clause and Tag 0D6F
(blueprint: lem-sfb-closed-test-derived-exchange-model). -/
def CoefficientRestriction {X W W' : Scheme.{u}} (b : W ⟶ X) (a : W' ⟶ W)
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X))) : Prop :=
  (restrictionOver Λ' b a).app N ≫ (restrictSectionsOver c (a ≫ b)).app N =
    (restrictSectionsOver c b).app N ≫
      (restrictionOver Λ b a).app ((restrict c X).obj N)

/-- Every coefficient comparison square commutes, including the square of any supplied
module morphism K → Res N. There is no scalar/direct-image invertibility assumption.
Source: coefficient clause and proof steps 10--11
(blueprint: lem-sfb-closed-test-derived-exchange-model).

Proof: On underlying section complexes the ordinary scalar comparison is the identity.
Use the universal right-derived units to define its direct-image comparison, without
assuming restriction preserves K-injectives. Units, counits, pullback composition and
restriction commute with this identity. Hence the two section-comparison squares and
closed-unit square commute, as does derived restriction. The remaining equation is the
naturality square at the actual supplied module map. For a degree-zero module apply it
to scalarUnit, which is precisely the ordinary extension unit, not derived tensor. -/
theorem closed_test_coefficient_naturality
    (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
    (w : IsPullback h fZ f (closedMap A I))
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤)]
    (K : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
    (N : DerivedCategory.Plus
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ' X)))
    (φ : K.obj ⟶ (restrict c X).obj N.obj) :
    CoefficientSectionComparison c
        (IsPullback.of_hasPullback f
          ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom).toCommSq N.obj ∧
      CoefficientSectionComparison c (IsPullback.of_hasPullback fZ V.hom).toCommSq
        ((pull Λ' h).obj N.obj) ∧
      CoefficientClosedComparison c A I V
        ((CondensedRing.moduleObjectDerivedPushforward Λ' f).obj N.obj) ∧
      CoefficientRestriction c
        (pullback.fst f ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom)
        (testMap A I w.toCommSq V) N.obj ∧
      (CondensedRing.moduleObjectDerivedPushforward Λ f ⋙ pull Λ (closedMap A I) ⋙
          sectionsOver Λ V.hom).map φ ≫
          (evaluatedExchange Λ A I w.toCommSq V).app ((restrict c X).obj N.obj) =
        (evaluatedExchange Λ A I w.toCommSq V).app K.obj ≫
          (pull Λ h ⋙ CondensedRing.moduleObjectDerivedPushforward Λ fZ ⋙
            sectionsOver Λ V.hom).map φ := by
  sorry

end Coefficients

/-- The derived comparison isomorphisms, with their unit normalization and mate equation.
Source: Stacks Project, Tags 09BL (1)--(2), 0D6E--0D6F
(blueprint: lem-sfb-closed-test-derived-exchange-model).

Proof: (1) Transport internal modules through the fixed section-ring equivalence,
which preserves underlying abelian sheaves, sections, exactness and K-injectivity
[def-weil-pbc-internal-abelian-sheaf-module-equivalence].
The coefficient inverse-image maps are isomorphisms, hence every pullback is exact
[sk-def-sfb-module-pushforward-pullback, lem-zl-condensed-lisse-proetale-locality].
(2) The two geometric w-contractible tests have exact evaluation on the full and
basis sites. The closed-site counit and unit-comparison theorems identify the actual
inverse-image unit section with the closed-evaluation isomorphism.
(3) Choose a K-injective I representing K. The exact left adjoint of f_* makes f_*I
K-injective; exact test evaluation and derived section localization identify the source
with Q(I(T)). (4) Resolve h*I by a K-injective J; the same argument identifies the target
with Q(J(T0)). Pullback composition identifies its coefficients with a*(K|T).
(5) On ordinary modules the square comparison followed by the counit sends the unit
section of x to the inverse-image section of x. The triangle identity cancels the
inserted unit and counit. (6) Apply this calculation degreewise to I and then to I → J.
Transposition under the normalized derived adjunction gives the specified exchange.
(7) The resulting I(T) → J(T0) is the derived unit for a followed by the canonical
section composition, which is the degreewise section identity on a K-injective target.
(8) K-injective Hom computation makes this independent of resolutions and natural in K
[lem-weil-pbc-kinjective-hom-derived].
(9) The same units, restrictions and composition constraints commute with test maps,
isomorphisms of squares and pro-etale localizations. (10) Restriction of scalars is
exact and its underlying section maps are identities; the universal derived comparison
has its natural direction and is not assumed invertible. (11) Apply this to the actual
map K → Res N and, in degree zero, to the ordinary extension unit x ↦ 1 tensor x. -/
theorem closed_test_derived_exchange_model
    (A : Type u) [CommRing A] (I : Ideal A)
    {X XZ : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of A))
    (h : XZ ⟶ X) (fZ : XZ ⟶ Spec (.of (A ⧸ I)))
    (w : IsPullback h fZ f (closedMap A I))
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    [IsWContractibleRing Γ(V.left, ⊤)]
    [IsWContractibleRing Γ(((Scheme.AffineProEt.closedSiteLift A I).obj V).left, ⊤)] :
    ∃ eLeft :
        DerivedCategory.Plus.ι ⋙ CondensedRing.moduleObjectDerivedPushforward Λ f ⋙
            pull Λ (closedMap A I) ⋙ sectionsOver Λ V.hom ≅
          DerivedCategory.Plus.ι ⋙ sectionsOver Λ
            (pullback.fst f ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom),
      ∃ eRight :
        DerivedCategory.Plus.ι ⋙ pull Λ h ⋙
            CondensedRing.moduleObjectDerivedPushforward Λ fZ ⋙ sectionsOver Λ V.hom ≅
          DerivedCategory.Plus.ι ⋙ pull Λ h ⋙
            sectionsOver Λ (pullback.fst fZ V.hom),
        (∀ K : DerivedCategory.Plus
            (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
          IsIso ((closedComparison Λ A I V).app
            ((CondensedRing.moduleObjectDerivedPushforward Λ f).obj K.obj)) ∧
          (closedComparison Λ A I V).app
              ((CondensedRing.moduleObjectDerivedPushforward Λ f).obj K.obj) ≫
                eLeft.hom.app K =
            (sectionComparison Λ (IsPullback.of_hasPullback f
              ((Scheme.AffineProEt.closedSiteLift A I).obj V).hom).toCommSq).app K.obj) ∧
        eRight.hom = Functor.whiskerLeft (DerivedCategory.Plus.ι ⋙ pull Λ h)
          (sectionComparison Λ (IsPullback.of_hasPullback fZ V.hom).toCommSq) ∧
        Functor.whiskerLeft DerivedCategory.Plus.ι
            (evaluatedExchange Λ A I w.toCommSq V) ≫ eRight.hom =
          eLeft.hom ≫ Functor.whiskerLeft DerivedCategory.Plus.ι
            (testRestriction Λ A I w.toCommSq V) := by
  obtain ⟨eLeft, eRight, hLeft, hRight, hExchange, _⟩ :=
    NonaffineClosedTestExchangeIdentification.nonaffine_closed_test_exchange_identification
      Λ A I f h fZ w V
  exact ⟨eLeft, eRight, hLeft, hRight, hExchange⟩

end AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel
