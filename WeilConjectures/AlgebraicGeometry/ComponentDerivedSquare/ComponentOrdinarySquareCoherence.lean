/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ComponentDerivedSquare.ComponentOrdinaryEdges
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.CompMonoidal

/-! # Coefficient-normalized ordinary component square coherence

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

private theorem tests_identity
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (s : OrdinaryEdges Λ)
    (sq : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
      Square Λ f (s.corner X) (s.corner Y) (s.slice f))
    (X : Scheme.{u}) [IsAffine X] (E : Over (affineComponentSpace X)) :
    (sq (𝟙 X)).tests.hom.app E ≫
        (CondensedRing.componentTests X).map ((s.identity X).tests.hom.app E) =
      (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ X).hom.app
        ((CondensedRing.componentTests X).obj E) := by
  obtain ⟨e, he, hc⟩ := component_lift_base_change.choose_spec.2.1 X E
  have h : e.hom = (s.identity X).tests.hom.app E := by
    apply Over.OverMorphism.ext
    exact he.trans ((s.identity X).tests_projection E).symm
  apply MorphismProperty.Over.Hom.ext
  change ((sq (𝟙 X)).tests.hom.app E).left ≫ _ = _
  rw [(sq (𝟙 X)).tests_eq]
  have hc' := congrArg (fun k ↦ k.left) hc
  rw [h] at hc'
  exact hc'

private theorem pullback_comp_fst {C : Type*} [Category* C] [HasPullbacks C]
    {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) (E : Over X) :
    ((Over.pullbackComp g f).hom.app E).left ≫
      pullback.fst (pullback.snd E.hom f) g ≫ pullback.fst E.hom f =
        pullback.fst E.hom (g ≫ f) := by
  have h := congrArg (fun k ↦ k.left)
    (conjugateEquiv_counit (Over.mapPullbackAdj (g ≫ f))
      ((Over.mapPullbackAdj g).comp (Over.mapPullbackAdj f))
      (Over.mapComp g f).symm.hom E)
  simpa [Over.pullbackComp, conjugateIsoEquiv, Adjunction.comp_counit_app,
    Over.mapPullbackAdj_counit_app, Category.assoc] using h

private theorem iterated_pullback_ext {C : Type*} [Category* C] [HasPullbacks C]
    {U W X Y Z : C} (u : U ⟶ X) (f : Y ⟶ X) (g : Z ⟶ Y)
    (a b : W ⟶ pullback (pullback.snd u f) g)
    (hf : a ≫ pullback.fst (pullback.snd u f) g ≫ pullback.fst u f =
      b ≫ pullback.fst (pullback.snd u f) g ≫ pullback.fst u f)
    (hs : a ≫ pullback.snd (pullback.snd u f) g =
      b ≫ pullback.snd (pullback.snd u f) g) : a = b := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc] using hf
    · simp only [Category.assoc, pullback.condition]
      simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ g) hs
  · exact hs

private theorem tests_composition
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (s : OrdinaryEdges Λ)
    (sq : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
      Square Λ f (s.corner X) (s.corner Y) (s.slice f))
    {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (g : Z ⟶ Y) (E : Over (affineComponentSpace X)) :
    (sq (g ≫ f)).tests.hom.app E ≫
        (CondensedRing.componentTests Z).map ((s.composition f g).tests.hom.app E) =
      (MorphismProperty.Over.pullbackComp g f).hom.app
          ((CondensedRing.componentTests X).obj E) ≫
        (Scheme.proEtaleBaseChange g).map ((sq f).tests.hom.app E) ≫
          (sq g).tests.hom.app ((Over.pullback (affineComponentMap f)).obj E) := by
  obtain ⟨e, he₁, he₂, hc⟩ := component_lift_base_change.choose_spec.2.2.1 X Y Z f g E
  have h : e.hom = (s.composition f g).tests.hom.app E := by
    apply Over.OverMorphism.ext
    apply iterated_pullback_ext E.hom (affineComponentMap f) (affineComponentMap g)
    · exact he₁.trans ((s.composition f g).tests_fst E).symm
    · exact he₂.trans ((s.composition f g).tests_snd E).symm
  apply MorphismProperty.Over.Hom.ext
  change ((sq (g ≫ f)).tests.hom.app E).left ≫ _ = _
  rw [(sq (g ≫ f)).tests_eq]
  have hc' := congrArg (fun k ↦ k.left) hc
  rw [h] at hc'
  have hm : ((Scheme.proEtaleBaseChange g).map ((sq f).tests.hom.app E)).left =
      ((Over.pullback g).map ((component_lift_base_change.choose f).hom.app E)).left := by
    simp only [Scheme.proEtaleBaseChange, MorphismProperty.Over.pullback_map_left,
      Over.pullback_map_left, (sq f).tests_eq]
    rfl
  have hp : ((MorphismProperty.Over.pullbackComp g f).hom.app
        ((CondensedRing.componentTests X).obj E)).left =
      ((Over.pullbackComp g f).hom.app ((relativeComponentLift X).obj E)).left := by
    apply iterated_pullback_ext ((relativeComponentLift X).obj E).hom f g
    · exact (MorphismProperty.Over.pullbackComp_left_fst_fst g f _).trans
        (pullback_comp_fst f g _).symm
    · exact (MorphismProperty.Over.w
        ((MorphismProperty.Over.pullbackComp g f).hom.app
          ((CondensedRing.componentTests X).obj E))).trans
        (Over.w ((Over.pullbackComp g f).hom.app ((relativeComponentLift X).obj E))).symm
  change _ ≫ _ =
    ((MorphismProperty.Over.pullbackComp g f).hom.app
      ((CondensedRing.componentTests X).obj E)).left ≫
      ((Scheme.proEtaleBaseChange g).map ((sq f).tests.hom.app E)).left ≫
        ((sq g).tests.hom.app ((Over.pullback (affineComponentMap f)).obj E)).left
  rw [hp, hm, (sq g).tests_eq]
  exact hc'

private theorem abelian_identity
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (s : OrdinaryEdges Λ)
    (sq : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
      Square Λ f (s.corner X) (s.corner Y) (s.slice f))
    (X : Scheme.{u}) [IsAffine X]
    (A : Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      Ab.{u + 1}) :
    (sq (𝟙 X)).abelian.hom.app A ≫
        (s.corner X).inverse.map ((s.identity X).abelian.hom.app A) =
      (upperStarId Ab.{u + 1} X).hom.app ((s.corner X).inverse.obj A) := by
  let c := s.corner X
  let i := s.identity X
  let a := upperStarLowerStarAdjunction Ab.{u + 1} (𝟙 X)
  have h : (sq (𝟙 X)).abelian =
      Functor.isoWhiskerLeft c.inverse (upperStarId Ab.{u + 1} X) ≪≫
        c.inverse.rightUnitor ≪≫ c.inverse.leftUnitor.symm ≪≫
          Functor.isoWhiskerRight i.abelian.symm c.inverse := by
    apply (conjugateIsoEquiv ((s.slice (𝟙 X)).adjunction.comp c.adjunction)
      (c.adjunction.comp a)).injective
    rw [conjugateIsoEquiv_trans _ (c.adjunction.comp Adjunction.id) _,
      conjugateIsoEquiv_trans _ c.adjunction _,
      conjugateIsoEquiv_trans _ (Adjunction.id.comp c.adjunction) _]
    dsimp only [a]
    simp only [conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_iso_symm,
      conjugateIsoEquiv_leftUnitor, conjugateIsoEquiv_rightUnitor,
      conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_upperStarId]
    apply Iso.ext
    apply NatTrans.ext
    funext G
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext E
    obtain ⟨E⟩ := E
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Iso.symm_hom, Iso.symm_inv, Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
      Category.comp_id, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app]
    have hi := i.abelian_mate ((componentDirect X c.continuous).obj G) E
    simp only [conjugateIsoEquiv_iso_symm, Iso.symm_hom] at hi
    rw [(sq (𝟙 X)).abelian_mate, hi]
    simp only [componentDirect, lowerStarId, Functor.sheafPushforwardContinuous_map_hom_app,
      Functor.sheafPushforwardContinuous_obj_obj_map,
      Functor.sheafPushforwardContinuousId'_inv_app_hom_app,
      ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
      Quiver.Hom.unop_op]
    erw [Category.comp_id]
    rw [← G.obj.map_comp, ← op_comp]
    congr 1
    apply congrArg Quiver.Hom.op
    have ht := tests_identity Λ s sq X E
    have ht' := congrArg
      (fun k ↦ k ≫ (CondensedRing.componentTests X).map
        ((s.identity X).tests.inv.app E)) ht
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at ht'
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at ht'
    simpa only [i] using ht'
  have ha := congrArg (fun e ↦ e.hom.app A) h
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Iso.symm_hom,
    Category.id_comp] at ha
  rw [ha]
  dsimp only [c, i]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp

private theorem abelian_composition
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (s : OrdinaryEdges Λ)
    (sq : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
      Square Λ f (s.corner X) (s.corner Y) (s.slice f))
    {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine Z]
    (f : Y ⟶ X) (g : Z ⟶ Y)
    (A : Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      Ab.{u + 1}) :
    (upperStarComp Ab.{u + 1} g f).hom.app ((s.corner X).inverse.obj A) ≫
        (upperStar Ab.{u + 1} g).map ((sq f).abelian.hom.app A) ≫
          (sq g).abelian.hom.app ((s.slice f).inverse.obj A) =
      (sq (g ≫ f)).abelian.hom.app A ≫
        (s.corner Z).inverse.map ((s.composition f g).abelian.hom.app A) := by
  let cx := s.corner X
  let cy := s.corner Y
  let cz := s.corner Z
  let sf := s.slice f
  let sg := s.slice g
  let sc := s.composition f g
  let af := upperStarLowerStarAdjunction Ab.{u + 1} f
  let ag := upperStarLowerStarAdjunction Ab.{u + 1} g
  let ac := upperStarLowerStarAdjunction Ab.{u + 1} (g ≫ f)
  have h : (sq (g ≫ f)).abelian =
      Functor.isoWhiskerLeft cx.inverse (upperStarComp Ab.{u + 1} g f) ≪≫
        (Functor.associator cx.inverse (upperStar Ab.{u + 1} f)
          (upperStar Ab.{u + 1} g)).symm ≪≫
        Functor.isoWhiskerRight (sq f).abelian (upperStar Ab.{u + 1} g) ≪≫
        Functor.associator sf.inverse cy.inverse (upperStar Ab.{u + 1} g) ≪≫
        Functor.isoWhiskerLeft sf.inverse (sq g).abelian ≪≫
        (Functor.associator sf.inverse sg.inverse cz.inverse).symm ≪≫
        Functor.isoWhiskerRight sc.abelian.symm cz.inverse := by
    apply (conjugateIsoEquiv ((s.slice (g ≫ f)).adjunction.comp cz.adjunction)
      (cx.adjunction.comp ac)).injective
    rw [conjugateIsoEquiv_trans _ (cx.adjunction.comp (af.comp ag)) _,
      conjugateIsoEquiv_trans _ ((cx.adjunction.comp af).comp ag) _,
      conjugateIsoEquiv_trans _ ((sf.adjunction.comp cy.adjunction).comp ag) _,
      conjugateIsoEquiv_trans _ (sf.adjunction.comp (cy.adjunction.comp ag)) _,
      conjugateIsoEquiv_trans _ (sf.adjunction.comp (sg.adjunction.comp cz.adjunction)) _,
      conjugateIsoEquiv_trans _ ((sf.adjunction.comp sg.adjunction).comp cz.adjunction) _]
    dsimp only [af, ag, ac]
    simp only [conjugateIsoEquiv_isoWhiskerRight, conjugateIsoEquiv_iso_symm,
      conjugateIsoEquiv_associator, conjugateIsoEquiv_isoWhiskerLeft,
      conjugateIsoEquiv_upperStarComp]
    apply Iso.ext
    apply NatTrans.ext
    funext G
    apply ObjectProperty.hom_ext
    apply NatTrans.ext
    funext E
    obtain ⟨E⟩ := E
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.comp_id, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app]
    have hs := sc.abelian_mate ((componentDirect Z (s.corner Z).continuous).obj G) E
    simp only [conjugateIsoEquiv_iso_symm, Iso.symm_hom] at hs
    rw [(sq (g ≫ f)).abelian_mate, hs]
    simp only [componentDirect, sliceDirect, Functor.sheafPushforwardContinuous_map_hom_app]
    dsimp only [sf, sg, cx, cy, cz]
    erw [(sq g).abelian_mate G
      ((Over.pullback (affineComponentMap f)).obj E),
      (sq f).abelian_mate ((lowerStar Ab.{u + 1} g).obj G) E,
      lowerStarComp_hom_app_hom_app, lowerStar_obj_obj_map']
    simp only [Functor.sheafPushforwardContinuous_obj_obj_map]
    rw [← G.obj.map_comp, ← G.obj.map_comp, ← G.obj.map_comp,
      ← op_comp, ← op_comp, ← op_comp]
    congr 1
    apply congrArg Quiver.Hom.op
    have ht := tests_composition Λ s sq f g E
    have ht' := congrArg
      (fun k ↦ k ≫ (CondensedRing.componentTests Z).map
        ((s.composition f g).tests.inv.app E)) ht
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at ht'
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at ht'
    simpa only [Quiver.Hom.unop_op, Scheme.proEtaleBaseChange, sc] using ht'
  have ha := congrArg (fun e ↦ e.hom.app A) h
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app] at ha
  rw [ha]
  dsimp only [cx, cy, cz, sf, sg, sc]
  simp [Category.assoc, ← Functor.map_comp]

@[reassoc]
private theorem square_unit
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X)
    {cx : Corner Λ X} {cy : Corner Λ Y} {sh : Slice Λ (affineComponentMap f)}
    (sq : Square Λ f cx cy sh)
    (M : Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
      Ab.{u + 1}) (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))) :
    CondensedRing.upperStarUnitHom Λ.X f ((cx.modules Λ X).obj M) ≫
        (sq.ordinary.hom.app M).hom = sq.abelian.hom.app M.X := by
  rw [sq.ordinary_underlying, ← Category.assoc]
  let N := ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ.X X)).obj
    ((cx.modules Λ X).obj M)
  change (Mod.extendUnitHom (condensedPullbackHom Λ.X f) N ≫
      ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ.X f)).hom.app N).hom) ≫
        sq.abelian.hom.app M.X = _
  rw [Mod.extendUnitHom_extendScalarsIsoComapInv_hom_app
    (condensedPullbackHom Λ.X f) N]
  exact Category.id_comp _

/-- Normalized ordinary squares satisfy the identity and composition equations.

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9 and the naturality
used in Corollary 4.4(2)
(blueprint: lem-zl-component-ordinary-square-coherence).

Proof: first forget module structures. The specified tests in Square agree with
the relative lift base-change isomorphisms. For the identity these are the
identity test comparison; for a composite they paste to the composite comparison
after the canonical pullback associators. The prescribed first and second
projection equations on s.identity and s.composition identify their tests with
the canonical slice comparisons, by pullback uniqueness. Applying an arbitrary
sheaf contravariantly yields the right-adjoint identity and composition equations.
Use Square.abelian_mate and the slice abelian_mate formulas to identify the left
comparisons as their adjunction mates. Injectivity of conjugateIsoEquiv and its
whiskering and pasting equations give the abelian identities. The scheme
identity and composition on modules are also the canonical adjunction mates.
Precompose the underlying module maps by upperStarUnitHom. The stored
ordinary_underlying equations and cancellation of the extension unit with
extendScalarsIsoComapInv turn each square into its abelian comparison. The
existing identity, composition and naturality equations for upperStarUnitHom
then reduce the two desired equations to the abelian coherence equations.
Faithfulness of Mod.forget proves the module equations. This lemma assumes all
edges, squares and their local normalizations; it constructs none of them. -/
theorem component_ordinary_square_coherence
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (s : OrdinaryEdges Λ)
    (sq : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
      Square Λ f (s.corner X) (s.corner Y) (s.slice f)) :
    (∀ (X : Scheme.{u}) [IsAffine X]
      (M : Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        Ab.{u + 1}) (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    ((sq (𝟙 X)).ordinary).hom.app M ≫
        ((s.corner X).modules Λ X).map ((s.identity X).ordinary.hom.app M) =
      (CondensedRing.upperStarId Λ.X X).hom.app (((s.corner X).modules Λ X).obj M)) ∧
    (∀ (X Y Z : Scheme.{u}) [IsAffine X] [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y)
      (M : Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        Ab.{u + 1}) (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    (CondensedRing.upperStarComp Λ.X g f).hom.app (((s.corner X).modules Λ X).obj M) ≫
        (CondensedRing.upperStar Λ.X g).map (((sq f).ordinary).hom.app M) ≫
        ((sq g).ordinary).hom.app (((s.slice f).modules Λ).obj M) =
      ((sq (g ≫ f)).ordinary).hom.app M ≫
        ((s.corner Z).modules Λ Z).map ((s.composition f g).ordinary.hom.app M)) := by
  constructor
  · intro X _ M
    ext : 1
    rw [← cancel_epi (CondensedRing.upperStarUnitHom Λ.X (𝟙 X)
      (((s.corner X).modules Λ X).obj M)), Mod.comp_hom', ← Category.assoc,
      square_unit Λ (𝟙 X), CondensedRing.upperStarUnitHom_upperStarId_hom_app_hom]
    change (sq (𝟙 X)).abelian.hom.app M.X ≫
        (s.corner X).inverse.map (((s.identity X).ordinary.hom.app M).hom) = _
    rw [(s.identity X).ordinary_underlying]
    exact abelian_identity Λ s sq X M.X
  · intro X Y Z _ _ _ f g M
    ext : 1
    rw [← cancel_epi (CondensedRing.upperStarUnitHom Λ.X (g ≫ f)
      (((s.corner X).modules Λ X).obj M))]
    simp only [Mod.comp_hom']
    rw [CondensedRing.upperStarUnitHom_upperStarComp_hom_app_hom_assoc,
      CondensedRing.upperStarUnitHom_map_hom_assoc,
      ← Functor.map_comp_assoc, square_unit Λ f,
      square_unit_assoc Λ (g ≫ f)]
    dsimp only [Functor.comp_obj]
    rw [square_unit Λ g (sq g) (((s.slice f).modules Λ).obj M)]
    change (upperStarComp Ab.{u + 1} g f).hom.app ((s.corner X).inverse.obj M.X) ≫
        (upperStar Ab.{u + 1} g).map ((sq f).abelian.hom.app M.X) ≫
          (sq g).abelian.hom.app ((s.slice f).inverse.obj M.X) =
      (sq (g ≫ f)).abelian.hom.app M.X ≫
        (s.corner Z).inverse.map (((s.composition f g).ordinary.hom.app M).hom)
    rw [(s.composition f g).ordinary_underlying]
    exact abelian_composition Λ s sq f g M.X

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
