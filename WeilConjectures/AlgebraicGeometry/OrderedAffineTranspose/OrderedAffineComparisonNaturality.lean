/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrderedAffineTranspose.OrderedAffineTransposeData
import WeilConjectures.AlgebraicGeometry.AffineLineEvaluation.AffineLineCompositeTranspose
import all WeilConjectures.SixFunctors.Exceptional.ExceptionalFiniteRestrictionAdjunction

/-! # Naturality of the ordered affine comparison

Source: the ordered affine transpose proof, Step 2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.OrderedAffineTranspose
open AffineLinePurity AffineSpacePurity VectorIntegrationSite

attribute [local semireducible] orderedSource exceptional lineSource twistAction
  projectionSourceObject projectionTargetObject
attribute [local implicit_reducible] orderedSource exceptional twistAction
  iteratedAffineLine iteratedAffineLineProj
set_option allowUnsafeReducibility true in
attribute [local reducible] lineSource projectionSourceObject projectionTargetObject
attribute [local irreducible] HasDerivedCategory.ofIsGrothendieckAbelian
  Scheme.finiteEtaleTateLine DerivedCategory.TStructure.t
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.singleFunctors

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2 AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2

set_option maxHeartbeats 1600000 in
-- Identifying the chosen reassociation with its explicit tensor formula is expensive.
set_option maxHeartbeats 400000 in
-- Specializing the three bounded-below Hom equivalences fixes their derived categories.
set_option maxHeartbeats 1600000 in
-- The chosen inverse compositor is compared with its explicit value along the tower.
attribute [local irreducible] Adjunction.ofIsLeftAdjoint Adjunction.homEquiv
  CategoryTheory.Functor.rightAdjoint fixedCompactSupportComparisonIso specifiedExceptionalHomEquiv
  derivedComparisonAdjunction

private theorem mapIso_refl_app
    {Cat : Type*} [Category* Cat] {Cat' : Type*} [Category* Cat']
    (B : Cat ⥤ Cat' ⥤ Cat') (M : Cat) (N : Cat') :
    (B.mapIso (Iso.refl M)).app N = Iso.refl _ := by
  apply Iso.ext
  exact NatTrans.congr_app (B.map_id M) N

private theorem tensorIso_refl_left (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (M : C A T) {W W' : C A T} (e : W ≅ W') :
    tensorIso A T (Iso.refl M) e = ((tensor A T).obj M).mapIso e := by
  unfold AffineSpacePurity.tensorIso
  rw [mapIso_refl_app, Iso.refl_trans]

private def rightTensorIso (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    {W W' : C A T} (e : W ≅ W') :
    (tensor A T).flip.obj W ≅ (tensor A T).flip.obj W' :=
  (tensor A T).flip.mapIso e

private def pullTensorIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T : Scheme.{u}} (f : X ⟶ T) (W : C A T) (W' : C A X)
    (e : (inverseImage A f).obj W ≅ W') :
    (tensor A T).flip.obj W ⋙ inverseImage A f ≅
      inverseImage A f ⋙ (tensor A X).flip.obj W' :=
  NatIso.ofComponents (fun M ↦ inverseImageTensorIso A f M W ≪≫
    ((tensor A X).obj _).mapIso e) (by
    let : IsNoetherianRing A := isNoetherian_of_finite A A
    intro M N a
    have h := NatTrans.congr_app
      ((leftDerivedUpperStarTensorNatIso (ModuleCat.{u + 1} A) f).hom.naturality a) W
    change (inverseImage A f).map (((tensor A T).map a).app W) ≫
        (inverseImageTensorIso A f N W).hom =
      (inverseImageTensorIso A f M W).hom ≫
        ((tensor A X).map ((inverseImage A f).map a)).app ((inverseImage A f).obj W) at h
    have h' := ((tensor A X).map ((inverseImage A f).map a)).naturality e.hom
    simp only [Iso.trans_hom,
    CategoryTheory.Functor.mapIso_hom,
      CategoryTheory.Functor.comp_map, CategoryTheory.Functor.flip_obj_map]
    change (inverseImage A f).map (((tensor A T).map a).app W) ≫
        (inverseImageTensorIso A f N W).hom ≫ ((tensor A X).obj _).map e.hom =
      ((inverseImageTensorIso A f M W).hom ≫ ((tensor A X).obj _).map e.hom) ≫
        ((tensor A X).map ((inverseImage A f).map a)).app W'
    simp only [Category.assoc]
    rw [← Category.assoc, h, Category.assoc, ← h'])

private theorem pullTensorIso_app (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T : Scheme.{u}} (f : X ⟶ T) (W : C A T) (W' : C A X)
    (e : (inverseImage A f).obj W ≅ W') (M : C A T) :
    (pullTensorIso A f W W' e).app M =
      inverseImageTensorIso A f M W ≪≫ ((tensor A X).obj _).mapIso e := by
  rfl

private def actionPullbackNatIso
    {C₁ : Type v₁} [Category.{w₁} C₁] {C₂ : Type v₂} [Category.{w₂} C₂]
    (F : C₁ ⥤ C₁) (G : C₂ ⥤ C₂) (H : C₁ ⥤ C₂)
    (e : F ⋙ H ≅ H ⋙ G) : (d : ℕ) → action F d ⋙ H ≅ H ⋙ action G d
  | 0 => Iso.refl _
  | d + 1 => CategoryTheory.Functor.isoWhiskerLeft (action F d) e ≪≫
      CategoryTheory.Functor.isoWhiskerRight (actionPullbackNatIso F G H e d) G

private theorem actionPullbackNatIso_app
    {C₁ : Type v₁} [Category.{w₁} C₁] {C₂ : Type v₂} [Category.{w₂} C₂]
    (F : C₁ ⥤ C₁) (G : C₂ ⥤ C₂) (H : C₁ ⥤ C₂)
    (e : F ⋙ H ≅ H ⋙ G) (M : C₁) (d : ℕ) :
    (actionPullbackNatIso F G H e d).app M =
      actionPullbackIso F G H (fun N ↦ e.app N) M d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change e.app ((action F d).obj M) ≪≫
        G.mapIso ((actionPullbackNatIso F G H e d).app M) =
      e.app ((action F d).obj M) ≪≫
        G.mapIso (actionPullbackIso F G H (fun N ↦ e.app N) M d)
    rw [ih]

private def tensorReassociationNatIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S)
    (W : C A T) (W' B : C A X)
    (eW : (inverseImage A f).obj W ≅ W') (eB : W' ≅ B) (d : ℕ) :
    inverseImage A (f ≫ g) ⋙ action ((tensor A X).flip.obj W') d ⋙
        (tensor A X).flip.obj W' ≅
      inverseImage A g ⋙ action ((tensor A T).flip.obj W) d ⋙
        inverseImage A f ⋙ (tensor A X).flip.obj B :=
  CategoryTheory.Functor.isoWhiskerRight
    (CategoryTheory.Functor.isoWhiskerRight (inverseImageComp A f g)
        (action ((tensor A X).flip.obj W') d) ≪≫
      CategoryTheory.Functor.isoWhiskerLeft (inverseImage A g)
        (actionPullbackNatIso ((tensor A T).flip.obj W) ((tensor A X).flip.obj W')
          (inverseImage A f) (pullTensorIso A f W W' eW) d).symm)
    ((tensor A X).flip.obj W') ≪≫
  CategoryTheory.Functor.isoWhiskerLeft
    (inverseImage A g ⋙ action ((tensor A T).flip.obj W) d ⋙ inverseImage A f)
    (rightTensorIso A X eB)

private def tensorZeroNatIso
    (A : Type (u + 1)) [CommRing A] {X T : Scheme.{u}} (f : X ⟶ T)
    (W B : C A X) (e : W ≅ B) :
    inverseImage A (f ≫ 𝟙 T) ⋙ (tensor A X).flip.obj W ≅
      inverseImage A f ⋙ (tensor A X).flip.obj B :=
  CategoryTheory.Functor.isoWhiskerRight
    (inverseImageComp A f (𝟙 T) ≪≫
      CategoryTheory.Functor.isoWhiskerRight (inverseImageId A T) (inverseImage A f))
    ((tensor A X).flip.obj W) ≪≫
  CategoryTheory.Functor.isoWhiskerLeft (inverseImage A f) (rightTensorIso A X e)

private theorem tensorReassociationNatIso_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S)
    (W : C A T) (W' B : C A X)
    (eW : (inverseImage A f).obj W ≅ W') (eB : W' ≅ B) (K : C A S) (d : ℕ) :
    (tensorReassociationNatIso A f g W W' B eW eB d).hom.app K =
      (tensorReassociation A f g W W' B eW eB K d).hom := by
  unfold tensorReassociation
  simp only [tensorIso_refl_left]
  simp only [tensorReassociationNatIso, AffineSpacePurity.tensorIso,
    rightTensorIso,
    Iso.trans_hom, Iso.app_hom,
    CategoryTheory.Functor.isoWhiskerRight_hom, CategoryTheory.Functor.isoWhiskerLeft_hom,
    CategoryTheory.Functor.whiskerRight_app, CategoryTheory.Functor.whiskerLeft_app,
    NatTrans.comp_app,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_comp, Iso.symm_hom,
    CategoryTheory.Functor.flip_obj_map, CategoryTheory.Functor.flip_map_app,
    Category.assoc]
  rw [← Iso.app_inv, actionPullbackNatIso_app]
  simp only [pullTensorIso_app]
  rfl

private theorem tensorZeroNatIso_app
    (A : Type (u + 1)) [CommRing A] {X T : Scheme.{u}} (f : X ⟶ T)
    (W B : C A X) (e : W ≅ B) (K : C A T) :
    (tensorZeroNatIso A f W B e).hom.app K =
      (tensorZeroReassociation A f W B e K).hom := by
  simp only [tensorZeroNatIso, tensorZeroReassociation, AffineSpacePurity.tensorIso,
    rightTensorIso,
    Iso.trans_hom, Iso.app_hom,
    CategoryTheory.Functor.isoWhiskerRight_hom, CategoryTheory.Functor.isoWhiskerLeft_hom,
    CategoryTheory.Functor.whiskerRight_app, CategoryTheory.Functor.whiskerLeft_app,
    NatTrans.comp_app,
    CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.flip_obj_map,
    CategoryTheory.Functor.flip_map_app]

private theorem tensorReassociation_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S)
    (W : C A T) (W' B : C A X)
    (eW : (inverseImage A f).obj W ≅ W') (eB : W' ≅ B)
    {K L : C A S} (v : K ⟶ L) (d : ℕ) :
    (inverseImage A (f ≫ g) ⋙ action ((tensor A X).flip.obj W') d ⋙
      (tensor A X).flip.obj W').map v ≫
        (tensorReassociation A f g W W' B eW eB L d).hom =
    (tensorReassociation A f g W W' B eW eB K d).hom ≫
      (inverseImage A g ⋙ action ((tensor A T).flip.obj W) d ⋙
        inverseImage A f ⋙ (tensor A X).flip.obj B).map v := by
  have hn := (tensorReassociationNatIso A f g W W' B eW eB d).hom.naturality v
  rw [tensorReassociationNatIso_app, tensorReassociationNatIso_app] at hn
  exact hn

private theorem tensorZero_natural
    (A : Type (u + 1)) [CommRing A] {X T : Scheme.{u}} (f : X ⟶ T)
    (W B : C A X) (e : W ≅ B) {K L : C A T} (v : K ⟶ L) :
    (inverseImage A (f ≫ 𝟙 T) ⋙ (tensor A X).flip.obj W).map v ≫
      (tensorZeroReassociation A f W B e L).hom =
    (tensorZeroReassociation A f W B e K).hom ≫
      (inverseImage A f ⋙ (tensor A X).flip.obj B).map v := by
  have hn := (tensorZeroNatIso A f W B e).hom.naturality v
  rw [tensorZeroNatIso_app, tensorZeroNatIso_app] at hn
  exact hn

private theorem source_natural
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) {K L : D P Y} (v : K ⟶ L) (d : ℕ) :
    (orderedSource P Y (d + 1)).map v ≫ (sourceReassociation P Y aY L d).hom =
      (sourceReassociation P Y aY K d).hom ≫
        (lineSource P (iteratedAffineLine Y d)).map ((orderedSource P Y d).map v) := by
  have he (M : D P Y) : HEq (sourceReassociation P Y aY M d).hom
      (sourceReassociationRaw P Y aY M d).2.2.hom := by
    unfold sourceReassociation
    exact (sourceReassociation_existsUnique P Y aY M d).exists.choose_spec
  have hK := he K
  have hL := he L
  cases d with
  | zero =>
    unfold orderedSource lineSource twistAction at hK hL ⊢
    rw [eq_of_heq hK, eq_of_heq hL]
    exact tensorZero_natural (Ring P) (lastProjection Y 0)
      (shiftedLine P (iteratedAffineLine Y 1))
      (coefficient P.coefficients.l P.extension (P.level - 1) Y P.level (annihilates P))
      (lineCoefficientIso P Y aY).symm v
  | succ d =>
    unfold orderedSource lineSource twistAction at hK hL ⊢
    rw [eq_of_heq hK, eq_of_heq hL]
    exact tensorReassociation_natural (Ring P) (lastProjection Y (d + 1))
      (iteratedAffineLineProj Y (d + 1))
      (shiftedLine P (iteratedAffineLine Y (d + 1)))
      (shiftedLine P (iteratedAffineLine Y (d + 2)))
      (coefficient P.coefficients.l P.extension (P.level - 1)
        (iteratedAffineLine Y (d + 1)) P.level (annihilates P))
      (shiftedLinePullback P (lastProjection Y (d + 1)) (towerBase aY (d + 1)))
      (lineCoefficientIso P (iteratedAffineLine Y (d + 1)) (towerBase aY (d + 1))).symm
      v (d + 1)

private theorem transposeComposition_natural
    {Cat Mid Out : Type v₁} [Category.{w₁} Cat] [Category.{w₁} Mid]
    [Category.{w₁} Out] (F : Cat ⥤ Mid) (G : Mid ⥤ Out) (H : Cat ⥤ Out)
    (P : ObjectProperty Cat) {M N W W' : Cat} {V V' : Mid} {K L : Out}
    (hM : P M) (hN : P N)
    (eMK : (H.obj M ⟶ K) ≃ (M ⟶ W))
    (eML : (H.obj M ⟶ L) ≃ (M ⟶ W'))
    (eNL : (H.obj N ⟶ L) ≃ (N ⟶ W'))
    (a : F.obj M ⟶ V) (a' : F.obj N ⟶ V')
    (b : G.obj V ⟶ K) (b' : G.obj V' ⟶ L)
    (e : P.ι ⋙ F ⋙ G ≅ P.ι ⋙ H)
    (s : M ⟶ N) (t : V ⟶ V') (v : K ⟶ L) (w : W ⟶ W')
    (hf : F.map s ≫ a' = a ≫ t) (hg : G.map t ≫ b' = b ≫ v)
    (hl : ∀ q : H.obj N ⟶ L, eML (H.map s ≫ q) = s ≫ eNL q)
    (hr : ∀ q : H.obj M ⟶ K, eML (q ≫ v) = eMK q ≫ w) :
    s ≫ transposeComposition F G H P hN eNL a' b' e =
      transposeComposition F G H P hM eMK a b e ≫ w := by
  have hc := e.inv.naturality (ObjectProperty.homMk s : ⟨M, hM⟩ ⟶ ⟨N, hN⟩)
  change H.map s ≫ e.inv.app ⟨N, hN⟩ =
    e.inv.app ⟨M, hM⟩ ≫ G.map (F.map s) at hc
  have hn : H.map s ≫ (e.inv.app ⟨N, hN⟩ ≫ G.map a' ≫ b') =
      (e.inv.app ⟨M, hM⟩ ≫ G.map a ≫ b) ≫ v := by
    rw [← Category.assoc, hc, Category.assoc, ← G.map_comp_assoc, hf,
      G.map_comp, Category.assoc, hg]
    simp only [Category.assoc]
  unfold transposeComposition
  exact (hl _).symm.trans ((congrArg eML hn).trans (hr _))

private theorem compositionInverse_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T S : Scheme.{u}} (f : X ⟶ T) (g : T ⟶ S)
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    [QuasiCompact f] [QuasiCompact g] [CompactSpace T] [CompactSpace S]
    (K L : Plus A S) (v : K.obj ⟶ L.obj) :
    (rightDerivedUpperShriek A f).map ((rightDerivedUpperShriek A g).map v) ≫
      compositionInverse A f g L =
    compositionInverse A f g K ≫ (rightDerivedUpperShriek A (f ≫ g)).map v := by
  have hM := plusEtaleOrigin_rightDerivedUpperShriek_obj f
    (plus_rightDerivedUpperShriek_obj g K.property)
  have hN := plusEtaleOrigin_rightDerivedUpperShriek_obj f
    (plus_rightDerivedUpperShriek_obj g L.property)
  exact transposeComposition_natural
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) g)
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (f ≫ g))
    (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X) hM hN
    (rightDerivedUpperShriekHomEquiv (f ≫ g) hM K.property)
    (rightDerivedUpperShriekHomEquiv (f ≫ g) hM L.property)
    (rightDerivedUpperShriekHomEquiv (f ≫ g) hN L.property)
    (rightDerivedUpperShriekCounit f _ (plus_rightDerivedUpperShriek_obj g K.property))
    (rightDerivedUpperShriekCounit f _ (plus_rightDerivedUpperShriek_obj g L.property))
    (rightDerivedUpperShriekCounit g K.obj K.property)
    (rightDerivedUpperShriekCounit g L.obj L.property)
    (originCompositionAmbient A f g)
    ((rightDerivedUpperShriek A f).map ((rightDerivedUpperShriek A g).map v))
    ((rightDerivedUpperShriek A g).map v) v ((rightDerivedUpperShriek A (f ≫ g)).map v)
    (rightDerivedUpperShriekCounit_naturality f
      (plus_rightDerivedUpperShriek_obj g K.property)
      (plus_rightDerivedUpperShriek_obj g L.property)
      ((rightDerivedUpperShriek A g).map v))
    (rightDerivedUpperShriekCounit_naturality g K.property L.property v)
    (fun q ↦ rightDerivedUpperShriekHomEquiv_naturality_left (f ≫ g) hM hN L.property
      ((rightDerivedUpperShriek A f).map ((rightDerivedUpperShriek A g).map v)) q)
    (fun q ↦ rightDerivedUpperShriekHomEquiv_naturality_right
      (f ≫ g) hM K.property L.property q v)

private theorem composite_natural
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K L : Plus (Ring P) Y) (v : K.obj ⟶ L.obj) (d : ℕ) :
    (rightDerivedUpperShriek (Ring P) (lastProjection Y d)).map
        ((exceptional P Y d).map v) ≫ exceptionalComposite P Y aY L d =
      exceptionalComposite P Y aY K d ≫ (exceptional P Y (d + 1)).map v := by
  have he (M : Plus (Ring P) Y) : HEq (exceptionalComposite P Y aY M d)
      (exceptionalCompositeRaw P Y aY M d).2.2 := by
    unfold exceptionalComposite
    exact (exceptionalComposite_existsUnique P Y aY M d).exists.choose_spec
  have hK := he K
  have hL := he L
  cases d with
  | zero =>
    let : HasCompactification (lastProjection Y 0 ≫ 𝟙 (iteratedAffineLine Y 0)) :=
      HasCompactification.of_eq (f := lastProjection Y 0) (Category.comp_id _).symm
    unfold exceptional at hK hL ⊢
    rw [eq_of_heq hK, eq_of_heq hL]
    exact (rightDerivedUpperShriekCongr (Ring P)
      (Category.comp_id (lastProjection Y 0)).symm).hom.naturality v
  | succ d =>
    let := (projection_geometry Y (d + 1)).2
    let := (projection_geometry Y (d + 2)).2
    let : HasCompactification
        (lastProjection Y (d + 1) ≫ iteratedAffineLineProj Y (d + 1)) :=
      HasCompactification.of_eq (f := iteratedAffineLineProj Y (d + 2))
        (iteratedAffineLineProj_succ Y (d + 1))
    let : IsNoetherian Y := tower_noetherian P Y aY 0
    let : IsNoetherian (iteratedAffineLine Y (d + 1)) := tower_noetherian P Y aY (d + 1)
    unfold exceptional at hK hL ⊢
    rw [eq_of_heq hK, eq_of_heq hL]
    exact compositionInverse_natural (Ring P) (lastProjection Y (d + 1))
      (iteratedAffineLineProj Y (d + 1)) K L v

private theorem lineExceptionalIso_natural
    (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})
    [(Etale.rightDerivedLowerShriekOfCompactification
      (ModuleCat.{u + 1} A) (affineTraceLineCompactification T)).IsLeftAdjoint]
    {K L : C A T} (v : K ⟶ L) :
    (sfFiniteExceptionalAt A (affineTraceLineCompactification T)).map v ≫
        (lineExceptionalIso A T L).hom =
      (lineExceptionalIso A T K).hom ≫
        (rightDerivedUpperShriek A (lastProjection T 0)).map v := by
  exact (CategoryTheory.Functor.isoWhiskerLeft
    (comparisonLowerStar (ModuleCat.{u + 1} A) T).rightDerivedFunctor
    (CategoryTheory.Functor.isoWhiskerRight
      ((Adjunction.ofIsLeftAdjoint
        (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} A) (affineTraceLineCompactification T))).rightAdjointUniq
        ((Etale.rightDerivedUpperShriekAdjunction A (lastProjection T 0)).ofNatIsoLeft
          (Etale.rightDerivedLowerShriekIso A (affineTraceLineCompactification T)).symm))
      (comparison A (AffineSpace PUnit.{u + 1} T)))).hom.naturality v

private theorem erase_identities {Cat : Type*} [Category* Cat]
    {A B X Y : Cat} (s : A ⟶ B) (a : A ⟶ X) (b : B ⟶ Y) (v : X ⟶ Y)
    (h : s ≫ (𝟙 B ≫ b) = (𝟙 A ≫ a) ≫ v) : s ≫ b = a ≫ v := by
  simpa only [Category.id_comp] using h

private theorem paste_two {Cat : Type*} [Category* Cat]
    {A B C A' B' C' : Cat} {s : A ⟶ A'} {t : B ⟶ B'} {v : C ⟶ C'}
    {a : A ⟶ B} {a' : A' ⟶ B'} {b : B ⟶ C} {b' : B' ⟶ C'}
    (ha : s ≫ a' = a ≫ t) (hb : t ≫ b' = b ≫ v) :
    s ≫ (a' ≫ b') = (a ≫ b) ≫ v := by
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc]

private theorem lineComparison_component
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) :
    lineComparison P Y aY K Ke hKe eK =
      affineLinePurityComparison P Y P.level (annihilates P) aY K Ke hKe eK ≫
        (lineExceptionalIso (Ring P) Y K.obj).hom := by
  unfold lineComparison
  have h : eqToHom (lineSource_obj_eq P Y K.obj) = 𝟙 _ := rfl
  exact (congrArg (fun q ↦ q ≫
    affineLinePurityComparison P Y P.level (annihilates P) aY K Ke hKe eK ≫
      (lineExceptionalIso (Ring P) Y K.obj).hom) h).trans
        (Category.id_comp _)

private theorem line_natural
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj)
    (L : Plus (Ring P) Y) (Le : Etale.DerivedCategoryModule (Ring P) Y)
    (hLe : etaleFiniteTor (Ring P) Y Le)
    (eL : (comparison (Ring P) Y).obj Le ≅ L.obj) (v : K.obj ⟶ L.obj) :
    (lineSource P Y).map v ≫ lineComparison P Y aY L Le hLe eL =
      lineComparison P Y aY K Ke hKe eK ≫
        (rightDerivedUpperShriek (Ring P) (lastProjection Y 0)).map v := by
  let : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType aY
  let c := affineTraceLineCompactification Y
  let Q := rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (Ring P)) c
  let MK : Plus (Ring P) (AffineSpace PUnit.{u + 1} Y) :=
    ⟨_, source_plus P.coefficients.l P.extension (P.level - 1) Y P.level
      (annihilates P) K.obj Ke hKe eK⟩
  let ML : Plus (Ring P) (AffineSpace PUnit.{u + 1} Y) :=
    ⟨_, source_plus P.coefficients.l P.extension (P.level - 1) Y P.level
      (annihilates P) L.obj Le hLe eL⟩
  let WK := sourceWitness P.coefficients.l P.extension (P.level - 1) Y P.level
    (annihilates P) K.obj Ke hKe eK
  let WL := sourceWitness P.coefficients.l P.extension (P.level - 1) Y P.level
    (annihilates P) L.obj Le hLe eL
  let aK := augmentation P.coefficients.l P.extension (P.level - 1) Y P.level
    (annihilates P) (primeUnit P Y aY) P.field.k aY K.obj Ke hKe eK
  let aL := augmentation P.coefficients.l P.extension (P.level - 1) Y P.level
    (annihilates P) (primeUnit P Y aY) P.field.k aY L.obj Le hLe eL
  have hn : Q.map ((lineSource P Y).map v) ≫ aL = aK ≫ v := by
    have h := AffineLineEvaluation.evaluation_naturality P Y aY K.obj L.obj
      Ke Le hKe hLe eK eL v
    have he (J : D P Y) : eqToHom (lineSource_obj_eq P Y J) = 𝟙 _ := rfl
    simp only [AffineLineEvaluation.evaluation, he] at h
    rw [CategoryTheory.Functor.map_id Q ((lineSource P Y).obj L.obj),
      CategoryTheory.Functor.map_id Q ((lineSource P Y).obj K.obj)] at h
    exact erase_identities (Q.map ((lineSource P Y).map v)) aK aL v h
  have hl := WeilConjectures.sfSpecifiedHomLeft (Ring P) c MK ML WK WL L
    ((lineSource P Y).map v) aL
  have hr := WeilConjectures.sfSpecifiedHomRight (Ring P) c MK WK K L aK v
  have ht : (lineSource P Y).map v ≫
      specifiedExceptionalHomEquiv (Ring P) c ML WL L aL =
      specifiedExceptionalHomEquiv (Ring P) c MK WK K aK ≫
        (sfFiniteExceptionalAt (Ring P) c).map v := by
    exact hl.symm.trans
      ((congrArg (specifiedExceptionalHomEquiv (Ring P) c MK WK L) hn).trans hr)
  have ht' : (lineSource P Y).map v ≫
      affineLinePurityComparison P Y P.level (annihilates P) aY L Le hLe eL =
    affineLinePurityComparison P Y P.level (annihilates P) aY K Ke hKe eK ≫
      (sfFiniteExceptionalAt (Ring P) c).map v := by
    unfold affineLinePurityComparison comparisonFromOrigin
    exact ht
  have he := lineExceptionalIso_natural (Ring P) Y v
  have hL := lineComparison_component P Y aY L Le hLe eL
  have hK := lineComparison_component P Y aY K Ke hKe eK
  exact (congrArg (fun q ↦ (lineSource P Y).map v ≫ q) hL).trans
    ((paste_two ht' he).trans
      (congrArg (fun q ↦ q ≫
        (rightDerivedUpperShriek (Ring P) (lastProjection Y 0)).map v) hK).symm)

private theorem paste_squares {T : Type*} [Category* T]
    {A₀ A₁ A₂ A₃ A₄ B₀ B₁ B₂ B₃ B₄ : T}
    {v₀ : A₀ ⟶ B₀} {v₁ : A₁ ⟶ B₁} {v₂ : A₂ ⟶ B₂}
    {v₃ : A₃ ⟶ B₃} {v₄ : A₄ ⟶ B₄}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} {d : A₃ ⟶ A₄}
    {a' : B₀ ⟶ B₁} {b' : B₁ ⟶ B₂} {c' : B₂ ⟶ B₃} {d' : B₃ ⟶ B₄}
    (ha : v₀ ≫ a' = a ≫ v₁) (hb : v₁ ≫ b' = b ≫ v₂)
    (hc : v₂ ≫ c' = c ≫ v₃) (hd : v₃ ≫ d' = d ≫ v₄) :
    v₀ ≫ (a' ≫ b' ≫ c' ≫ d') = (a ≫ b ≫ c ≫ d) ≫ v₄ := by
  simp only [Category.assoc]
  rw [reassoc_of% ha, reassoc_of% hb, reassoc_of% hc, hd]

/-- Naturality of the ordered comparison, with arbitrary retained ordinary origins.
Source: ordered affine transpose proof Step 2, naturality before the pasted-counit
calculation (blueprint: lem-pur-ordered-affine-comparison-natural).

Proof: for one line, the compactification projection is natural in the coefficient,
as are tensoring by its fixed integration and the coefficient unitor. Inverting the
projection preserves this naturality. The specified exceptional Hom equivalence is
natural in both variables; its source-origin witnesses affect only applicability.
Thus the affine-line comparison is natural, including between different origins.
Induct on d in the ordered recursion. At zero both functors and comparisons are
identities. At a successor, the pullback compositor, tensor comparison, Tate-line
comparison and tensor associator make sourceReassociation natural. The line comparison
is natural by the preceding calculation. The inverse exceptional compositor is natural:
it is the transpose of the pasted counit, and each counit and the compact-support
compositor is natural. Combining these three squares and the induction hypothesis
proves the displayed equation. The stage applicability theorem supplies each bounded
exceptional input. No exceptional adjunction outside the retained class is used. -/
theorem orderedAffineComparison_natural
    (P : WeilConjectures.PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj)
    (L : Plus (Ring P) Y) (Le : Etale.DerivedCategoryModule (Ring P) Y)
    (hLe : etaleFiniteTor (Ring P) Y Le)
    (eL : (comparison (Ring P) Y).obj Le ≅ L.obj) (v : K.obj ⟶ L.obj) (d : ℕ) :
    (orderedSource P Y d).map v ≫ affineSpacePurityComparison P Y aY L Le hLe eL d =
      affineSpacePurityComparison P Y aY K Ke hKe eK d ≫ (exceptional P Y d).map v := by
  induction d with
  | zero =>
    change v ≫ 𝟙 L.obj = 𝟙 K.obj ≫ v
    rw [Category.comp_id, Category.id_comp]
  | succ d ih =>
    let : LocallyOfFiniteType (towerBase aY d) := (tower_geometry aY d).1
    let : QuasiCompact (towerBase aY d) := (tower_geometry aY d).2.1
    let : IsSeparated (towerBase aY d) := (tower_geometry aY d).2.2
    have hs := source_natural P Y aY v d
    have hl := line_natural P (iteratedAffineLine Y d) (towerBase aY d)
      ⟨_, (stage_applicability P Y aY K Ke hKe eK d).1⟩
      (stageEtale P Y K.obj Ke d) (stage_applicability P Y aY K Ke hKe eK d).2
      (stageComparison P Y K.obj Ke eK d)
      ⟨_, (stage_applicability P Y aY L Le hLe eL d).1⟩
      (stageEtale P Y L.obj Le d) (stage_applicability P Y aY L Le hLe eL d).2
      (stageComparison P Y L.obj Le eL d) ((exceptional P Y d).map v)
    have hc := composite_natural P Y aY K L v d
    change (orderedSource P Y (d + 1)).map v ≫
        comparisonStep P Y aY L Le hLe eL d
          (affineSpacePurityComparison P Y aY L Le hLe eL d) =
      comparisonStep P Y aY K Ke hKe eK d
        (affineSpacePurityComparison P Y aY K Ke hKe eK d) ≫ _
    unfold comparisonStep
    refine paste_squares hs ?_ hl hc
    simpa only [CategoryTheory.Functor.map_comp] using
      congrArg (lineSource P (iteratedAffineLine Y d)).map ih

set_option maxHeartbeats 1600000 in
-- Compare the retained origins through the specified Hom equivalence, without unfolding it.
end AlgebraicGeometry.ProEtale.OrderedAffineTranspose
