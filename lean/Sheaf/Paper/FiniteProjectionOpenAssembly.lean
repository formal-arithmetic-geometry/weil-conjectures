/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups C9, F1
-/
module

public import Sheaf.Paper.FiniteProjectionExchangeData
import Sheaf.Paper.FiniteProjectionOpenRestrictions
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence

/-! # Open restrictions and assembly of the compact projection diamond -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.FiniteProjectionExchange
variable (A : Type (u + 1)) [CommRing A] [Finite A]

-- Bifunctoriality, kept in the fixed-scalar coordinates of the statement.
omit [Finite A] in
@[reassoc] private theorem tensorMap_comp {X : Scheme.{u}} {K K' K'' M M' M'' : Dcat A X}
    (a : K ⟶ K') (a' : K' ⟶ K'') (b : M ⟶ M') (b' : M' ⟶ M'') :
    tensorMap A (a ≫ a') (b ≫ b') = tensorMap A a b ≫ tensorMap A a' b' := by
  exact (Functor.uncurry.obj (derivedTensor (ModuleCat A) X)).map_comp
    (Prod.mkHom a b) (Prod.mkHom a' b')

omit [Finite A] in
private theorem tensorMap_id {X : Scheme.{u}} (K M : Dcat A X) :
    tensorMap A (𝟙 K) (𝟙 M) = 𝟙 (tensor A X K M) := by
  exact (Functor.uncurry.obj (derivedTensor (ModuleCat A) X)).map_id (K, M)

omit [Finite A] in
private theorem tensorMap_left {X : Scheme.{u}} {K K' : Dcat A X} (a : K ⟶ K')
    (M : Dcat A X) : tensorMap A a (𝟙 M) =
      ((derivedTensor (ModuleCat A) X).map a).app M := by
  unfold tensorMap
  rw [((derivedTensor (ModuleCat A) X).obj K').map_id, Category.comp_id]

omit [Finite A] in
private theorem tensorMap_right {X : Scheme.{u}} (K : Dcat A X)
    {M M' : Dcat A X} (b : M ⟶ M') : tensorMap A (𝟙 K) b =
      ((derivedTensor (ModuleCat A) X).obj K).map b := by
  unfold tensorMap
  rw [(derivedTensor (ModuleCat A) X).map_id, NatTrans.id_app]
  exact Category.id_comp _

omit [Finite A] in
private theorem tensorMap_comp_left {X : Scheme.{u}} {K K' K'' : Dcat A X}
    (a : K ⟶ K') (a' : K' ⟶ K'') (M : Dcat A X) :
    tensorMap A (a ≫ a') (𝟙 M) = tensorMap A a (𝟙 M) ≫ tensorMap A a' (𝟙 M) := by
  simpa only [Category.comp_id] using tensorMap_comp A a a' (𝟙 M) (𝟙 M)

private theorem mu_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K K' M M' : Dcat A Y} (a : K ⟶ K') (b : M ⟶ M') :
    (pull A f).map (tensorMap A a b) ≫ (mu A f K' M').hom =
      (mu A f K M).hom ≫ tensorMap A ((pull A f).map a) ((pull A f).map b) := by
  have hn := NatTrans.naturality
    ((Functor.uncurry.mapIso (leftDerivedUpperStarTensorNatIso (ModuleCat A) f)).hom)
    (Prod.mkHom a b)
  dsimp only [leftDerivedUpperStarDerivedTensor, derivedTensorLeftDerivedUpperStar,
    Functor.uncurry_obj_map, Functor.uncurry_map_app, Functor.mapIso_hom,
    Functor.postcompose₂_obj_obj_map_app, Functor.postcompose₂_obj_obj_obj_map,
    Functor.whiskeringLeft₂_obj_obj_map_app_app,
    Functor.whiskeringLeft₂_obj_obj_obj_obj_map] at hn
  simpa only [tensorMap, Functor.map_comp, Category.assoc, pull, ext, tensor, mu,
    leftDerivedUpperStarTensorIso, Iso.app_hom, Functor.uncurry_obj_obj,
    Functor.postcompose₂_obj_obj_obj_obj,
    Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.whiskeringLeft₂_obj_obj_obj_map_app] using hn

-- Include equality-transport in the compositor, keeping the large derived functors closed.
@[irreducible] private def compEq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z) (e : k = f ≫ g) : pull A k ≅ pull A g ⋙ pull A f :=
  leftDerivedUpperStarCongr (ModuleCat A) e ≪≫ leftDerivedUpperStarComp (ModuleCat A) f g

omit [Finite A] in
private theorem compEq_assoc {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h) (K : Dcat A Z) :
    (compEq A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app K ≫
        (pull A f).map ((compEq A g h gh hgh).hom.app K) =
      (compEq A fg h fgh hfgh).hom.app K ≫
        (compEq A f g fg hfg).hom.app ((pull A h).obj K) := by
  subst fg gh fgh
  simpa only [compEq, leftDerivedUpperStarCongr_rfl, Iso.refl_trans,
    Iso.trans_hom, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Category.assoc] using
    (leftDerivedUpperStarComp_assoc_app (A := ModuleCat A) f g h K).symm

omit [Finite A] in
private theorem compEq_move_left {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h) (K : Dcat A Z) :
    (compEq A f g fg hfg).hom.app ((pull A h).obj K) ≫
        (pull A f).map ((compEq A g h gh hgh).inv.app K) =
      (compEq A fg h fgh hfgh).inv.app K ≫
        (compEq A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app K := by
  rw [← cancel_epi ((compEq A fg h fgh hfgh).hom.app K)]
  rw [← Category.assoc, ← compEq_assoc A f g h fg gh fgh hfg hgh hfgh K]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app_assoc]
  erw [(pull A f).map_id, Category.comp_id]

omit [Finite A] in
private theorem compEq_move_right {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h) (K : Dcat A Z) :
    (pull A f).map ((compEq A g h gh hgh).hom.app K) ≫
        (compEq A f g fg hfg).inv.app ((pull A h).obj K) =
      (compEq A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).inv.app K ≫
        (compEq A fg h fgh hfgh).hom.app K := by
  rw [← cancel_epi ((compEq A f gh fgh
    (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app K)]
  rw [← Category.assoc, compEq_assoc A f g h fg gh fgh hfg hgh hfgh K]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  erw [Iso.hom_inv_id_app, Category.comp_id]

omit [Finite A] in
private theorem compEq_move_inv {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h) (K : Dcat A Z) :
    (pull A f).map ((compEq A g h gh hgh).inv.app K) ≫
        (compEq A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).inv.app K =
      (compEq A f g fg hfg).inv.app ((pull A h).obj K) ≫
        (compEq A fg h fgh hfgh).inv.app K := by
  rw [← cancel_mono ((compEq A fg h fgh hfgh).hom.app K)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [(compEq_move_right A f g h fg gh fgh hfg hgh hfgh K).symm]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [(pull A f).map_id, Category.id_comp, Category.comp_id]

omit [Finite A] in
private theorem theta_compEq {B' B Y' Y : Scheme.{u}} {h : B' ⟶ B} {p' : B' ⟶ Y'}
    {p : B ⟶ Y} {g : Y' ⟶ Y} (s : CommSq h p' p g) :
    theta A s = (compEq A p' g (h ≫ p) s.w).symm ≪≫ compEq A h p (h ≫ p) rfl := by
  ext K
  simp only [theta, leftDerivedUpperStarSquareIso, compEq, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, NatTrans.comp_app, leftDerivedUpperStarCongr_rfl,
    Iso.refl_hom, Category.id_comp,
    leftDerivedUpperStarCongr_inv_app, Category.assoc]

omit [Finite A] in
private theorem compactification_compEq {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    leftDerivedUpperStarCompactificationIso (ModuleCat A) c =
      (compEq A c.i c.g f c.comm).symm := by
  have ht {X Y Z : Scheme.{u}} (i : X ⟶ Y) (p : Y ⟶ Z) (f : X ⟶ Z)
      (e : f = i ≫ p) :
      (leftDerivedUpperStarComp (ModuleCat A) i p).symm ≪≫
          eqToIso (congrArg (fun h ↦ pull A h) e.symm) = (compEq A i p f e).symm := by
    subst f
    simp only [compEq, leftDerivedUpperStarCongr_rfl, Iso.refl_trans,
      eqToIso_refl, Iso.trans_refl]
  exact ht c.i c.g f c.comm

omit [Finite A] in
private theorem square_compEq
    {X' X B' B Y' Y : Scheme.{u}} {a : X' ⟶ X} {i' : X' ⟶ B'} {i : X ⟶ B}
    {h : B' ⟶ B} {p' : B' ⟶ Y'} {p : B ⟶ Y} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : CommSq a f' f g)
    (si : CommSq a i' i h) (sp : CommSq h p' p g)
    (e : f = i ≫ p) (e' : f' = i' ≫ p') (L : Dcat A Y) :
    (pull A i').map ((theta A sp).hom.app L) ≫
        (theta A si).hom.app ((pull A p).obj L) ≫
        (pull A a).map ((compEq A i p f e).inv.app L) ≫
        (theta A s).inv.app L =
      (compEq A i' p' f' e').inv.app ((pull A g).obj L) := by
  simp only [theta_compEq, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Iso.symm_inv, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% (compEq_move_left A a i p (a ≫ i) f (a ≫ f)
    rfl e (by rw [Category.assoc, ← e]) L), Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% (compEq_move_right A i' h p (a ≫ i) (h ≫ p) (a ≫ f)
    si.w rfl (by rw [Category.assoc, ← e]) L), Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% (compEq_move_inv A i' p' g f' (h ≫ p) (a ≫ f)
    e' sp.w s.w L), Iso.inv_hom_id_app]
  erw [Category.comp_id]

omit [Finite A] in
private theorem compactification_square
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : CommSq a f' f g) (c : Compactification f)
    (c' : Compactification f') (h : c'.Z ⟶ c.Z)
    (si : CommSq a c'.i c.i h) (sp : CommSq h c'.g c.g g) (L : Dcat A Y) :
    (pull A c'.i).map
        ((theta A sp).hom.app L) ≫
      (theta A si).hom.app ((pull A c.g).obj L) ≫
      (pull A a).map ((leftDerivedUpperStarCompactificationIso (ModuleCat A) c).hom.app L) ≫
      (theta A s).inv.app L =
    (leftDerivedUpperStarCompactificationIso (ModuleCat A) c').hom.app
      ((pull A g).obj L) := by
  rw [compactification_compEq, compactification_compEq]
  exact square_compEq A s si sp c.comm c'.comm L

private theorem open_inverse_square
    {X' X B' B : Scheme.{u}} {a : X' ⟶ X} {j' : X' ⟶ B'}
    {j : X ⟶ B} {h : B' ⟶ B} [IsOpenImmersion j] [IsOpenImmersion j']
    (s : IsPullback a j' j h) (K : Dcat A X) (P : Dcat A B) :
    (mu A h ((ext A j).obj K) P).inv ≫
        (pull A h).map (gamma A j K P).hom ≫
        (beta A s).hom.app (tensor A X K ((pull A j).obj P)) =
      tensorMap A ((beta A s).hom.app K) (𝟙 ((pull A h).obj P)) ≫
        (gamma A j' ((pull A a).obj K) ((pull A h).obj P)).hom ≫
        (ext A j').map (tensorMap A (𝟙 ((pull A a).obj K))
          ((theta A s.toCommSq).hom.app P)) ≫
        (ext A j').map (mu A a K ((pull A j).obj P)).inv := by
  have ht := congrArg
    (fun z ↦ (mu A h ((ext A j).obj K) P).inv ≫ z ≫
      (ext A j').map (tensorMap A (𝟙 ((pull A a).obj K))
        ((theta A s.toCommSq).hom.app P) ≫ (mu A a K ((pull A j).obj P)).inv))
    (open_factor_routes A s K P).1
  simp only [openFirst, openSecond, Category.assoc, Iso.inv_hom_id_assoc,
    Functor.map_comp] at ht
  simp only [← Functor.map_comp, ← tensorMap_comp_assoc,
    Category.comp_id, Iso.inv_hom_id_app] at ht
  simp only [Functor.comp_obj, tensorMap_id, Iso.hom_inv_id,
    Category.id_comp, Functor.map_comp] at ht
  erw [(ext A j').map_id, Category.comp_id] at ht
  exact ht

section OpenAssemblyCalculation

-- Keep the derived-functor constructions closed during the diagram calculation.
-- The comparison API supplies all equations needed below.
attribute [local instance 30000] isNoetherian_of_finite
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf
  CategoryTheory.GrothendieckTopology.isGrothendieckAbelian_sheaf_proEtTopology
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.hasDerivedMonoidalCategory
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  Adjunction.derivedAdjunction upperStar lowerStar leftDerivedUpperStarComp
  leftDerivedUpperStarTensorComparison leftDerivedUpperStarTensorIso
  leftDerivedUpperStarTensorNatIso
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem compactification_open_aux
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : CommSq a f' f g) (c : Compactification f)
    (c' : Compactification f') (h : c'.Z ⟶ c.Z)
    (si : IsPullback a c'.i c.i h) (sp : CommSq h c'.g c.g g)
    (K : Dcat A X) (L : Dcat A Y) :
    tensorMap A (𝟙 ((pull A h).obj ((ext A c.i).obj K)))
        ((theta A sp).hom.app L) ≫
      (mu A h ((ext A c.i).obj K) ((pull A c.g).obj L)).inv ≫
      (pull A h).map (gamma A c.i K ((pull A c.g).obj L)).hom ≫
      (pull A h).map ((ext A c.i).map
        (tensorMap A (𝟙 K)
          ((leftDerivedUpperStarCompactificationIso (ModuleCat A) c).hom.app L))) ≫
      (beta A si).hom.app (tensor A X K ((pull A f).obj L)) ≫
      (ext A c'.i).map (mu A a K ((pull A f).obj L)).hom ≫
      (ext A c'.i).map (tensorMap A (𝟙 ((pull A a).obj K))
        ((theta A s).inv.app L)) =
    tensorMap A ((beta A si).hom.app K)
        (𝟙 ((pull A c'.g).obj ((pull A g).obj L))) ≫
      (gamma A c'.i ((pull A a).obj K)
        ((pull A c'.g).obj ((pull A g).obj L))).hom ≫
      (ext A c'.i).map (tensorMap A (𝟙 ((pull A a).obj K))
        ((leftDerivedUpperStarCompactificationIso (ModuleCat A) c').hom.app
          ((pull A g).obj L))) := by
  have oi := open_inverse_square A si K ((pull A c.g).obj L)
  have n₁ := (beta A si).hom.naturality
    (tensorMap A (𝟙 K) ((leftDerivedUpperStarCompactificationIso (ModuleCat A) c).hom.app L))
  dsimp only [Functor.comp_map] at n₁
  rw [reassoc_of% n₁, reassoc_of% oi]
  have e₁ := ((derivedTensor (ModuleCat A) c'.Z).map
      ((beta A si).hom.app K)).naturality
    ((theta A sp).hom.app L)
  have e₂ := ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat A)
      c'.i).inv.app ((pull A a).obj K)).naturality
    ((theta A sp).hom.app L)
  have e₃ := mu_naturality A a (𝟙 K)
    ((leftDerivedUpperStarCompactificationIso (ModuleCat A) c).hom.app L)
  erw [(pull A a).map_id K] at e₃
  simp only [tensorMap_right] at e₃
  have hC := compactification_square A s c c' h si.toCommSq sp L
  dsimp at e₁ e₂
  simp only [tensorMap_left, tensorMap_right]
  erw [reassoc_of% e₁, reassoc_of% e₂]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  congr 2
  congr 1
  rw [reassoc_of% e₃, Iso.inv_hom_id_assoc]
  simp only [← Functor.map_comp]
  rw [Category.assoc, hC]

end OpenAssemblyCalculation

private theorem pf_eq {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : Dcat A X) (L : Dcat A Y) :
    pf A c K L = pi A c.g ((ext A c.i).obj K) L ≫
      (push A c.g).map (gamma A c.i K ((pull A c.g).obj L)).hom ≫
      (push A c.g).map ((ext A c.i).map (tensorMap A (𝟙 K)
        ((leftDerivedUpperStarCompactificationIso (ModuleCat A) c).hom.app L))) := by
  rw [tensorMap_right]
  exact projectionMapOfCompactification_app_app (ModuleCat A) c K L

omit [Finite A] in
private theorem ex_eq {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g) (c : Compactification f)
    (K : Dcat A X) :
    ex A s c K = exchange A (c.isPullback_g_ofIsPullback s).flip.toCommSq
        ((ext A c.i).obj K) ≫
      (push A (c.ofIsPullback s).g).map
        ((beta A (c.isPullback_i_ofIsPullback s)).hom.app K) := by
  simp only [ex, rightDerivedLowerShriekOfCompactificationBaseChangeMap,
    rightDerivedLowerShriekOfCompactificationBaseChangeIso, beta,
    leftDerivedOpenImmersionLowerShriekBaseChangeIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.map_comp, Category.assoc]

section CompactificationSpecialization

private theorem compactification_diamond_of_factors
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g) (c : Compactification f)
    (c' : Compactification f') (h : c'.Z ⟶ c.Z)
    (si : IsPullback a c'.i c.i h) (sp : CommSq h c'.g c.g g)
    (e : rightDerivedLowerShriekOfCompactification (ModuleCat A) c ⋙ pull A g ⟶
      pull A a ⋙ rightDerivedLowerShriekOfCompactification (ModuleCat A) c')
    (he : ∀ T : Dcat A X, e.app T = exchange A sp ((ext A c.i).obj T) ≫
      (push A c'.g).map ((beta A si).hom.app T))
    (K : Dcat A X) (L : Dcat A Y)
    (hp : properFirst A sp ((ext A c.i).obj K) L =
      exchangeFirst A sp ((ext A c.i).obj K) L) :
    (pull A g).map (pf A c K L) ≫ e.app (tensor A X K ((pull A f).obj L)) ≫
        (rightDerivedLowerShriekOfCompactification (ModuleCat A) c').map
          (target A s K L) =
      (mu A g ((rightDerivedLowerShriekOfCompactification (ModuleCat A) c).obj K) L).hom ≫
        tensorMap A (e.app K) (𝟙 ((pull A g).obj L)) ≫
        pf A c' ((pull A a).obj K) ((pull A g).obj L) := by
  rw [he, he]
  have n₁ := (derivedBaseChangeMap (ModuleCat A) sp).naturality ((ext A c.i).map
    (tensorMap A (𝟙 K) ((leftDerivedUpperStarCompactificationIso (ModuleCat A) c).hom.app L)))
  have n₂ := (derivedBaseChangeMap (ModuleCat A) sp).naturality
    (gamma A c.i K ((pull A c.g).obj L)).hom
  have n₃ :
      tensorMap A ((push A c'.g).map ((beta A si).hom.app K)) (𝟙 ((pull A g).obj L)) ≫
        pi A c'.g ((ext A c'.i).obj ((pull A a).obj K)) ((pull A g).obj L) =
      pi A c'.g ((pull A h).obj ((ext A c.i).obj K)) ((pull A g).obj L) ≫
        (push A c'.g).map (tensorMap A ((beta A si).hom.app K)
          (𝟙 ((pull A c'.g).obj ((pull A g).obj L)))) := by
    have hn := NatTrans.congr_app
      ((rightDerivedLowerStarProjectionMap (ModuleCat A) c'.g).naturality
        ((beta A si).hom.app K)) ((pull A g).obj L)
    dsimp only [NatTrans.comp_app, derivedTensorRightDerivedLowerStar,
      rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar, Functor.comp_map,
      Functor.postcompose₂_obj_obj_map_app,
      Functor.whiskeringLeft₂_obj_obj_map_app_app, Functor.id_map] at hn
    simpa only [tensorMap_left, Functor.whiskeringLeft₂_obj_obj_obj_map_app,
      Functor.id_map, Functor.comp_obj] using hn
  have E2' :
      (pull A g).map (pi A c.g ((ext A c.i).obj K) L) ≫
        exchange A sp (tensor A c.Z ((ext A c.i).obj K) ((pull A c.g).obj L)) =
      (mu A g ((push A c.g).obj ((ext A c.i).obj K)) L).hom ≫
        tensorMap A (exchange A sp ((ext A c.i).obj K)) (𝟙 ((pull A g).obj L)) ≫
        pi A c'.g ((pull A h).obj ((ext A c.i).obj K)) ((pull A g).obj L) ≫
        (push A c'.g).map (tensorMap A (𝟙 ((pull A h).obj ((ext A c.i).obj K)))
          ((theta A sp).hom.app L)) ≫
        (push A c'.g).map (mu A h ((ext A c.i).obj K) ((pull A c.g).obj L)).inv := by
    have ht := congrArg (fun z ↦ z ≫
      (push A c'.g).map (tensorMap A (𝟙 ((pull A h).obj ((ext A c.i).obj K)))
        ((theta A sp).hom.app L) ≫
        (mu A h ((ext A c.i).obj K) ((pull A c.g).obj L)).inv)) hp
    simp only [properFirst, exchangeFirst, Functor.map_comp, Category.assoc] at ht
    simp only [← Functor.map_comp, ← tensorMap_comp_assoc,
      Category.comp_id, Iso.inv_hom_id_app] at ht
    simp only [Functor.comp_obj, tensorMap_id, Iso.hom_inv_id,
      Category.id_comp, Functor.map_comp] at ht
    erw [(push A c'.g).map_id, Category.comp_id] at ht
    exact ht
  have aux := compactification_open_aux A s.toCommSq c c' h si sp K L
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp] at aux
  rw [pf_eq, pf_eq]
  dsimp only [target, rightDerivedLowerShriekOfCompactification, derivedTensorRightDerivedLowerStar,
    derivedTensorRightDerivedLowerShriek, Functor.comp_obj]
  simp only [Functor.map_comp, Functor.comp_map, Category.assoc,
    tensorMap_comp_left]
  dsimp only [Functor.comp_map] at n₁ n₂
  rw [reassoc_of% n₁, reassoc_of% n₂, reassoc_of% E2']
  erw [reassoc_of% n₃]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  erw [aux]

-- Partial proof applications retain their inferred dependent types.
set_option linter.defProp false
private def diamond_base_changed
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g) (c : Compactification f) :=
  compactification_diamond_of_factors A s c (c.ofIsPullback s)

private def diamond_horizontal
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g) (c : Compactification f) :=
  diamond_base_changed A s c (pullback.fst c.g g)

private def diamond_squares
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g) (c : Compactification f) :=
  diamond_horizontal A s c (c.isPullback_i_ofIsPullback s)
    (c.isPullback_g_ofIsPullback s).flip.toCommSq

private def diamond_exchange
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g) (c : Compactification f) :=
  diamond_squares A s c
    (rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat A) s c)

private def diamond_specialized
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g) (c : Compactification f) :=
  diamond_exchange A s c (fun T ↦ ex_eq A s c T)

end CompactificationSpecialization

section InstanceCongruence
open Lean Meta

-- Explicit heterogeneous congruence keeps instance-proof comparisons local.
-- Every generated term is checked by the ordinary kernel.
private meta def unfoldCongrHead (e : Expr) : MetaM (Option Expr) := do
  match e with
  | .mdata _ b => return some b
  | .letE _ _ v b _ => return some (b.instantiate1 v)
  | .fvar id => return (← id.getDecl).value? (allowNondep := true)
  | .proj .. =>
    let r ← withTransparency .default (whnf e)
    return if r == e then none else some r
  | _ =>
    if let .const n us := e.getAppFn then
      let ci ← getConstInfo n
      if let .defnInfo _ := ci then
        return some ((← instantiateValueLevelParams ci us).beta e.getAppArgs)
    return none

private meta def asHEq (p : Expr) : MetaM Expr := do
  let ty ← inferType p
  if ty.isAppOf ``Eq then mkAppM ``heq_of_eq #[p] else pure p

private meta def isCoordinateHead (e : Expr) : Bool :=
  e.getAppFn.constName?.any fun n =>
    n.toString.startsWith "AlgebraicGeometry.ProEtale.FiniteProjectionExchange."

private meta def explicitInstanceCongr
    (cache : IO.Ref (Std.HashMap (Expr × Expr) Expr)) :
    Nat → Expr → Expr → Array (Expr × Expr × Expr) → MetaM Expr
  | 0, lhs, rhs, _ => throwError "Congruence depth exhausted: {lhs.getAppFn} / {rhs.getAppFn}"
  | fuel + 1, lhs₀, rhs₀, links => do
    let lhs := lhs₀.headBeta
    let rhs := rhs₀.headBeta
    let key := (lhs, rhs)
    if let some h := (← cache.get).get? key then return h
    let result ← do
      for (l, r, h) in links do
        if lhs == l && rhs == r then return h
      if lhs == rhs then return ← mkHEqRefl lhs
      if (← isProof lhs) && (← isProof rhs) then
        return mkApp4 (.const ``proof_irrel_heq []) (← inferType lhs) (← inferType rhs) lhs rhs
      if lhs.isLambda || rhs.isLambda then
        let lt ← whnf (← inferType lhs)
        let rt ← whnf (← inferType rhs)
        let .forallE ln la lb li := lt | throwError "Expected a function on the left"
        let .forallE rn ra rb ri := rt | throwError "Expected a function on the right"
        let hd ← explicitInstanceCongr cache fuel la ra links
        let hd ← mkAppM ``eq_of_heq #[hd]
        return ← withLocalDecl ln li la fun x => do
          withLocalDecl rn ri ra fun y => do
            withLocalDeclD `hxy (← mkHEq x y) fun hxy => do
              let h ← explicitInstanceCongr cache fuel (mkApp lhs x).headBeta
                (mkApp rhs y).headBeta (links.push (x, y, hxy))
              let h ← mkLambdaFVars #[x, y, hxy] h
              return ← mkAppOptM ``Function.hfunext
                #[some la, some ra, some (.lam ln la lb li), some (.lam rn ra rb ri),
                  some lhs, some rhs, some hd, some h]
      let lf := lhs.getAppFn
      let rf := rhs.getAppFn
      let la := lhs.getAppArgs
      let ra := rhs.getAppArgs
      if lf == rf && la.size == ra.size && !la.isEmpty then
        let thm ← mkHCongrWithArity lf la.size
        let mut args := #[]
        for l in la, r in ra, kind in thm.argKinds do
          let h ← explicitInstanceCongr cache fuel l r links
          let h ← match kind with
            | .eq => mkAppM ``eq_of_heq #[h]
            | .heq => pure h
            | _ => throwError "Unsupported congruence argument"
          args := args ++ #[l, r, h]
        return ← asHEq (mkAppN thm.proof args)
      if isCoordinateHead rhs then
        if let some r ← unfoldCongrHead rhs then
          return ← explicitInstanceCongr cache fuel lhs r links
      if let some l ← unfoldCongrHead lhs then
        return ← explicitInstanceCongr cache fuel l rhs links
      if let some r ← unfoldCongrHead rhs then
        return ← explicitInstanceCongr cache fuel lhs r links
      let shape := fun (e : Expr) => match e with
        | .const .. => "const"
        | .fvar .. => "fvar"
        | .lam .. => "lambda"
        | .forallE .. => "forall"
        | .mdata .. => "metadata"
        | .proj .. => "projection"
        | .letE .. => "let"
        | _ => "other"
      throwError "Congruence stopped at {shape lf}: {lf} / {shape rf}: {rf}"
    cache.modify (·.insert key result)
    return result

end InstanceCongruence

open Lean Meta Elab Tactic in
/-- Open-factor restriction identities and assembly with a supplied proper-factor equality.
Source: prop-sf-pf-coherence.proof.md, open-factor and base-change paragraphs.
(blueprint: lem-sf-finite-projection-open-assembly).

Proof: restrict the two open routes by j'^*. The open-unit normalization of beta,
gamma and gamma' replaces their restrictions by the canonical units. Naturality of
mu and tensor_square for (a,j',j,h) identify each remaining composite with
openSource. Both open routes are isomorphisms onto an object in the image of j'_!,
so full faithfulness of j'_! turns equality of their restrictions into equality of
these routes. Expand PF^c as the proper projection followed by the proper image of
gamma and the pullback-composition comparison. Expand Ex_!^c as proper exchange
followed by the proper image of beta. Naturality of proper exchange moves the image
of gamma through exchange; naturality of proper projection moves beta through the
projection. Substitute the supplied proper-factor equality and the open-route equality.
The pullback composition associativity identifies the two remaining target comparisons
with the one for the outside square. This gives the diamond equality. All maps are
actual fixed-scalar maps; no constructibility, absolute separatedness, or invertibility
of proper projection or exchange is used. -/
theorem open_factor_assembly
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (s : IsPullback a f' f g) (c : Compactification f)
    (K : Dcat A X) (L : Dcat A Y)
    (_hp : properFirst A (c.isPullback_g_ofIsPullback s).flip.toCommSq
        ((ext A c.i).obj K) L =
      exchangeFirst A (c.isPullback_g_ofIsPullback s).flip.toCommSq
        ((ext A c.i).obj K) L) :
    diamondLeft A s c K L = diamondRight A s c K L ∧
    (pull A (c.ofIsPullback s).i).map
        (openFirst A (c.isPullback_i_ofIsPullback s) K ((pull A c.g).obj L)) ≫
        openUnitInv A (c.ofIsPullback s).i _ =
      openSource A (c.isPullback_i_ofIsPullback s) K ((pull A c.g).obj L) ∧
    (pull A (c.ofIsPullback s).i).map
        (openSecond A (c.isPullback_i_ofIsPullback s) K ((pull A c.g).obj L)) ≫
        openUnitInv A (c.ofIsPullback s).i _ =
      openSource A (c.isPullback_i_ofIsPullback s) K ((pull A c.g).obj L) := by
  refine ⟨?_,
    (open_factor_routes A (c.isPullback_i_ofIsPullback s) K ((pull A c.g).obj L)).2.1,
    (open_factor_routes A (c.isPullback_i_ofIsPullback s) K ((pull A c.g).obj L)).2.2⟩
  have comparison := diamond_specialized A s c K L _hp
  run_tac do
    withMainContext do
      let p := mkFVar (← getLocalDeclFromUserName `comparison).fvarId
      let lhs ← instantiateMVars (← inferType p)
      let rhs ← instantiateMVars (← getMainTarget)
      let cache ← IO.mkRef ({} : Std.HashMap (Expr × Expr) Expr)
      let h ← explicitInstanceCongr cache 200 lhs rhs #[]
      let h ← mkAppM ``eq_of_heq #[h]
      let result ← mkAppM ``Eq.mp #[h, p]
      (← getMainGoal).assign result


end AlgebraicGeometry.ProEtale.FiniteProjectionExchange
