/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientDerivedFunctorAPI
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsAdjunctionQh
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPullMate
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MateCounit
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CompNatIsoCounit

/-! # Normalized exchange compatibility for scalar restriction

This comparison concerns arbitrary coefficient maps and arbitrary input complexes.
It contains neither a proper-base-change assertion nor a constructibility hypothesis.
(blueprint: lem-sp-original-integral-finite-quotient-mate-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable {A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
  (a : A ⟶ B) [IsMonHom a]

/-- The canonical restriction/direct-image isomorphism, obtained by conjugating the
existing derived extension/pullback isomorphism between composite left adjoints.
No flatness of the coefficient quotient is assumed or introduced.
(blueprint: lem-sp-original-integral-finite-quotient-mate-transport) -/
def originalIntegralRestrictionPushIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    coefficientDerivedLowerStar B f ⋙ D(Mod.comap (coefficientMap a Y)) ≅
      D(Mod.comap (coefficientMap a X)) ⋙ coefficientDerivedLowerStar A f :=
  ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y)).comp
      (derivedUpperStarLowerStarAdjunction B f)).rightAdjointUniq
    (((derivedUpperStarLowerStarAdjunction A f).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))).ofNatIsoLeft
        (derivedUpperStarExtendScalarsIso a f))

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
  {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- Source comparison assembled from the fixed restriction/pullback comparison and
canonical conjugate direct-image comparison.
(blueprint: lem-sp-original-integral-finite-quotient-mate-transport) -/
def originalIntegralRestrictionExchangeSource
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj B X))) :
    (coefficientDerivedUpperStar A g).obj
        ((coefficientDerivedLowerStar A f).obj (D(Mod.comap (coefficientMap a X)).obj K)) ≅
      D(Mod.comap (coefficientMap a Y')).obj
        ((coefficientDerivedUpperStar B g).obj ((coefficientDerivedLowerStar B f).obj K)) :=
  (coefficientDerivedUpperStar A g).mapIso
      ((originalIntegralRestrictionPushIso a f).app K).symm ≪≫
    (derivedComapLeftDerivedUpperStarIso a g).app ((coefficientDerivedLowerStar B f).obj K)

/-- Target comparison using the same fixed pullback and direct-image comparisons.
(blueprint: lem-sp-original-integral-finite-quotient-mate-transport) -/
def originalIntegralRestrictionExchangeTarget
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj B X))) :
    (coefficientDerivedLowerStar A f').obj
        ((coefficientDerivedUpperStar A g').obj (D(Mod.comap (coefficientMap a X)).obj K)) ≅
      D(Mod.comap (coefficientMap a Y')).obj
        ((coefficientDerivedLowerStar B f').obj ((coefficientDerivedUpperStar B g').obj K)) :=
  (coefficientDerivedLowerStar A f').mapIso
      ((derivedComapLeftDerivedUpperStarIso a g').app K) ≪≫
    ((originalIntegralRestrictionPushIso a f').app
      ((coefficientDerivedUpperStar B g').obj K)).symm

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedUpperStarLowerStarAdjunction
  Mod.derivedExtendMapDerivedCategoryAdjunction

set_option maxHeartbeats 2000000 in
-- The concrete derived module-object functors require a larger elaboration budget.
private theorem restriction_pullback_comp
    {U V W : Scheme.{u}} (h : U ⟶ V) (k : V ⟶ W) :
    NatTrans.SquareCompatible
      (T := D(Mod.comap (coefficientMap a W)))
      (T' := D(Mod.comap (coefficientMap a U)))
      (derivedComapLeftDerivedUpperStarIso a (h ≫ k)).symm
      (Functor.pasteSquareIso (derivedComapLeftDerivedUpperStarIso a k).symm
        (derivedComapLeftDerivedUpperStarIso a h).symm)
      (coefficientDerivedUpperStarComp B h k).hom
      (coefficientDerivedUpperStarComp A h k).hom := by
  intro N
  have hc := derivedComapLeftDerivedUpperStarIso_comp_hom_app a h k N
  apply (cancel_mono ((Functor.pasteSquareIso
    (derivedComapLeftDerivedUpperStarIso a k).symm
    (derivedComapLeftDerivedUpperStarIso a h).symm).inv.app N)).1
  simp only [Category.assoc, Iso.hom_inv_id_app]
  simp only [Functor.pasteSquareIso_inv_app, Iso.symm_inv, Iso.symm_hom]
  change _ = _ ≫ (leftDerivedUpperStarComp A h k).hom.app _ ≫ _ ≫ _
  rw [hc]
  simp only [Iso.inv_hom_id_app_assoc]
  exact Category.comp_id _

set_option maxHeartbeats 2000000 in
-- The concrete derived module-object functors require a larger elaboration budget.
set_option maxHeartbeats 2000000 in
-- The concrete derived module-object functors require a larger elaboration budget.
private theorem restriction_pullback_square (sq : CommSq g' f' f g) :
    NatTrans.SquareCompatible
      (T := D(Mod.comap (coefficientMap a Y)))
      (T' := D(Mod.comap (coefficientMap a X')))
      (Functor.pasteSquareIso (derivedComapLeftDerivedUpperStarIso a g).symm
        (derivedComapLeftDerivedUpperStarIso a f').symm)
      (Functor.pasteSquareIso (derivedComapLeftDerivedUpperStarIso a f).symm
        (derivedComapLeftDerivedUpperStarIso a g').symm)
      (coefficientAmbientSquare B sq).hom (coefficientAmbientSquare A sq).hom := by
  rw [coefficientAmbientSquare_eq, coefficientAmbientSquare_eq,
    coefficientIsoTransThree_eq, coefficientIsoTransThree_eq]
  exact (restriction_pullback_comp a f' g).inv.comp
    ((restriction_pullback_congr a sq.w.symm).comp (restriction_pullback_comp a g' f))

private theorem rightAdjointUniq_ofNatIsoLeft
    {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} {R S : D ⥤ C} (adj : F ⊣ R) (adj' : G ⊣ S) (e : G ≅ F) :
    (adj.rightAdjointUniq (adj'.ofNatIsoLeft e)).hom =
      conjugateEquiv adj adj' e.hom := by
  ext K
  simp [Adjunction.rightAdjointUniq, conjugateEquiv_apply_app,
    Adjunction.ofNatIsoLeft, Category.assoc]

set_option maxHeartbeats 2000000 in
-- The concrete derived module-object functors require a larger elaboration budget.
private theorem restrictionPush_mate {U V : Scheme.{u}} (h : U ⟶ V) :
    (coefficientDerivedAdjunction B h).IsMateSquare (coefficientDerivedAdjunction A h)
      (derivedComapLeftDerivedUpperStarIso a h).symm
      (originalIntegralRestrictionPushIso a h) := by
  rw [coefficientDerivedAdjunction_eq, coefficientDerivedAdjunction_eq,
    Adjunction.isMateSquare_iff]
  unfold originalIntegralRestrictionPushIso
  rw [rightAdjointUniq_ofNatIsoLeft]
  have hm := conjugateEquiv_comp_eq_mateEquiv_mateEquiv
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a V))
    (derivedUpperStarLowerStarAdjunction B h) (derivedUpperStarLowerStarAdjunction A h)
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a U))
    (derivedUpperStarExtendScalarsIso a h).hom
  rw [derivedUpperStarExtendScalarsMateNormalization] at hm
  exact hm.symm

set_option maxHeartbeats 2000000 in
-- The concrete derived module-object functors require a larger elaboration budget.
/-- Scalar restriction intertwines the two specified exchange morphisms through the
canonical comparisons, including their normalization by the actual derived adjunctions.

Source: Bhatt--Scholze, Section 6.1; the unit--square--counit definition of exchange.

Proof in words. The underived extension/pullback isomorphism is the mate of the inverse
restriction/pullback comparison. Derive this identity on K-flat resolutions, using the
counit formula for the derived extension/restriction adjunction. Conjugating the resulting
identity between composite left adjoints shows that originalIntegralRestrictionPushIso
is the geometric right mate of the exact restriction/pullback comparison. Hence its unit
and counit equations hold with these specific maps. The restriction/pullback comparisons
respect composition: this is derivedComapLeftDerivedUpperStarIso_comp_hom_app. Apply it to
both paths around sq, and cancel the comparison for their common composite; this gives the
pullback cube, including the equality transport by sq.w. Paste the unit, cube, and counit
squares. Their two endpoint maps are exactly the displayed source and target comparisons.
This is an equality for every complex and coefficient map, without any properness,
constructibility, torsion, or invertibility-of-exchange assumption. In particular it remains
an equality for empty schemes and the zero ring.
(blueprint: lem-sp-original-integral-finite-quotient-mate-transport) -/
theorem originalIntegralFiniteQuotientMateTransport
    (sq : ChosenCartesianSquare g' f' f g)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj B X))) :
    (refinementAmbientExchange A sq).app (D(Mod.comap (coefficientMap a X)).obj K) ≫
        (originalIntegralRestrictionExchangeTarget a (f' := f') (g' := g') K).hom =
      (originalIntegralRestrictionExchangeSource a (f := f) (g := g) K).hom ≫
        D(Mod.comap (coefficientMap a Y')).map ((refinementAmbientExchange B sq).app K) := by
  have hex := NatTrans.SquareCompatible.exchangeRight
    (restrictionPush_mate a f) (restrictionPush_mate a f')
    (restriction_pullback_square a sq.toCommSq)
  have h := square_inverse _ _ _ _ hex K
  simp only [Functor.pasteSquareIso_inv_app, Iso.symm_inv] at h
  dsimp only [coefficientDerivedUpperStar, coefficientDerivedLowerStar] at h ⊢
  simpa only [originalIntegralRestrictionExchangeSource,
    originalIntegralRestrictionExchangeTarget, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc, refinementAmbientExchange,
    Adjunction.exchangeRight_app, mateEquiv_apply, TwoSquare.mk, TwoSquare.natTrans,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.rightUnitor_inv_app,
    Functor.leftUnitor_hom_app, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Functor.map_id, Category.id_comp, Category.comp_id, Iso.app_inv,
    coefficientDerivedUpperStar, coefficientDerivedLowerStar, Functor.id_obj, Functor.id_map]
    using h

end AlgebraicGeometry.ProEtale.CondensedRing
