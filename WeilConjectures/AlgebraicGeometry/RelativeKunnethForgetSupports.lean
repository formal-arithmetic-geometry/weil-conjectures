/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.RelativeMap
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionProper
import WeilConjectures.AlgebraicGeometry.RelativeKunnethCompositorForgetSupports
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange
import WeilConjectures.AlgebraicGeometry.ProperKunnethNormalizationAlgebra
import all WeilConjectures.AlgebraicGeometry.ProperRelativeKunnethSupports
import WeilConjectures.AlgebraicGeometry.EtaleKunnethSymmetricFactorization
import WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar

/-! # Forgetting supports in the relative compact-support product -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option Elab.async false
universe u v
open Lean Meta Elab Tactic
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local instance high] SymmetricCategory.toBraidedCategory
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

-- Reuse the generic diagram calculations without importing the proper-only product theory.
private theorem kunneth_inner_supports_algebra {D : Type v} [Category.{u + 1} D]
    (T : D ⥤ D ⥤ D)
    (s : ∀ M N : D, (T.obj M).obj N ≅ (T.obj N).obj M)
    (hs : ∀ {M M' : D} (a : M ⟶ M') (N : D),
      (T.obj N).map a ≫ (s M' N).inv = (s M N).inv ≫ (T.map a).app N)
    {Z Z' Q Q' K V : D}
    (e : Z ⟶ Q) (c : Q ⟶ Q') (a : Z ⟶ Z') (b : Z' ⟶ Q')
    (r : (T.obj Q).obj K ⟶ V) (r' : (T.obj Q').obj K ⟶ V)
    (hp : r = (T.map c).app K ≫ r') (he : e ≫ c = a ≫ b) :
    (s Z K).inv ≫ (T.map e).app K ≫ r =
      (T.obj K).map a ≫ (s Z' K).inv ≫ (T.map b).app K ≫ r' := by
  rw [hp]
  simp only [← NatTrans.comp_app_assoc, ← Functor.map_comp]
  rw [he]
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← reassoc_of% (hs a K)]

private theorem kunneth_tensor_inputs_swap_algebra {D : Type v} [Category.{u + 1} D]
    (T : D ⥤ D ⥤ D)
    (s : ∀ M N : D, (T.obj M).obj N ≅ (T.obj N).obj M)
    (hL : ∀ {M M' : D} (a : M ⟶ M') (N : D),
      (T.obj N).map a ≫ (s M' N).inv = (s M N).inv ≫ (T.map a).app N)
    (hR : ∀ (M : D) {N N' : D} (b : N ⟶ N'),
      (T.map b).app M ≫ (s M N').inv = (s M N).inv ≫ (T.obj M).map b)
    {M M' N N' : D} (a : M ⟶ M') (b : N ⟶ N') :
    (s N M).inv ≫ (T.map b).app M ≫ (T.obj N').map a =
      (T.map a).app N ≫ (T.obj M').map b ≫ (s N' M').inv := by
  rw [← reassoc_of% (hL b M)]
  rw [← hR N' a]
  rw [(T.map a).naturality_assoc b]



variable (A : Type (u + 1)) [CommRing A] [Finite A]

private theorem kunneth_exchange_forget {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) [HasCompactification f] [HasCompactification q]
    [QuasiCompact q] (E : DerivedCategoryModule A X) :
    (rightDerivedLowerShriekBaseChangeMap A sq).app E ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A)
          (HasCompactification.compactification q)).app
            ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E) =
      (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
          ((compactificationForgetSupports (ModuleCat.{u + 1} A)
            (HasCompactification.compactification f)).app E) ≫
        (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app E := by
  let c := HasCompactification.compactification f
  rw [rightDerivedLowerShriekBaseChangeMap_eq]
  simp only [rightDerivedLowerShriekBaseChangeMap', rightDerivedLowerShriekIso,
    compactificationForgetSupports, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj, Category.assoc, Functor.map_comp]
  rw [rightDerivedLowerShriekOfCompactificationIso_hom_app_comp_toLowerStar]
  exact rightDerivedLowerShriekOfCompactificationBaseChangeMap'_app_comp_toLowerStar _
    sq.toCommSq c (c.ofIsPullback sq) _ (c.isPullback_i_ofIsPullback sq)
    (IsPullback.of_hasPullback c.g g).toCommSq E

private theorem kunneth_projection_forget {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (projectionIsoApp A f E K).hom ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A)
          (HasCompactification.compactification f)).app
            (((derivedTensor (ModuleCat.{u + 1} A) X).obj E).obj
              ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((compactificationForgetSupports (ModuleCat.{u + 1} A)
          (HasCompactification.compactification f)).app E)).app K ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app E).app K := by
  exact projectionMapOfCompactification_comp_compactificationForgetSupports
    (ModuleCat.{u + 1} A) (HasCompactification.compactification f) E K

private theorem kunneth_inner_forget {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) [HasCompactification f] [HasCompactification q]
    [QuasiCompact q] (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (relativeKunnethInnerIso A sq E K).inv ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A)
          (HasCompactification.compactification q)).app
            (((derivedTensor (ModuleCat.{u + 1} A) W).obj
              ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E)).obj
                ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj K)) =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
          ((compactificationForgetSupports (ModuleCat.{u + 1} A)
            (HasCompactification.compactification f)).app E)) ≫
        (derivedTensorBraidingIso (ModuleCat.{u + 1} A) Y
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj
            ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj E)) K).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Y).map
          ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app E)).app K ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app
          ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E)).app K := by
  simp only [relativeKunnethInnerIso, Iso.trans_inv, Iso.symm_inv,
    Iso.app_inv, Functor.mapIso_inv,
    rightDerivedLowerShriekBaseChangeIso, asIso_hom, Category.assoc]
  have hi := kunneth_inner_supports_algebra (derivedTensor (ModuleCat.{u + 1} A) Y)
    (derivedTensorBraidingIso (ModuleCat.{u + 1} A) Y)
    (fun a N ↦ NatTrans.naturality_app (derivedTensorBraiding (ModuleCat.{u + 1} A) Y).inv N a)
    ((rightDerivedLowerShriekBaseChangeMap A sq).app E)
    ((compactificationForgetSupports (ModuleCat.{u + 1} A)
      (HasCompactification.compactification q)).app _)
    ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
      ((compactificationForgetSupports (ModuleCat.{u + 1} A)
        (HasCompactification.compactification f)).app E))
    ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app E)
    ((projectionIsoApp A q ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E) K).hom ≫
      (compactificationForgetSupports (ModuleCat.{u + 1} A)
        (HasCompactification.compactification q)).app _)
    (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) q).app _).app K)
    (kunneth_projection_forget A q _ K) (kunneth_exchange_forget A sq E)
  exact hi

-- Present the chosen forward comparison with the native lower-shriek functor as domain.
private def kunneth_native_forget {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] :
    R(f)_![ModuleCat.{u + 1} A] ⟶ R((f)_*[ModuleCat.{u + 1} A]) :=
  compactificationForgetSupports (ModuleCat.{u + 1} A)
    (HasCompactification.compactification f)

private theorem kunneth_native_projection_forget {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (projectionIsoApp A f E K).hom ≫
        (kunneth_native_forget A f).app
            (((derivedTensor (ModuleCat.{u + 1} A) X).obj E).obj
              ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((kunneth_native_forget A f).app E)).app K ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app E).app K := by
  simpa only [kunneth_native_forget] using kunneth_projection_forget A f E K

-- Present the ordinary projection with its native direct-image codomain.
omit [Finite A] in
private def kunneth_native_star_projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      ((R((f)_*[ModuleCat.{u + 1} A])).obj E)).obj K ⟶
      (R((f)_*[ModuleCat.{u + 1} A])).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj E).obj
          ((L((f)^*[ModuleCat.{u + 1} A])).obj K)) :=
  ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app E).app K

-- Keep the native domain and codomain while naming the underlying projection map.
omit [Finite A] in
private def kunneth_native_projection {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      ((R(f)_![ModuleCat.{u + 1} A]).obj E)).obj K ⟶
      (R(f)_![ModuleCat.{u + 1} A]).obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj E).obj
          ((L((f)^*[ModuleCat.{u + 1} A])).obj K)) :=
  ((projectionMap (ModuleCat.{u + 1} A) f).app E).app K

private theorem kunneth_native_projection_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (projectionIsoApp A f E K).hom = kunneth_native_projection A f E K := by
  rfl

private theorem kunneth_native_projection_forget_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    kunneth_native_projection A f E K ≫
        (kunneth_native_forget A f).app
            (((derivedTensor (ModuleCat.{u + 1} A) X).obj E).obj
              ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)) =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).map
        ((kunneth_native_forget A f).app E)).app K ≫
        kunneth_native_star_projection A f E K := by
  simpa only [kunneth_native_forget, kunneth_native_projection, kunneth_native_star_projection,
    projectionIsoApp_hom] using
    kunneth_projection_forget A f E K

private theorem kunneth_native_inner_forget {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) [HasCompactification f] [HasCompactification q]
    [QuasiCompact q] (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (relativeKunnethInnerIso A sq E K).inv ≫
        (kunneth_native_forget A q).app
            (((derivedTensor (ModuleCat.{u + 1} A) W).obj
              ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E)).obj
                ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj K)) =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj K).map
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
          ((kunneth_native_forget A f).app E)) ≫
        (derivedTensorBraidingIso (ModuleCat.{u + 1} A) Y
          ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj
            ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj E)) K).inv ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Y).map
          ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app E)).app K ≫
        kunneth_native_star_projection A q
          ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E) K := by
  simpa only [kunneth_native_forget, kunneth_native_star_projection] using
    kunneth_inner_forget A sq E K

private theorem kunneth_native_comp_forget {W X S : Scheme.{u}}
    (p : W ⟶ X) (f : X ⟶ S) (h : W ⟶ S) (w : p ≫ f = h)
    [HasCompactification p] [HasCompactification f] [HasCompactification h]
    [QuasiCompact h] (E : DerivedCategoryModule A W) :
    (rightDerivedLowerShriekCompIsoApp A p f h w E).inv ≫
        (kunneth_native_forget A h).app E =
      (R(f)_![ModuleCat.{u + 1} A]).map
          ((kunneth_native_forget A p).app E) ≫
        (kunneth_native_forget A f).app
            ((R((p)_*[ModuleCat.{u + 1} A])).obj E) ≫
        (rightDerivedLowerStarCompIsoOfComp
          (ModuleCat.{u + 1} A) p f h w).hom.app E := by
  simpa only [kunneth_native_forget] using
    relativeKunneth_compOfEq_forgetSupports A p f h w E

omit [Finite A] in
private theorem kunneth_native_ordinary_projection_nat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : DerivedCategoryModule A X) {K K' : DerivedCategoryModule A Y} (a : K ⟶ K') :
    kunneth_native_star_projection A f E K ≫
        (R((f)_*[ModuleCat.{u + 1} A])).map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj E).map
            ((L((f)^*[ModuleCat.{u + 1} A])).map a)) =
      ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
        ((R((f)_*[ModuleCat.{u + 1} A])).obj E)).map a ≫
        kunneth_native_star_projection A f E K' := by
  have hn := (kunnethProjection_naturality_right (ModuleCat.{u + 1} A) f E a).symm
  dsimp only [kunneth_native_star_projection, derivedTensorRightDerivedLowerStar,
    rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar, Functor.postcompose₂,
    Functor.whiskeringLeft₂, Functor.whiskeringLeft, Functor.whiskeringRight,
    Functor.comp_obj, Functor.comp_map, Functor.id_obj, catToReflQuiver] at hn ⊢
  run_tac support_transport_local `hn

section NativeNormalization

-- Expand the inverse word once, before the support-comparison calculation.
private theorem kunneth_four_iso_inverse {D : Type v} [Category.{u + 1} D]
    {X₀ X₁ X₂ X₃ X₄ : D} (i : X₀ ≅ X₁) (j : X₁ ≅ X₂)
    (k : X₂ ≅ X₃) (l : X₃ ≅ X₄) :
    (i ≪≫ j ≪≫ k ≪≫ l).inv = l.inv ≫ k.inv ≫ j.inv ≫ i.inv := by
  simp only [Iso.trans_inv, Category.assoc]

private theorem kunneth_relative_inverse_word {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) (h : W ⟶ S) (w : q ≫ g = h)
    [HasCompactification f] [HasCompactification g] [HasCompactification q]
    [HasCompactification h] [QuasiCompact q] [QuasiCompact h]
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (relativeKunnethIsoOfIsPullback A sq h w E K).inv =
      (derivedTensorBraidingIso (ModuleCat.{u + 1} A) S
          ((R(g)_![ModuleCat.{u + 1} A]).obj K)
          ((R(f)_![ModuleCat.{u + 1} A]).obj E)).inv ≫
        (projectionIsoApp A g K ((R(f)_![ModuleCat.{u + 1} A]).obj E)).symm.inv ≫
        ((R(g)_![ModuleCat.{u + 1} A]).mapIso
          (relativeKunnethInnerIso A sq E K)).inv ≫
        (rightDerivedLowerShriekCompIsoApp A q g h w _).inv := by
  exact kunneth_four_iso_inverse _ _ _ _

omit [Finite A] in
private theorem kunneth_native_swap_eq (Z : Scheme.{u})
    (M N : DerivedCategoryModule A Z) :
    supportedTensorSwapIso (ModuleCat.{u + 1} A) Z M N =
      derivedTensorBraidingIso (ModuleCat.{u + 1} A) Z M N := by
  rfl

attribute [local irreducible] _root_.DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian derivedTensor rightDerivedLowerShriek
  kunneth_native_forget kunneth_native_projection kunneth_native_star_projection
  HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  projectionMap projectionIsoApp rightDerivedLowerStarProjectionMap derivedBaseChangeMap
  rightDerivedLowerShriekBaseChangeMap kunnethMap

omit [Finite A] in
private theorem kunneth_native_symmetric_factorization {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) (h : W ⟶ S) (w : q ≫ g = h)
    (E : DerivedCategoryModule A X) (K : DerivedCategoryModule A Y) :
    (derivedTensorBraidingIso (ModuleCat.{u + 1} A) S
      ((R((g)_*[ModuleCat.{u + 1} A])).obj K)
      ((R((f)_*[ModuleCat.{u + 1} A])).obj E)).inv ≫
        kunneth_native_star_projection A g K
          ((R((f)_*[ModuleCat.{u + 1} A])).obj E) ≫
        (R((g)_*[ModuleCat.{u + 1} A])).map
          ((derivedTensorBraidingIso (ModuleCat.{u + 1} A) Y
            ((L((g)^*[ModuleCat.{u + 1} A])).obj
              ((R((f)_*[ModuleCat.{u + 1} A])).obj E)) K).inv ≫
            ((derivedTensor (ModuleCat.{u + 1} A) Y).map
              ((derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app E)).app K ≫
            kunneth_native_star_projection A q
              ((L((p)^*[ModuleCat.{u + 1} A])).obj E) K) ≫
        (rightDerivedLowerStarCompIsoOfComp
          (ModuleCat.{u + 1} A) q g h w).hom.app _ =
      kunnethMap (ModuleCat.{u + 1} A) p q f g h (sq.w.trans w) w E K := by
  have hk := (kunnethMap_symmetricFactorization (ModuleCat.{u + 1} A)
    p q f g h (sq.w.trans w) w E K).symm
  unfold kunneth_native_star_projection
  simp only [kunneth_native_swap_eq, Functor.map_comp, Category.assoc] at hk ⊢
  dsimp only [derivedTensorRightDerivedLowerStar,
    rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar, Functor.postcompose₂,
    Functor.whiskeringLeft₂, Functor.whiskeringLeft, Functor.whiskeringRight,
    Functor.comp_obj, Functor.id_obj, catToReflQuiver] at hk ⊢
  run_tac support_transport_local `hk

set_option maxHeartbeats 400000 in
-- Normalizing all six derived factors exceeds the default elaboration budget.
/-- The six-factor relative product respects the canonical forward forget-supports maps.
Source: thm-sf-kunneth-relative, proper-identification clause.
(blueprint: lem-sf-relative-kunneth-forget-supports).

Proof: reverse the six-factor word. The compositor followed by forget supports becomes
the ordinary compositor after the two forget-supports maps. The inner word becomes the
ordinary exchange/projection word by the projection and exchange squares. Naturality
moves the two outside coefficient comparisons past the braiding and projection. The
ordinary symmetric factorization identifies the remaining word with the ordinary Kunneth
map. This equation uses only forward forget-supports maps, so it holds without assuming
properness. For a proper factor its comparison is the canonical proper identification. -/
private theorem kunneth_native_normalization {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) (h : W ⟶ S) (w : q ≫ g = h)
    [HasCompactification f] [HasCompactification g] [HasCompactification q]
    [HasCompactification h] [QuasiCompact q] [QuasiCompact h]
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (relativeKunnethIsoOfIsPullback A sq h w E K).inv ≫
        (kunneth_native_forget A h).app
            (((derivedTensor (ModuleCat.{u + 1} A) W).obj
              ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E)).obj
                ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj K)) =
      ((derivedTensor (ModuleCat.{u + 1} A) S).map
          ((kunneth_native_forget A f).app E)).app
              ((R(g)_![ModuleCat.{u + 1} A]).obj K) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) S).obj
          ((R((f)_*[ModuleCat.{u + 1} A])).obj E)).map
            ((kunneth_native_forget A g).app K) ≫
        kunnethMap (ModuleCat.{u + 1} A) p q f g h (sq.w.trans w) w E K := by
  let C := ModuleCat.{u + 1} A
  let F := R(g)_![C]
  let G := R((g)_*[C])
  let eta : F ⟶ G :=
    kunneth_native_forget A g
  let a : (R(f)_![C]).obj E ⟶ (R((f)_*[C])).obj E :=
    (kunneth_native_forget A f).app E
  let b : F.obj K ⟶ G.obj K := eta.app K
  let t := (derivedTensorBraidingIso C Y
    ((upperStar C g).leftDerivedFunctor.obj ((lowerStar C f).rightDerivedFunctor.obj E)) K).inv ≫
    ((derivedTensor C Y).map ((derivedBaseChangeMap C sq.toCommSq).app E)).app K ≫
    kunneth_native_star_projection A q
      ((upperStar C p).leftDerivedFunctor.obj E) K
  have hInput := kunneth_tensor_inputs_swap_algebra (derivedTensor C S)
    (derivedTensorBraidingIso C S)
    (fun a N ↦ NatTrans.naturality_app (derivedTensorBraiding C S).inv N a)
    (fun M {N N'} b ↦ ((derivedTensorBraiding C S).inv.app M).naturality b) a b
  have hAlgebra := properKunnethNormalizationAlgebra F G eta
    (derivedTensorBraidingIso C S (F.obj K) ((R(f)_![C]).obj E)).inv
    (kunneth_native_projection A g K ((R(f)_![C]).obj E))
    (relativeKunnethInnerIso A sq E K).inv
    (rightDerivedLowerShriekCompIsoApp A q g h w _).inv
    ((kunneth_native_forget A h).app _)
    ((kunneth_native_forget A q).app _)
    ((rightDerivedLowerStarCompIsoOfComp C q g h w).hom.app _)
    (((derivedTensor C Y).obj K).map ((upperStar C g).leftDerivedFunctor.map a))
    t
    (((derivedTensor C S).map b).app ((R(f)_![C]).obj E))
    (kunneth_native_star_projection A g K ((R(f)_![C]).obj E))
    (((derivedTensor C S).obj (G.obj K)).map a)
    (kunneth_native_star_projection A g K
      ((lowerStar C f).rightDerivedFunctor.obj E))
    (((derivedTensor C S).map a).app (F.obj K) ≫
      ((derivedTensor C S).obj ((lowerStar C f).rightDerivedFunctor.obj E)).map b)
    (derivedTensorBraidingIso C S (G.obj K)
      ((lowerStar C f).rightDerivedFunctor.obj E)).inv
    (kunnethMap C p q f g h (sq.w.trans w) w E K)
    (by as_aux_lemma =>
      have hc := kunneth_native_comp_forget A q g h w
        (((derivedTensor C W).obj ((L((p)^*[C])).obj E)).obj
          ((L((q)^*[C])).obj K))
      dsimp only [C, F, G, a, b, eta] at hc ⊢
      run_tac support_transport_local `hc)
    (by as_aux_lemma =>
      have hi := kunneth_native_inner_forget A sq E K
      dsimp only [C, F, G, a, b, eta] at hi ⊢
      run_tac support_transport_local `hi)
    (by as_aux_lemma =>
      have hp := kunneth_native_projection_forget_map A g K ((R(f)_![C]).obj E)
      dsimp only [C, F, G, a, b, eta] at hp ⊢
      exact hp)
    (by as_aux_lemma =>
      have hn := kunneth_native_ordinary_projection_nat A g K a
      dsimp only [C, F, G, a, b, eta] at hn ⊢
      exact hn)
    (by as_aux_lemma =>
      simp only [Category.assoc] at hInput ⊢
      dsimp only [C, F, G, a, b, eta] at hInput ⊢
      run_tac support_transport_local `hInput)
    (by as_aux_lemma =>
      have hk := kunneth_native_symmetric_factorization A sq h w E K
      dsimp only [C, F, G, a, b, eta, t] at hk ⊢
      exact hk)
  rw [kunneth_relative_inverse_word]
  simp only [Iso.symm_inv, Functor.mapIso_inv, kunneth_native_projection_hom, Category.assoc]
  simp only [Category.assoc] at hAlgebra
  dsimp only [C, F, G, a, b, eta] at hAlgebra ⊢
  run_tac support_transport_local `hAlgebra

end NativeNormalization

/-- The six-factor relative product respects the canonical forward forget-supports maps.
Source: thm-sf-kunneth-relative, proper-identification clause.
(blueprint: lem-sf-relative-kunneth-forget-supports).

Proof: reverse the six-factor word. The compositor followed by forget supports becomes
the ordinary compositor after the two forget-supports maps. The inner word becomes the
ordinary exchange/projection word by the projection and exchange squares. Naturality
moves the two outside coefficient comparisons past the braiding and projection. The
ordinary symmetric factorization identifies the remaining word with the ordinary Kunneth
map. This equation uses only forward forget-supports maps, so it holds without assuming
properness. For a proper factor its comparison is the canonical proper identification. -/
theorem relativeKunneth_inv_forgetSupports {S X Y W : Scheme.{u}}
    {p : W ⟶ X} {q : W ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (sq : IsPullback p q f g) (h : W ⟶ S) (w : q ≫ g = h)
    [HasCompactification f] [HasCompactification g] [HasCompactification q]
    [HasCompactification h] [QuasiCompact q] [QuasiCompact h]
    (E : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (relativeKunnethIsoOfIsPullback A sq h w E K).inv ≫
        (compactificationForgetSupports (ModuleCat.{u + 1} A)
          (HasCompactification.compactification h)).app
            (((derivedTensor (ModuleCat.{u + 1} A) W).obj
              ((upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor.obj E)).obj
                ((upperStar (ModuleCat.{u + 1} A) q).leftDerivedFunctor.obj K)) =
      ((derivedTensor (ModuleCat.{u + 1} A) S).map
          ((compactificationForgetSupports (ModuleCat.{u + 1} A)
            (HasCompactification.compactification f)).app E)).app
              ((R(g)_![ModuleCat.{u + 1} A]).obj K) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) S).obj
          ((R((f)_*[ModuleCat.{u + 1} A])).obj E)).map
            ((compactificationForgetSupports (ModuleCat.{u + 1} A)
              (HasCompactification.compactification g)).app K) ≫
        kunnethMap (ModuleCat.{u + 1} A) p q f g h (sq.w.trans w) w E K := by
  simpa only [kunneth_native_forget] using kunneth_native_normalization A sq h w E K

end AlgebraicGeometry.Etale
