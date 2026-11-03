/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.PreservesSheafification

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
set_option linter.style.haveILetI false
/-! # Completed open-immersion base change

Source: blueprint order 1587; Stacks Tags 03DI, 09BP, 099N
(blueprint: lem-cbc-completed-extension-zero-comparison).
All extension functors below are the specified direct-sum presheaf followed by
module sheafification, transported along the ringed slice-site identification.
-/

/- LEGACY MODEL: withdrawn completed/adic coefficients.
Reviewer C-b7b9a required withdrawal of the proofs of
cbcCompletedPullback_complete_of_complete and cbcCompletedExchange_unique_of_complete,
and their three added proof imports. Those proofs must not be restored here.
The historical blueprint anchor above is deleted, and the four lem-route-cbc-* anchors
below have no current blueprint unit. Do not fill this legacy module's remaining holes.
Current open-immersion module operations use condensed coefficients; see blueprint
def-sfb-module-open-lower-shriek-adjunction. Any needed completed base-change statement
must be formulated in that model. This file is retained for existing consumers pending
the maintainer's coordinated legacy purge, rather than withdrawn in isolation.
In particular, `completedExtensionZeroComparison` and its four supporting
theorems below remain historical declarations with their original proof holes;
this source-level record prevents a future stage-3 worker from treating them as
the current condensed-coefficient target.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)


private local instance sliceFunctor_cocontinuous (T : Scheme.{t}) (W : T.ProEt) :
    (cbcSliceFunctor T W).IsCocontinuous ((ProEt.topology T).over W)
      (ProEt.topology W.left) :=
  ( (ProEt.sliceEquiv T W).toAdjunction.isCocontinuous_iff_coverPreserving
    ((ProEt.topology T).over W) (ProEt.topology W.left)).mpr (ProEt.sliceFrom_cover T W)

attribute [local irreducible] finiteSliceIso


private local instance overRing_limits {T : Scheme.{t}} (W : T.ProEt) :
    PreservesLimitsOfShape ℕᵒᵖ ((ProEt.topology T).overPullback CommRingCat.{t + 1} W) := by
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf ((ProEt.topology T).over W) CommRingCat.{t + 1})

private local instance sliceRing_limits {T : Scheme.{t}} (W : T.ProEt) :
    PreservesLimitsOfShape ℕᵒᵖ
      ((cbcSliceFunctor T W).sheafPushforwardContinuous CommRingCat.{t + 1}
        ((ProEt.topology T).over W) (ProEt.topology W.left)) := by
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf ((ProEt.topology T).over W) CommRingCat.{t + 1})

private local instance openSiteFunctor_cocontinuous {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (cbcOpenSiteFunctor j hj).IsCocontinuous (ProEt.topology U) (ProEt.topology T) :=
  ProEt.isCocontinuous_overMap (cbcOpenWeaklyEtale j hj)

private local instance openRing_limits {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    PreservesLimitsOfShape ℕᵒᵖ
      ((cbcOpenSiteFunctor j hj).sheafPushforwardContinuous CommRingCat.{t + 1}
        (ProEt.topology U) (ProEt.topology T)) := by
  exact preservesLimitsOfShape_of_reflects_of_preserves _
    (sheafToPresheaf (ProEt.topology U) CommRingCat.{t + 1})

private local instance openSliceFrom_continuous {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (ProEt.sliceFrom T (cbcOpenObject j hj)).IsContinuous (ProEt.topology U)
      ((ProEt.topology T).over (cbcOpenObject j hj)) := by
  have : (ProEt.sliceEquiv T (cbcOpenObject j hj)).functor.IsCocontinuous
      ((ProEt.topology T).over (cbcOpenObject j hj)) (ProEt.topology U) :=
    sliceFunctor_cocontinuous T (cbcOpenObject j hj)
  exact (ProEt.sliceEquiv T (cbcOpenObject j hj)).toAdjunction.isContinuous_of_isCocontinuous _ _

set_option maxHeartbeats 2000000 in
-- Unfolding the concrete composite adjunction and its generator formula needs more heartbeats.
open Classical in
attribute [local irreducible] rightFiniteOpenRing

variable {U' U X' X : Scheme.{t}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : AlgebraicGeometry.OpenImmersionSquare gU j' j g)

set_option maxHeartbeats 400000 in
-- Elaborating all four completed scalar-restriction functors needs a larger budget.
private theorem cbcCompletedExchange_endpoint_complete [QuasiCompact j]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal) :
    ∀ K : (cbcCompleteProperty d U r a ha).FullSubcategory,
      cbcCompleteProperty d X r a ha
          ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj) ∧
        cbcCompleteProperty d X' r a ha
          ((cbcCompletedPullback d g).obj
            ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj)) ∧
        cbcCompleteProperty d X' r a ha
          ((cbcDerivedOpenShriek d j' sq.isOpenImmersion').obj
            ((cbcCompletedPullback d gU).obj K.obj)) := by
  intro K
  have hleft := cbcOpenShriek_complete_of_complete d sq r a ha K K.property
  have hpull := cbcCompletedPullback_complete_of_complete d g r a ha
    ((cbcDerivedOpenShriek d j sq.isOpenImmersion).obj K.obj) hleft
  have hsq : IsPullback gU j' j g :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  have hqj' : QuasiCompact j' :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hsq inferInstance
  letI : QuasiCompact j' := hqj'
  let hi := IsPullback.id_horiz j'
  let sq' : OpenImmersionSquare (𝟙 U') j' j' (𝟙 X') :=
    { toCommSq := hi.toCommSq
      isoPullback := hi.isoPullback
      hom_fst := hi.isoPullback_hom_fst
      hom_snd := hi.isoPullback_hom_snd
      isOpenImmersion := sq.isOpenImmersion'
      isOpenImmersion' := sq.isOpenImmersion' }
  have hbase := cbcCompletedPullback_complete_of_complete d gU r a ha K.obj K.property
  have hright := cbcOpenShriek_complete_of_complete d sq' r a ha
    ⟨(cbcCompletedPullback d gU).obj K.obj, hbase⟩ hbase
  exact ⟨hleft, hpull, hright⟩

end AlgebraicGeometry.Scheme
