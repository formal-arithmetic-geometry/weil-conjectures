/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import all WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.PreservesSheafification

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
/-! # Completed open-immersion base change

Source: blueprint order 1587; Stacks Tags 03DI, 09BP, 099N
(blueprint: lem-cbc-completed-extension-zero-comparison).
All extension functors below are the specified direct-sum presheaf followed by
module sheafification, transported along the ringed slice-site identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme
variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The concrete localization functor is continuous.
Source: Tags 098K, 094T, 0951 (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: the functor keeps the underlying schemes and arrows. The pro-etale covering
condition is the same finite affine fpqc covering condition on those arrows;
therefore inverse images of covering sieves cover. This is exactly the site
identification in weaklyEtale_localization, with its concrete underlying maps. -/
@[instance] theorem cbcSliceFunctor_continuous (T : Scheme.{t}) (W : T.ProEt) :
    (cbcSliceFunctor T W).IsContinuous ((ProEt.topology T).over W)
      (ProEt.topology W.left) := by
  have : (ProEt.sliceEquiv T W).symm.functor.IsCocontinuous (ProEt.topology W.left)
      ((ProEt.topology T).over W) := ProEt.sliceFrom_cocont T W
  exact (ProEt.sliceEquiv T W).symm.toAdjunction.isContinuous_of_isCocontinuous
    (ProEt.topology W.left) ((ProEt.topology T).over W)

-- These private coefficient constructions also occur in RingedOpenStrictReduction.
-- That module imports this one, so we construct them here without importing it.

attribute [local irreducible] finiteSliceIso

/-- Extension by zero is additive.
Source: Tag 03DI (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: the slice transport keeps addition of maps; direct sums and module
sheafification are additive. Their composite is therefore additive. -/
@[instance] theorem cbcOpenShriek_additive {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) : (cbcOpenShriek d j hj).Additive := by
  have : (cbcModuleToSlice d T (cbcOpenObject j hj)).Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  change (cbcModuleToSlice d T (cbcOpenObject j hj) ⋙
    SheafOfModules.localizedSystemExtension.{t + 1, t, t + 1}
      (completedReductionCoefficient T d) (cbcOpenObject j hj)).Additive
  infer_instance

/-- Extension by zero is exact, without any quasi-compactness assumption.
Source: Tag 03DJ (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: restriction to a slice is exact and its direct-sum/sheafification left
adjoint is exact. Ringed slice transport is an equivalence. The argument is
unchanged at distinct site object and Hom universes; equivalently transport to
AsSmall at t+1, apply the recorded localization theorem, and transport back. -/
@[instance] theorem cbcOpenShriek_finiteLimits {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) : PreservesFiniteLimits (cbcOpenShriek d j hj) := by
  have : (cbcSliceFunctor T (cbcOpenObject j hj)).IsContinuous
      ((ProEt.topology T).over (cbcOpenObject j hj)) (ProEt.topology U) :=
    cbcSliceFunctor_continuous T (cbcOpenObject j hj)
  let F := cbcModuleToSlice d T (cbcOpenObject j hj)
  let G := SheafOfModules.toSheaf
    ((reductionModuleRing T (completedReductionCoefficient T d)).over (cbcOpenObject j hj))
  have : PreservesFiniteLimits (F ⋙ G) := by
    change PreservesFiniteLimits
      (SheafOfModules.toSheaf (reductionModuleRing U (completedReductionCoefficient U d)) ⋙
        (cbcSliceFunctor T (cbcOpenObject j hj)).sheafPushforwardContinuous
          AddCommGrpCat.{t + 1} ((ProEt.topology T).over (cbcOpenObject j hj))
            (ProEt.topology U))
    infer_instance
  have : PreservesFiniteLimits F := preservesFiniteLimits_of_reflects_of_preserves F G
  change PreservesFiniteLimits (F ⋙
    SheafOfModules.localizedSystemExtension.{t + 1, t, t + 1}
      (completedReductionCoefficient T d) (cbcOpenObject j hj))
  infer_instance

/-- Extension by zero preserves finite colimits.
Source: Tag 03DI (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: it is left adjoint to restriction, via the direct-sum Hom bijection and
sheafification. Hence it preserves colimits, in particular finite colimits. -/
@[instance] theorem cbcOpenShriek_finiteColimits {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) : PreservesFiniteColimits (cbcOpenShriek d j hj) := by
  have h : cbcCompletedSliceMap d T (cbcOpenObject j hj) =
      (completedSliceIso (cbcOpenObject j hj) d).hom :=
    (cbcCompletedSliceMap_exists d T (cbcOpenObject j hj)).unique
      (cbcCompletedSliceMap_exists d T (cbcOpenObject j hj)).exists.choose_spec
      (completedSliceIso_projection (cbcOpenObject j hj) d)
  have : IsIso (cbcCompletedSliceMap d T (cbcOpenObject j hj)) := by
    rw [h]
    infer_instance
  have : (cbcSliceFunctor T (cbcOpenObject j hj)).IsEquivalence :=
    inferInstanceAs (ProEt.sliceEquiv T (cbcOpenObject j hj)).functor.IsEquivalence
  let F := cbcModuleToSlice d T (cbcOpenObject j hj)
  have : F.IsLeftAdjoint := by
    dsimp only [F, cbcModuleToSlice]
    infer_instance
  have : PreservesFiniteColimits F := inferInstance
  change PreservesFiniteColimits (F ⋙
    SheafOfModules.localizedSystemExtension.{t + 1, t, t + 1}
      (completedReductionCoefficient T d) (cbcOpenObject j hj))
  infer_instance

/-- Open-site composition is continuous.
Source: Tag 098K (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: its maps are unchanged scheme arrows and hence preserve the finite-affine
fpqc covering condition. This is the inverse side of slice-site localization. -/
@[instance] theorem cbcOpenSiteFunctor_continuous {U T : Scheme.{t}}
    (j : U ⟶ T) (hj : IsOpenImmersion j) :
    (cbcOpenSiteFunctor j hj).IsContinuous (ProEt.topology U) (ProEt.topology T) := by
  let := hj
  exact ProEt.isContinuous_overMap (inferInstance : WeaklyEtale j)

attribute [local irreducible] rightFiniteOpenRing

variable {U' U X' X : Scheme.{t}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : AlgebraicGeometry.OpenImmersionSquare gU j' j g)

/-- Ordinary open base change is invertible for the cartesian square.
Source: blueprint order 1587, Step 7 (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: right exchange restricts along the cartesian comparison isomorphism, hence
is invertible. Its adjoint conjugate is invertible. This is the usual finite
coefficient open base-change map, with completed coefficient scalar actions. -/
@[instance] theorem cbcUnderivedInverseExchange_isIso :
    IsIso (cbcUnderivedInverseExchange d sq) := by
  have hsq := IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback
    sq.hom_fst sq.hom_snd
  have := MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (cbcOpenWeaklyEtale j sq.isOpenImmersion)
    (cbcOpenWeaklyEtale j' sq.isOpenImmersion') hsq
  have hη (M : pbcModules X' (pbcAdicCompletion X' d)) (V : U.ProEtᵒᵖ) :
      IsIso (((cbcRightExchange d sq).app M).val.app V) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    have hb := ConcreteCategory.bijective_of_isIso
      (M.val.presheaf.map
        ((MorphismProperty.Over.pullbackMapComparison
          (cbcOpenWeaklyEtale j sq.isOpenImmersion)
          (cbcOpenWeaklyEtale j' sq.isOpenImmersion') sq.toCommSq).app V.unop).op)
    have he : ⇑(((cbcRightExchange d sq).app M).val.app V) =
        ⇑(M.val.presheaf.map
          ((MorphismProperty.Over.pullbackMapComparison
            (cbcOpenWeaklyEtale j sq.isOpenImmersion)
            (cbcOpenWeaklyEtale j' sq.isOpenImmersion') sq.toCommSq).app V.unop).op) := by
      funext x
      exact (cbcRightExchange_exists d sq).exists.choose_spec M V x
    exact he ▸ hb
  have hM (M : pbcModules X' (pbcAdicCompletion X' d)) :
      IsIso ((cbcRightExchange d sq).app M) := by
    let e := PresheafOfModules.isoMk
      (fun V ↦ asIso (((cbcRightExchange d sq).app M).val.app V))
      (fun {_ _} f ↦ ((cbcRightExchange d sq).app M).val.naturality f)
    have he : e.hom = ((cbcRightExchange d sq).app M).val := by
      ext V x
      rfl
    have : IsIso ((SheafOfModules.forget _).map ((cbcRightExchange d sq).app M)) := by
      change IsIso (((cbcRightExchange d sq).app M).val)
      rw [← he]
      infer_instance
    exact isIso_of_reflects_iso ((cbcRightExchange d sq).app M) (SheafOfModules.forget _)
  have : IsIso (cbcRightExchange d sq) := NatIso.isIso_of_isIso_app _
  dsimp only [cbcUnderivedInverseExchange]
  infer_instance

/-- The derived mate remains an isomorphism.
Source: blueprint order 1587, Step 7 (blueprint: lem-cbc-completed-extension-zero-comparison).
Proof: on each K-flat representative the normalized derived exchange is a
composition of invertible counits and the termwise underived base-change
isomorphism. Every derived object has such a representative; hence every
component is an isomorphism, so the natural transformation is an isomorphism. -/
@[instance] theorem cbcDerivedInverseExchange_isIso :
    IsIso (cbcDerivedInverseExchange d sq) := by
  have hrep (K : DerivedCategory (pbcModules U (pbcAdicCompletion U d))) :
      ∃ P, CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d) P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ K) := by
    let : EssentiallySmall.{t + 1} U.ProEt := essentiallySmallSelf.{0, t, t + 1} _
    let : HasSheafify (ProEt.topology U) AddCommGrpCat.{t + 1} :=
      WeilConjectures.integralCoefficientAbSheafify.{t, 0} U
    let : (ProEt.topology U).WEqualsLocallyBijective AddCommGrpCat.{t + 1} :=
      WeilConjectures.integralCoefficientAbLocallyBijective.{t, 0} U
    exact independentKFlatRepresentatives (pbcAdicCompletion U d) K
  exact derivedExchange_isIso (completedModulePullback gU d)
    (completedModulePullback g d) (cbcOpenShriek d j sq.isOpenImmersion)
    (cbcOpenShriek d j' sq.isOpenImmersion') (completedOrdinaryPullback gU d)
    (completedOrdinaryPullback g d) (completedOrdinaryPullbackComplexCounit gU d)
    (completedOrdinaryPullbackComplexCounit g d) (cbcUnderivedInverseExchange d sq)
    (CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d))
    (ordinaryComplexCounit_isIso d gU) (ordinaryComplexCounit_isIso d g) hrep
    (cbcDerivedInverseExchange d sq) (cbcDerivedInverseExchange_exists d sq).exists.choose_spec

end AlgebraicGeometry.Scheme
