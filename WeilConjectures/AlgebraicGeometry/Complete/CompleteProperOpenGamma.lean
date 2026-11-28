/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionCompactification
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.Ringed.RingedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCompactSupportExchange
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualStrictPullback
public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenRestrictionPullback
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportFiniteTorsion
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
public import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedExchangeCoherence
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Mathlib.CategoryTheory.Adjunction.Mates

import WeilConjectures.Compactification.Cofiltered
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryOpenExchangeIdentity
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullbackReflection

import all WeilConjectures.Algebra.Homology.ProperBaseChange.OpenImmersionTensorPiece
import all WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all Mathlib.CategoryTheory.Sites.Over
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.AlgebraicGeometry.Clopen.ClopenScalarRestrictionReverseAdjunction
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenStrictReduction
import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenFiniteEtaleOrigins
import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulQuotientComparison
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedFiniteExchangeCoordinates

/-!
# Proper/open comparisons for complete pro-etale compact support

The open extension, clopen projection and proper/open gamma on completed-ring modules,
split out of `CompleteCompactSupportProetale`.

## References

* Stacks Project, Tags 01K5, 03DI, 03DJ, 07A6, 07A7, 09AE, 0F7B, 0F7D
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The exact, section-normalized open adjunction on completed coefficients. -/
def cbcDerivedOpenAdjunction {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcDerivedOpenShriek d j inferInstance ⊣ d.pull j :=
  Adjunction.ofNatIsoRight
    ((Adjunction.ofNatIsoRight (cbcOpenAdjunction d j inferInstance)
      (@asIso _ _ _ _ (cbcPullToRestriction d j)
        (cbcPullToRestriction_isIso d j)).symm).mapDerivedCategoryRightDerivedAdjunction)
    (proEtaleRingModulePullback j (d.completedRing T) (d.completedRing U)
      (d.integralRingIso j)).rightDerivedFunctorIsoMapDerivedCategory

/-- Abbreviation for the recorded exact open extension, without a new construction. -/
abbrev cbcJ {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :=
  cbcDerivedOpenShriek d j inferInstance

/-- Open composition is the unique comparison of the composition adjunctions. -/
def cbcJComp {U V T : Scheme.{t}} (j : U ⟶ V) (k : V ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion k] : cbcJ d j ⋙ cbcJ d k ≅ cbcJ d (j ≫ k) :=
  Adjunction.leftAdjointCompIso (cbcDerivedOpenAdjunction d j)
    (cbcDerivedOpenAdjunction d k) (cbcDerivedOpenAdjunction d (j ≫ k))
    (d.pullComp j k).symm

/-- Equality transport for the recorded open extension. -/
def cbcJCongr {U T : Scheme.{t}} {j k : U ⟶ T}
    [IsOpenImmersion j] [IsOpenImmersion k] (h : j = k) : cbcJ d j ≅ cbcJ d k :=
  by
    subst k
    exact Iso.refl _

/-- Proper inverse image/direct image with their published tensor-normalized adjunction. -/
abbrev cbcPullPushAdjunction {U T : Scheme.{t}} (f : U ⟶ T) : d.pull f ⊣ d.push f :=
  proEtaleRingDerivedAdjunction f (d.completedRing T) (d.completedRing U)
    (d.integralRingIso f)

/-- Pullback composition around a commutative square, with its canonical compositors. -/
def cbcSquarePull {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    d.pull i ⋙ d.pull r ≅ d.pull p ⋙ d.pull k :=
  (d.pullComp r i).symm ≪≫ eqToIso (congrArg (fun f ↦ d.pull f) h.symm) ≪≫
    d.pullComp k p

/-- The open unit is invertible, including on the empty open subscheme. -/
theorem cbcOpenUnit_isIso {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    IsIso (cbcDerivedOpenAdjunction d j).unit := by
  let W := cbcOpenObject j inferInstance
  let e := ProEt.sliceEquiv T W
  let : e.inverse.IsDenseSubsite (ProEt.topology U) ((ProEt.topology T).over W) :=
    ProEt.sliceDense T W
  let : e.inverse.IsContinuous (ProEt.topology U) ((ProEt.topology T).over W) :=
    inferInstance
  let : e.functor.IsContinuous ((ProEt.topology T).over W) (ProEt.topology U) :=
    cbcSliceFunctor_continuous T W
  let : e.symm.functor.IsContinuous (ProEt.topology U) ((ProEt.topology T).over W) :=
    inferInstanceAs (e.inverse.IsContinuous _ _)
  let : e.symm.inverse.IsContinuous ((ProEt.topology T).over W) (ProEt.topology U) :=
    inferInstanceAs (e.functor.IsContinuous _ _)
  let : e.functor.IsDenseSubsite ((ProEt.topology T).over W) (ProEt.topology U) := by
    have h := e.eq_inducedTopology_of_isDenseSubsite
      ((ProEt.topology T).over W) (ProEt.topology U)
    rw [h]
    infer_instance
  let : e.symm.inverse.IsDenseSubsite ((ProEt.topology T).over W)
      (ProEt.topology U) := inferInstanceAs (e.functor.IsDenseSubsite _ _)
  let c := (sheafCompose ((ProEt.topology T).over W)
    (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).mapIso
      (cbcCompletedRestriction W d)
  obtain ⟨q, hq⟩ := ProEt.module_transport (ProEt.topology U) ((ProEt.topology T).over W)
    e.symm (reductionModuleRing U (d.completedRing U))
    ((reductionModuleRing T (d.completedRing T)).over W) c
  let hq' : q.functor ≅ cbcModuleToSlice d T W :=
    Functor.fullyFaithfulCancelRight (SheafOfModules.forget _)
      (eqToIso (by rw [hq]; rfl))
  have : (cbcModuleToSlice d T W).IsEquivalence :=
    Functor.isEquivalence_of_iso hq'
  have : (cbcModuleToSlice d T W).Additive := by
    constructor
    intro M N f g
    ext V x
    rfl
  have : (SheafOfModules.localizedModuleExtension.{t} (d.completedRing T) W).Additive :=
    SheafOfModules.localizedModuleExtension_additive (d.completedRing T) W
  have : PreservesFiniteLimits
      (SheafOfModules.localizedModuleExtension.{t} (d.completedRing T) W) :=
    SheafOfModules.localizedModuleExtension_limits (d.completedRing T) W
  have : PreservesFiniteColimits
      (SheafOfModules.localizedModuleExtension.{t} (d.completedRing T) W) :=
    SheafOfModules.localizedModuleExtension_colimits (d.completedRing T) W
  let b := SheafOfModules.localizedModuleDerivedAdjunction.{t}
    (d.completedRing T) W
  have : IsIso b.unit :=
    SheafOfModules.localizedDerivedUnit_isIso j (d.completedRing T)
  have := b.fullyFaithfulLOfIsIsoUnit.full
  have := b.fullyFaithfulLOfIsIsoUnit.faithful
  let eD := Functor.mapDerivedCategoryCompIso (cbcModuleToSlice d T W)
    (SheafOfModules.localizedModuleExtension (d.completedRing T) W)
  have : (cbcJ d j).Full := Functor.Full.of_iso eD
  have : (cbcJ d j).Faithful := Functor.Faithful.of_iso eD
  infer_instance

/-- The inverse open comparison is the transpose of the open-extension unit. -/
def cbcBetaInv {U' U T' T : Scheme.{t}}
    (a : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (g : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g) :
    d.pull a ⋙ cbcJ d j' ⟶ cbcJ d j ⋙ d.pull g :=
  (((cbcDerivedOpenAdjunction d j').whiskerRight _).homEquiv _ _).symm
    ((Functor.leftUnitor (d.pull a)).inv ≫
      Functor.whiskerRight (cbcDerivedOpenAdjunction d j).unit (d.pull a) ≫
      (Functor.associator (cbcJ d j) (d.pull j) (d.pull a)).hom ≫
      Functor.whiskerLeft (cbcJ d j) (cbcSquarePull d a j' j g h).inv ≫
      (Functor.associator (cbcJ d j) (d.pull g) (d.pull j')).inv)

/-- The unit-normalized open comparison is invertible for a Cartesian open square. -/
theorem cbcBetaInv_isIso {U' U T' T : Scheme.{t}}
    (a : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (g : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (_sq : IsPullback a j' j g) : IsIso (cbcBetaInv d a j' j g h) := by
  let sq : OpenImmersionSquare a j' j g :=
    { w := h
      isoPullback := _sq.isoPullback
      hom_fst := _sq.isoPullback_hom_fst
      hom_snd := _sq.isoPullback_hom_snd
      isOpenImmersion := inferInstance
      isOpenImmersion' := inferInstance }
  have := cbcOpenUnit_isIso d j
  have := cbcOpenUnit_isIso d j'
  let ff := (cbcDerivedOpenAdjunction d j').fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have he : IsIso (cbcDatumOrdinaryExchange d sq) := by
    unfold cbcDatumOrdinaryExchange cbcOrdinaryExchange
    infer_instance
  let adj := (cbcDerivedOpenAdjunction d j').whiskerRight (d.derived U)
  have : IsIso (adj.counit.app (cbcJ d j ⋙ d.pull g)) :=
    adj.isIso_counit_app_of_iso (asIso (cbcDatumOrdinaryExchange d sq))
  unfold cbcBetaInv
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- Cartesian open comparison, in the forward direction fixed by the inverse unit-mate. -/
def cbcBeta {U' U T' T : Scheme.{t}}
    (a : U' ⟶ U) (j' : U' ⟶ T') (j : U ⟶ T) (g : T' ⟶ T)
    [IsOpenImmersion j] [IsOpenImmersion j'] (h : a ≫ j = j' ≫ g)
    (sq : IsPullback a j' j g) : cbcJ d j ⋙ d.pull g ≅ d.pull a ⋙ cbcJ d j' :=
  (@asIso _ _ _ _ (cbcBetaInv d a j' j g h)
    (cbcBetaInv_isIso d a j' j g h sq)).symm

/-- Open extension to direct image, fixed by the ordinary units of both adjunctions. -/
def cbcOpenToPush {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j] :
    cbcJ d j ⟶ d.push j :=
  (Functor.rightUnitor _).inv ≫ Functor.whiskerLeft (cbcJ d j) (cbcPullPushAdjunction d j).unit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (@inv _ _ _ _ (cbcDerivedOpenAdjunction d j).unit
      (cbcOpenUnit_isIso d j)) (d.push j) ≫ (Functor.leftUnitor _).hom

private theorem cbcRestrictionScalar_isIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] : IsIso (cbcCompletedRestrictionMap d j inferInstance) := by
  let G := cbcOpenSiteFunctor j inferInstance
  let R := d.completedRing T
  let c := cbcCompletedRestrictionMap d j inferInstance
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j
    (inferInstance : WeaklyEtale j) trivial
  let b := a.sheafPushforwardContinuous (E := CommRingCat.{t + 1})
    (ProEt.topology U) (ProEt.topology T)
  let e := ((proEtaleSheafAdjunction j CommRingCat.{t + 1}).leftAdjointUniq b).app R
  have hc : (d.integralRingIso j).hom ≫ c = e.hom := by
    apply ((proEtaleSheafAdjunction j CommRingCat.{t + 1}).homEquiv _ _).injective
    change ((proEtaleSheafAdjunction j CommRingCat.{t + 1}).homEquiv R
      ((G.sheafPushforwardContinuous CommRingCat.{t + 1}
        (ProEt.topology U) (ProEt.topology T)).obj R)) ((d.integralRingIso j).hom ≫ c) =
      ((proEtaleSheafAdjunction j CommRingCat.{t + 1}).homEquiv R
        ((G.sheafPushforwardContinuous CommRingCat.{t + 1}
          (ProEt.topology U) (ProEt.topology T)).obj R))
        (((proEtaleSheafAdjunction j CommRingCat.{t + 1}).leftAdjointUniq b).hom.app R)
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    apply Sheaf.hom_ext
    exact (cbcCompletedCoefficientCounit d j).symm
  have heq : c = ((d.integralRingIso j).symm ≪≫ e).hom := by
    apply (cancel_epi (d.integralRingIso j).hom).1
    simpa only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc] using hc
  change IsIso c
  rw [heq]
  infer_instance

private theorem cbcClopenReverseAdjunction {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [IsClosedImmersion j] : Nonempty (d.pull j ⊣ cbcJ d j) := by
  let R := d.completedRing T
  let S := d.completedRing U
  let c := cbcCompletedRestrictionMap d j inferInstance
  have : IsIso c := cbcRestrictionScalar_isIso d j
  let : (proEtaleOpenComposition j).IsContinuous (ProEt.topology U)
      (ProEt.topology T) := cbcOpenSiteFunctor_continuous j inferInstance
  obtain ⟨b⟩ := clopenScalarRestrictionReverseAdjunction j R S (asIso c)
    (cbcOpenShriek d j inferInstance) (cbcOpenAdjunction d j inferInstance)
  let pb := proEtaleRingModulePullback j R S (d.integralRingIso j)
  let r : pb ≅ cbcOpenRestriction d j inferInstance :=
    @asIso _ _ _ _ (cbcPullToRestriction d j) (cbcPullToRestriction_isIso d j)
  let br := b.ofNatIsoLeft r.symm
  let : (cbcOpenShriek d j inferInstance).Additive :=
    cbcOpenShriek_additive d j inferInstance
  let : PreservesFiniteLimits (cbcOpenShriek d j inferInstance) :=
    cbcOpenShriek_finiteLimits d j inferInstance
  let : PreservesFiniteColimits (cbcOpenShriek d j inferInstance) :=
    cbcOpenShriek_finiteColimits d j inferInstance
  exact ⟨br.mapExactDerivedCategory⟩

/-- The specified open-to-direct-image map is invertible on a clopen immersion. -/
theorem cbcOpenToPush_isIso {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [IsClosedImmersion j] : IsIso (cbcOpenToPush d j) := by
  obtain ⟨ar⟩ := cbcClopenReverseAdjunction d j
  let e := ar.rightAdjointUniq (cbcPullPushAdjunction d j)
  have := cbcOpenUnit_isIso d j
  let ff := (cbcDerivedOpenAdjunction d j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  have : (d.push j).Full := Functor.Full.of_iso e
  have : (d.push j).Faithful := Functor.Faithful.of_iso e
  have hi (M : d.derived U) : IsIso ((cbcOpenToPush d j).app M) := by
    have hu : IsIso ((cbcPullPushAdjunction d j).unit.app ((cbcJ d j).obj M)) :=
      (cbcPullPushAdjunction d j).isIso_unit_app_of_iso (e.app M)
    dsimp only [cbcOpenToPush, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.rightUnitor_inv_app, Functor.associator_inv_app,
      Functor.leftUnitor_hom_app]
    simp only [Category.id_comp]
    have hv : IsIso ((inv (cbcDerivedOpenAdjunction d j).unit).app M) := inferInstance
    have hw : IsIso ((d.push j).map ((inv (cbcDerivedOpenAdjunction d j).unit).app M)) :=
      inferInstance
    exact IsIso.comp_isIso' hu (IsIso.comp_isIso' hw (IsIso.id _))
  exact NatIso.isIso_of_isIso_app _

/-- Canonical clopen projection; identity on the image and zero on the complement. -/
def cbcClopenProjection {U T : Scheme.{t}} (j : U ⟶ T)
    [IsOpenImmersion j] [IsClosedImmersion j] : 𝟭 (d.derived T) ⟶ d.pull j ⋙ cbcJ d j :=
  (cbcPullPushAdjunction d j).unit ≫ Functor.whiskerLeft (d.pull j)
    (@inv _ _ _ _ (cbcOpenToPush d j) (cbcOpenToPush_isIso d j))

/-- The non-Cartesian proper/open comparison before taking its proper-adjunction mate.
It projects onto the clopen image of (k,r) in the fibre product, with no extra
Cartesian-square hypothesis on a refinement. -/
def cbcProperOpenAlpha {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : cbcJ d i ⋙ d.pull p ⟶ d.pull r ⋙ cbcJ d k :=
  (cbcBeta d (pullback.snd p i) (pullback.fst p i) i p
    pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom ≫
  Functor.whiskerRight (Functor.whiskerLeft (d.pull (pullback.snd p i))
    (cbcClopenProjection d (ProEtale.StrictTower.squareLift k r p i h)))
      (cbcJ d (pullback.fst p i)) ≫
  Functor.whiskerRight (Functor.associator (d.pull (pullback.snd p i))
    (d.pull (ProEtale.StrictTower.squareLift k r p i h))
      (cbcJ d (ProEtale.StrictTower.squareLift k r p i h))).inv
        (cbcJ d (pullback.fst p i)) ≫
  (Functor.associator (d.pull (pullback.snd p i) ⋙
    d.pull (ProEtale.StrictTower.squareLift k r p i h))
      (cbcJ d (ProEtale.StrictTower.squareLift k r p i h))
        (cbcJ d (pullback.fst p i))).hom ≫
  Functor.whiskerLeft (d.pull (pullback.snd p i) ⋙
    d.pull (ProEtale.StrictTower.squareLift k r p i h))
      ((cbcJComp d (ProEtale.StrictTower.squareLift k r p i h) (pullback.fst p i)).hom ≫
        (cbcJCongr d (pullback.lift_fst k r h)).hom) ≫
  Functor.whiskerRight ((d.pullComp (ProEtale.StrictTower.squareLift k r p i h)
    (pullback.snd p i)).inv ≫
      (eqToIso (congrArg (fun f ↦ d.pull f) (pullback.lift_snd k r h))).hom) (cbcJ d k)

/-- The canonical proper/open map is the proper-adjunction mate of the clopen projection. -/
def cbcProperOpenGamma {V W S T : Scheme.{t}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) [IsOpenImmersion k] [IsOpenImmersion i]
    [QuasiCompact k] [QuasiCompact i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) : d.push r ⋙ cbcJ d i ⟶ cbcJ d k ⋙ d.push p :=
  mateEquiv (cbcPullPushAdjunction d r) (cbcPullPushAdjunction d p)
    (cbcProperOpenAlpha d k r p i h)

/-- The base-changed finite-type morphism is quasi-compact. This is a consequence
of the supplied square, not an additional typeclass hypothesis in the coherence laws. -/
abbrev cbcBaseChangeQuasiCompact {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g' : X' ⟶ X} [QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sq : OpenImmersionSquare g' c'.i c.i gbar) : QuasiCompact f' :=
  c'.quasiCompact (MorphismProperty.of_isPullback
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)
      (c.quasiCompact_openImmersion inferInstance))

/-- The recorded exchange, with its quasi-compactness instance named for explicit
transport to a base-changed compactification. Its map is definitionally unchanged. -/
abbrev cbcExchange {X' X Y' Y : Scheme.{t}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [qf : QuasiCompact f]
    (c : Compactification f) (c' : Compactification f') (gbar : c'.Z ⟶ c.Z)
    (sp : ChosenCartesianSquare gbar c'.g c.g g)
    (sj : OpenImmersionSquare g' c'.i c.i gbar)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : (cbcCompleteProperty d X r a ha).FullSubcategory) :=
  completedCompactSupportExchange d c c' gbar sp sj r a ha K

/-- The exact chosen-compactification functor Rp_* j_! on completed-ring modules. -/
abbrev cbcSupport {X Y : Scheme.{t}} {f : X ⟶ Y} (c : Compactification f) :=
  cbcJ d c.i ⋙ d.push c.g

end AlgebraicGeometry.Scheme
