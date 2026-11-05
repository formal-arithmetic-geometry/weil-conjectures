/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.CompletedStrictOpenExchange
public import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenScalars.FiniteOpenExchangeScalars
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDirectImageSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenStrictReduction
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
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import all WeilConjectures.AlgebraicGeometry.Open.OpenClosedAdjunctionTransport

/-!
# Fixed finite coordinates for completed-ring open exchange

Source: Stacks 03DI, 03D7, 04J0 and 099N; blueprint finite exchange before Rlim
(blueprint: def-cbc-completed-finite-exchange-coordinates).

The scalar comparisons are mates of the sectionwise specified right comparisons.
The level coordinate change is identity on sections. Thus no unrelated finite
coordinate isomorphism is selected.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)

open AlgebraicGeometry.ProEtale.StrictTower

/-- The bundled finite ring is finite by the coefficient datum.
Source: the coefficient datum (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: this is exactly d.quotientFinite at the positive exponent n+1. -/
@[instance] theorem cbcFiniteRing_finite (n : ℕ) : Finite (cbcFiniteRing d n) := by
  exact d.quotientFinite n

/-- The sectionwise direct-image comparison, with its fixed identity normalization.
Source: Stacks 03D7 (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
@[irreducible] def cbcFiniteDirectRes {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :=
  (cbcFiniteDirectRes_existsUnique d f n).exists.choose

/-- The ordinary pullback mate is invertible at finite coefficients.
Source: Stacks 03EK, 099N (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: on inverse-image tensor generators the mate sends b tensor m to pi_n(b)
tensor m. The inverse inserts 1 in the completed tensor factor. The finite
constant-ring comparison and balancing make these maps mutually inverse. -/
@[instance] theorem cbcFinitePullRes_isIso {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :
    IsIso (cbcFinitePullRes d f n) := by
  have hc : IsIso (completedCoefficientMap f d) := completedCoefficient_isIso f d
  let c := asIso (completedCoefficientMap f d)
  let R := pbcAdicCompletion T d
  let RS := pbcAdicCompletion S d
  let B := coefficients (cbcFiniteRing d n) T
  let B' := coefficients (cbcFiniteRing d n) S
  let cB := constantRingIso (cbcFiniteRing d n) f
  have h : c.hom ≫ cbcFiniteProjection d S n =
      (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (cbcFiniteProjection d T n) ≫ cB.hom := finiteProjection_pullback d f n
  let z := proEtaleRingRestrictionDirectImage f R B RS B'
    (cbcFiniteProjection d T n) (cbcFiniteProjection d S n) c cB h
  have hz : z = cbcFiniteDirectRes d f n := by
    apply (cbcFiniteDirectRes_existsUnique d f n).unique
    · exact (proEtaleRingRestrictionDirectImage_existsUnique
        f R B RS B' (cbcFiniteProjection d T n) (cbcFiniteProjection d S n) c cB h)
          |>.choose_spec.1
    · simpa only [cbcFiniteDirectRes] using
        (cbcFiniteDirectRes_existsUnique d f n).exists.choose_spec
  let a := proEtaleRingModuleAdjunction f B B' cB
  let b := proEtaleRingModuleAdjunction f R RS c
  let β := proEtaleRingRestrictionPullbackInv f R B RS B'
    (cbcFiniteProjection d T n) (cbcFiniteProjection d S n) c cB h
  have hβ : IsIso β := proEtaleRingRestrictionPullbackInv_isIso
    f R B RS B' (cbcFiniteProjection d T n) (cbcFiniteProjection d S n) c cB h
  have hm : (mateEquiv a b (TwoSquare.mk _ _ _ _ β)).natTrans = z.hom :=
    restrictionPullback_mate f R B RS B'
      (cbcFiniteProjection d T n) (cbcFiniteProjection d S n) c cB h
  have hm' : mateEquiv a b (TwoSquare.mk _ _ _ _ β) =
      TwoSquare.mk _ _ _ _ z.hom := (TwoSquare.equivNatTrans _ _ _ _).injective hm
  have hi : IsIso ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ z.hom)).natTrans := by
    rw [← hm', Equiv.symm_apply_apply]
    exact hβ
  have hi' := inverseMate_isIso_change_left a b (cbcModulePullbackAdjunction d f)
    (TwoSquare.mk _ _ _ _ z.hom) hi
  rw [hz] at hi'
  exact hi'

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction

attribute [local irreducible] finiteOpenRing

attribute [local irreducible] finiteOpenAdjunction

/-- The uniquely normalized finite open-restriction comparison.
Source: Stacks 03DI (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
@[irreducible] def cbcFiniteOpenRestriction {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :=
  (cbcFiniteOpenRestriction_existsUnique d e he n).exists.choose

attribute [local instance] openSliceContinuous openSliceCompContinuous

attribute [local irreducible] finiteSliceRing

/-- The normalized open-extension comparison is invertible.
Source: Stacks 03DI (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: the finite extension unit is invertible, and the adjunct of the specified
mate is this unit followed by the fixed open-restriction isomorphism. The existing
ringed-slice scalar comparison places its target in the essential image of the
fully faithful completed extension. Its counit is therefore invertible, and the
adjunction formula expresses the mate as a composite of two isomorphisms. -/
@[instance] theorem cbcFiniteOpenRes_isIso {W T : Scheme.{u}}
    (e : W ⟶ T) (he : IsOpenImmersion e) (n : ℕ) :
    IsIso (cbcFiniteOpenRes d e he n) := by
  let := he
  let a := @moduleJAdj.{u} (cbcFiniteRing d n) _ W T e he
  let b := cbcOpenAdjunction d e he
  have := finiteExtension_unit_isIso d e he n
  let hb := completedExtension_fullyFaithful d e he
  let := hb.full
  let := hb.faithful
  let θ := cbcOpenRestrictIso (cbcOpenObject e he)
    (cbcCompletedRestriction (cbcOpenObject e he) d)
    (finiteSliceRing d T (cbcOpenObject e he) n)
    (cbcFiniteProjection d T n) (cbcFiniteProjection d W n)
    (finiteSliceRing_projection d T (cbcOpenObject e he) n)
  let χ := θ ≪≫ Functor.isoWhiskerRight (finiteExtensionComparison d e he n)
    (cbcFiniteRes d T n)
  have h (M : ProEtale.StrictTower.Modules (cbcFiniteRing d n) W) :
      IsIso ((cbcFiniteOpenRes d e he n).app M) := by
    let f := (cbcFiniteOpenRes d e he n).app M
    have hf : b.homEquiv _ _ f =
        (cbcFiniteRes d W n).map (a.unit.app M) ≫
          (cbcFiniteOpenRestriction d e he n).hom.app ((moduleJ (cbcFiniteRing d n) e).obj M) := by
      rw [Adjunction.homEquiv_unit]
      exact (unit_mateEquiv_symm a b
        (TwoSquare.mk _ _ _ _ (cbcFiniteOpenRestriction d e he n).hom) M).symm
    have hi : IsIso (b.homEquiv _ _ f) := by
      rw [hf]
      infer_instance
    have hs : (cbcOpenShriek d e he).essImage
        (((moduleJ (cbcFiniteRing d n) e) ⋙ cbcFiniteRes d T n).obj M) :=
      ⟨(cbcFiniteRes d W n).obj M, ⟨χ.app M⟩⟩
    have : IsIso (b.counit.app _) := b.isIso_counit_app_iff_mem_essImage.mpr hs
    have heq : f = (cbcOpenShriek d e he).map (b.homEquiv _ _ f) ≫ b.counit.app _ :=
      ((b.homEquiv _ _).symm_apply_apply f).symm
    change IsIso f
    rw [heq]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- Finite reduction followed by coefficient restriction is additive.
Source: Stacks 03EK, 099N
(blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: sheafified scalar extension and scalar restriction both preserve sums of
morphisms. Composing their sum equations proves additivity. -/
@[instance] theorem cbcFiniteReductionModule_additive (T : Scheme.{u}) (n : ℕ) :
    (cbcFiniteReductionModule d T n).Additive := by
  unfold cbcFiniteReductionModule
  infer_instance

/-- The finite coordinate change fixed by identity on sections.
Source: Stacks 099N (blueprint: def-cbc-completed-finite-exchange-coordinates). -/
@[irreducible] def cbcFiniteLevel (T : Scheme.{u}) (n : ℕ) :=
  (cbcFiniteLevel_existsUnique d T n).exists.choose

/-- Both finite source and target are exact and additive.
Source: Stacks 03DI, 03DJ, 03EK
(blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: open extension and finite constant pullback are exact and additive, as
is scalar restriction. Compose these properties in the indicated order. -/
@[instance] theorem cbcFiniteSource_additive (n : ℕ) :
    (cbcFiniteSource d sq n).Additive := by
  unfold cbcFiniteSource cbcFiniteRes
  infer_instance

/-- Exactness of the finite source, checked before derived localization.
Source: Stacks 03DJ, 03EK (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: compose exact open extension, finite pullback and scalar restriction. -/
@[instance] theorem cbcFiniteSource_limits (n : ℕ) :
    PreservesFiniteLimits (cbcFiniteSource d sq n) := by
  unfold cbcFiniteSource cbcFiniteRes
  infer_instance

/-- The finite source preserves cokernels and finite sums.
Source: Stacks 03DI, 03EK (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: all three functors preserve finite colimits, hence so does their composite. -/
@[instance] theorem cbcFiniteSource_colimits (n : ℕ) :
    PreservesFiniteColimits (cbcFiniteSource d sq n) := by
  unfold cbcFiniteSource cbcFiniteRes
  infer_instance

/-- Additivity of the finite target.
Source: Stacks 03DI, 03EK (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: finite pullback, open extension and scalar restriction are additive. -/
@[instance] theorem cbcFiniteTarget_additive (n : ℕ) :
    (cbcFiniteTarget d sq n).Additive := by
  unfold cbcFiniteTarget cbcFiniteRes
  infer_instance

/-- Exactness of the finite target on kernels.
Source: Stacks 03DJ, 03EK (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: each of the three factors preserves finite limits. -/
@[instance] theorem cbcFiniteTarget_limits (n : ℕ) :
    PreservesFiniteLimits (cbcFiniteTarget d sq n) := by
  unfold cbcFiniteTarget cbcFiniteRes
  infer_instance

/-- Exactness of the finite target on cokernels.
Source: Stacks 03DI, 03EK (blueprint: def-cbc-completed-finite-exchange-coordinates).
Proof: each of the three factors preserves finite colimits. -/
@[instance] theorem cbcFiniteTarget_colimits (n : ℕ) :
    PreservesFiniteColimits (cbcFiniteTarget d sq n) := by
  unfold cbcFiniteTarget cbcFiniteRes
  infer_instance

end AlgebraicGeometry.Scheme
