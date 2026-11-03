/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Admissible.AdmissibleDivisorClass
public import WeilConjectures.AlgebraicGeometry.PurityVectorBundle.LineZeroGeometry
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionFullyFaithful
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerStarFullyFaithful
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExchangeMono

/-! # Integral rank-one divisor classes

Source: latest blueprint thm-pur-rank-one-thom, Steps 1 and 3
(blueprint: lem-pur-rank-one-divisor-class-integral).
The class is the all-admissible global divisor class through the specified
supported-Hom map. The proper-section comparison and all exchange maps below
are constructions from the published adjunctions, not fields of the conclusion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Admissible

/-- The zero ideal is Cartier, including over nonreduced and empty bases.
Source: lem-pur-line-zero-geometry (blueprint: lem-pur-rank-one-divisor-class-integral).
Proof: in a frame it is (t) in C[t]; coefficient comparison makes multiplication
by t injective for every C. This persists after arbitrary base change. -/
theorem rankOne_zero_ideal (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1) : V.zeroSection.ker.IsInvertible := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hI, _⟩ :=
    PurityVectorBundle.lineZeroGeometry P B b V
  exact isEffectiveCartierCenter_iff_isInvertible_ker.mp hI

/-- Compactifiability supplied by the projective completion of the line bundle.
Source: lem-pur-line-zero-geometry (blueprint: lem-pur-rank-one-divisor-class-integral).
Proof: the standard open chart of Proj Sym(O_B ⊕ E) is V, and its projection
is proper. This is the compactification recorded by lineZeroGeometry. -/
theorem rankOne_compactifiable (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1) : HasCompactification V.p := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hcomp, _⟩ :=
    PurityVectorBundle.lineZeroGeometry P B b V
  obtain ⟨_, _, _, _, _, c, _⟩ := hcomp
  exact c.hasCompactification

attribute [instance] rankOne_compactifiable

/-- The line zero divisor satisfies the actual smooth-pair hypotheses of frame gluing.
Source: lem-pur-line-zero-geometry, smooth projection and Cartier stalk dimension
(blueprint: lem-pur-rank-one-divisor-class-integral).
Proof: the bundle projection is smooth of relative dimension one and finite type,
and its section composite is identity. The base is separated finite type and
therefore Noetherian of finite dimension; the polynomial t equation gives the
stalk dimension difference one, including over a nonreduced base. -/
theorem rankOne_smoothPair (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1) :
    SmoothDivisorPair P (V.p ≫ b) V.zeroSection := by
  obtain ⟨_, _, hsep, hlft, hqc, _, _, _, hsmooth, _, _, _, _, hz, hdim, _⟩ :=
    PurityVectorBundle.lineZeroGeometry P B b V
  have : Smooth (V.zeroSection ≫ V.p) := hz.smooth
  exact ⟨B, b, V.p, 1, rfl, inferInstance, inferInstance, inferInstance,
    hsep, hlft, hqc, hsmooth, inferInstance, hdim⟩

/-- The open-extension unit is invertible; its inverse is uniquely determined.
Source: det-sf-open-closed-sequence-ring-sheaf(1)
(blueprint: lem-pur-rank-one-divisor-class-integral).
Proof: open extension is fully faithful and its restriction is the identity;
the exact derived comparison carries its unit to the derived adjunction unit. -/
theorem openUnit_isIso (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (K : DerivedCategory (Modules Λ X)) :
    IsIso ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).unit.app K) := by
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).unit :=
    refinementOpenUnit_isIso Λ.X j
  infer_instance

/-- The displayed proper-section map is invertible, with its scalar fixed by one.
Source: proper coincidence and unital composition
(blueprint: lem-pur-rank-one-divisor-class-integral).
Proof: z is proper and its closed direct image is exact. The supported object
has proper support over B, so forgetting compact support is an isomorphism.
The remaining factors identify R(πz)_! with R(id_B)_! and then with the unit,
using the canonical section identity and identity comparison. -/
theorem properSectionMap_isIso (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (c : Compactification V.p) :
    IsIso (properSectionMap P b V Λ c) := by
  have : IsNoetherian B := isNoetherian_of_locallyOfFiniteType b
  have : IsNoetherian c.Z := isNoetherian_of_locallyOfFiniteType c.g
  have : TopologicalSpace.NoetherianSpace V.E :=
    c.i.isOpenEmbedding.isInducing.noetherianSpace
  have : IsNoetherian V.E := isNoetherian_of_locallyOfFiniteType c.i
  have hzi : (V.zeroSection ≫ c.i) ≫ c.g = 𝟙 B := by
    rw [Category.assoc, ← c.comm, V.zeroSection_spec.1]
  have : IsProper ((V.zeroSection ≫ c.i) ≫ c.g) := hzi.symm ▸ inferInstance
  have : IsClosedImmersion (V.zeroSection ≫ c.i) := by
    have : IsImmersion (V.zeroSection ≫ c.i) := inferInstance
    exact IsClosedImmersion.of_comp_of_isSeparated (V.zeroSection ≫ c.i) c.g
  have := rankOne_supportedOpenComparison_isIso Λ V.zeroSection c.i (unit Λ B)
  have := rankOne_closedSingleMap_isIso Λ V.zeroSection
  unfold properSectionMap supportToOrdinary
  infer_instance

/-- The inverse open mate is invertible for a Cartesian square.
Source: det-prop-sf-cbc, normalized open comparison
(blueprint: lem-pur-rank-one-divisor-class-integral).
Proof: arbitrary-base open extension commutes with exact inverse image. Its
canonical comparison has inverse the open adjunction mate, so that mate is invertible. -/
theorem openExchange_isIso (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {h : X' ⟶ X} {g : Y' ⟶ Y} (sq : IsPullback h f' f g)
    (c : Compactification f) : IsIso (CompactSupportComposition.openExchange Λ.X sq c) := by
  let a := (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X c.i).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory Λ.X c.i).symm
  let a' :=
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X (c.ofIsPullback sq).i
      ).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory Λ.X (c.ofIsPullback sq).i).symm
  have : IsIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X c.i).unit :=
    refinementOpenUnit_isIso Λ.X c.i
  have hu : IsIso a.unit := by
    dsimp only [a]
    simp only [Adjunction.ofNatIsoRight_unit]
    infer_instance
  have hc (K : DerivedCategory (Modules Λ X)) :
      IsIso (a'.counit.app
        ((moduleObjectDerivedPullback Λ.X (pullback.fst c.g g)).obj
          ((openImmersionLowerShriek Λ.X c.i).mapDerivedCategory.obj K))) := by
    let e := (leftDerivedUpperStarIsoMapDerivedCategory Λ.X (pullback.fst c.g g)).app
        ((openImmersionLowerShriek Λ.X c.i).mapDerivedCategory.obj K) ≪≫
      (Functor.mapDerivedCategoryCompIso
        (openImmersionLowerShriek Λ.X c.i)
        (upperStar Λ.X (pullback.fst c.g g))).symm.app K
    have h := cartesianDerivedCounit Λ.X (c.isPullback_i_ofIsPullback sq) K
    have ht : IsIso
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X
          (c.ofIsPullback sq).i).counit.app
          ((moduleObjectDerivedPullback Λ.X (pullback.fst c.g g)).obj
            ((openImmersionLowerShriek Λ.X c.i).mapDerivedCategory.obj K))) :=
      (NatTrans.isIso_app_iff_of_iso _ e).mpr h
    dsimp only [a']
    simp only [Adjunction.ofNatIsoRight_counit, NatTrans.comp_app,
      Functor.whiskerRight_app]
    infer_instance
  unfold CompactSupportComposition.openExchange
  change IsIso (Adjunction.exchangeLeft a a' _)
  rw [Adjunction.exchangeLeft]
  have : IsIso (Functor.whiskerLeft
      ((openImmersionLowerShriek Λ.X c.i).mapDerivedCategory ⋙
        moduleObjectDerivedPullback Λ.X (pullback.fst c.g g)) a'.counit) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact hc
  infer_instance

/-- The proper/open exchange as a natural transformation, before evaluating on an object.
Source: det-prop-sf-cbc, proper mate followed by inverse open mate
(blueprint: lem-pur-rank-one-divisor-class-integral). -/
def compactExchangeTransformation (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {h : X' ⟶ X} {g : Y' ⟶ Y} (sq : IsPullback h f' f g)
    (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification Λ.X c ⋙ moduleObjectDerivedPullback Λ.X g ⟶
      moduleObjectDerivedPullback Λ.X h ⋙
        rightDerivedLowerShriekOfCompactification Λ.X (c.ofIsPullback sq) :=
  letI := openExchange_isIso Λ sq c
  Functor.whiskerLeft (openImmersionLowerShriek Λ.X c.i).mapDerivedCategory
      (condensedAmbientExchange Λ.X
        (CompactSupportComposition.square (c.isPullback_g_ofIsPullback sq).flip)) ≫
    Functor.whiskerRight (asIso (CompactSupportComposition.openExchange Λ.X sq c)).inv
      (moduleObjectDerivedPushforward Λ.X (c.ofIsPullback sq).g)

/-- Evaluation of the exchange transformation is the specified compact-support map.
Source: the definitions of the two exchange maps
(blueprint: lem-pur-rank-one-divisor-class-maps). -/
theorem compactExchangeTransformation_app (Λ : Profinite.CondensedRing.{u})
    [IsCommMonObj Λ.X]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {h : X' ⟶ X} {g : Y' ⟶ Y} (sq : IsPullback h f' f g)
    (c : Compactification f) (K : DerivedCategory (Modules Λ X)) :
    (compactExchangeTransformation Λ sq c).app K = compactExchange Λ sq c K := rfl

/-- Naturality of the specified compact-support exchange, on arbitrary derived arrows.
Source: naturality of the proper and open exchange mates
(blueprint: lem-pur-rank-one-divisor-class-integral). -/
theorem compactExchange_naturality (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {h : X' ⟶ X} {g : Y' ⟶ Y} (sq : IsPullback h f' f g)
    (c : Compactification f) {K L : DerivedCategory (Modules Λ X)} (φ : K ⟶ L) :
    (moduleObjectDerivedPullback Λ.X g).map
        ((rightDerivedLowerShriekOfCompactification Λ.X c).map φ) ≫
      compactExchange Λ sq c L =
    compactExchange Λ sq c K ≫
      (rightDerivedLowerShriekOfCompactification Λ.X (c.ofIsPullback sq)).map
        ((moduleObjectDerivedPullback Λ.X h).map φ) :=
  (compactExchangeTransformation Λ sq c).naturality φ

end AlgebraicGeometry.ProEtale.CondensedRing
