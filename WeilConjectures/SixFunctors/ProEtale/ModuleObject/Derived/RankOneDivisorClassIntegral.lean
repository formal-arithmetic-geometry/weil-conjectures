/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Admissible.AdmissibleDivisorClass
public import WeilConjectures.AlgebraicGeometry.PurityVectorBundle.PurityVectorBundleZeroSection
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.VectorProjectiveCompletion.VectorProjectiveCompletionData
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import WeilConjectures.AlgebraicGeometry.VectorProjectiveCompletion.VectorProjectivePresentation
public import WeilConjectures.RingTheory.SmoothPurity.SymmetricAlgebraDehomogenization
public import WeilConjectures.AlgebraicGeometry.VectorProjectiveCompletion.VectorProjectiveFrameModel
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Universal
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.Algebra.MvPolynomial.Equiv
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.DetPropSfCbc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.AlgebraicGeometry.PurityVectorBundle.LineZeroGeometry
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Mono
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionFullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionEssImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerStarFullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RankOneDivisorClassMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.RankOneProperSectionPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExchangeMono

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

/-- Closedness of the actual augmentation zero section, from the recorded bundle.
Source: zero-section specification (blueprint: lem-pur-rank-one-divisor-class-integral). -/
instance rankOne_zero_closed (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1) : IsClosedImmersion V.zeroSection :=
  V.zeroSection_spec.2.1

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

/-- The actual arrow attached to cl(z(B)) by the all-admissible supported-Hom map.
Source: thm-pur-rank-one-thom, Step 1
(blueprint: lem-pur-rank-one-divisor-class-integral). -/
def canonicalThom (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ) :=
  divisorArrow P Λ hΛ (V.p ≫ b) V.zeroSection (rankOne_zero_ideal P b V)
    (rankOne_smoothPair P b V)

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

/-- Forget support by the open adjunction, using the inverse of its specific unit,
then the canonical direct-image compositor. Source: proper-section composition
(blueprint: lem-pur-rank-one-divisor-class-integral). -/
def supportToOrdinary (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (Modules Λ X)) :=
  letI := openUnit_isIso Λ c.i K
  (moduleObjectDerivedPushforward Λ.X c.g).map
      (((upperStarLowerStarAdjunction Λ.X c.i).mapDerivedCategoryRightDerivedAdjunction
        ).homEquiv _ _
          (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X c.i).unit.app K))) ≫
    (rightDerivedLowerStarComp Λ.X c.i c.g).hom.app K ≫
    (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ.X c.comm.symm)).hom.app K

/-- The map from underived closed pushforward in degree zero to total pushforward,
fixed as the adjunct of the ordinary closed counit. Source: proper coincidence
(blueprint: lem-pur-rank-one-divisor-class-integral). -/
def closedSingleMap (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {D X : Scheme.{u}} (i : D ⟶ X) :=
  (derivedUpperStarLowerStarAdjunction Λ.X i).homEquiv
    ((DerivedCategory.singleFunctor _ 0).obj (source Λ i))
    ((DerivedCategory.singleFunctor _ 0).obj (unit Λ D)) <|
      (leftDerivedUpperStarIsoMapDerivedCategory Λ.X i).hom.app _ ≫
        ((upperStar Λ.X i).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((upperStarLowerStarAdjunction Λ.X i).counit.app (unit Λ D))

/-- The canonical proper-section/composition map Rπ_!z_*Λ → Λ. All its factors
are the ordinary proper comparison, the direct-image compositor, the section
identity and the identity-functor comparison. Source: thm-pur-rank-one-thom, Step 1
(blueprint: lem-pur-rank-one-divisor-class-integral). -/
def properSectionMap (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (c : Compactification V.p) :=
  supportToOrdinary Λ c ((DerivedCategory.singleFunctor _ 0).obj (source Λ V.zeroSection)) ≫
    (moduleObjectDerivedPushforward Λ.X V.p).map (closedSingleMap Λ V.zeroSection) ≫
    (rightDerivedLowerStarComp Λ.X V.zeroSection V.p).hom.app
      ((DerivedCategory.singleFunctor _ 0).obj (unit Λ B)) ≫
    (Functor.rightDerivedFunctorNatIso
      (lowerStarCongr Λ.X V.zeroSection_spec.1)).hom.app _ ≫
    (CondensedOpenProper.rId Λ.X B).hom.app _

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

/-- σ is the isomorphism of the explicitly constructed proper-section map.
Source: thm-pur-rank-one-thom, Step 1
(blueprint: lem-pur-rank-one-divisor-class-integral). -/
def canonicalSigma (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (c : Compactification V.p) :=
  letI := properSectionMap_isIso P b V Λ c
  asIso (properSectionMap P b V Λ c)

/-- τ = Rπ_!(thom) ∘ σ⁻¹ on the actual proper/open compactification model.
Source: thm-pur-rank-one-thom, Step 1
(blueprint: lem-pur-rank-one-divisor-class-integral). -/
def canonicalTau (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ) (c : Compactification V.p) :=
  (canonicalSigma P b V Λ c).inv ≫
    (rightDerivedLowerShriekOfCompactification Λ.X c).map (canonicalThom P b V Λ hΛ)

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

/-- Ex_! is the published proper mate followed by the inverse open mate. The target
uses the pulled-back compactification itself. Source: det-prop-sf-cbc
(blueprint: lem-pur-rank-one-divisor-class-integral). -/
def compactExchange (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {h : X' ⟶ X} {g : Y' ⟶ Y} (sq : IsPullback h f' f g)
    (c : Compactification f) (K : DerivedCategory (Modules Λ X)) :=
  letI := openExchange_isIso Λ sq c
  (condensedAmbientExchange Λ.X
      (CompactSupportComposition.square (c.isPullback_g_ofIsPullback sq).flip)).app
        ((openImmersionLowerShriek Λ.X c.i).mapDerivedCategory.obj K) ≫
    (moduleObjectDerivedPushforward Λ.X (c.ofIsPullback sq).g).map
      ((asIso (CompactSupportComposition.openExchange Λ.X sq c)).inv.app K)

/-- The two actual base-change equations. The square is Cartesian, and hz says
that the pulled-back section is the zero section of V'. No comparison map is a field.
Source: thm-pur-rank-one-thom, Step 3
(blueprint: lem-pur-rank-one-divisor-class-integral). -/
def RankOneBaseChangeLaw (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ) (c : Compactification V.p)
    {B' : Scheme.{u}} (b' : B' ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b'] [LocallyOfFiniteType b'] [QuasiCompact b']
    (V' : PurityVectorBundle P B' b' 1) (g : B' ⟶ B) (gV : V'.E ⟶ V.E)
    (sq : IsPullback gV V'.p V.p g)
    (hz : V'.zeroSection ≫ gV = g ≫ V.zeroSection) : Prop :=
  (closedSourcePull Λ (CommSq.mk hz.symm) ≫ canonicalThom P b' V' Λ hΛ =
    (moduleObjectDerivedPullback Λ.X gV).map (canonicalThom P b V Λ hΛ) ≫
      (twistPull P Λ hΛ (V'.p ≫ b') (V.p ≫ b) gV).hom) ∧
  ((unitPull Λ g).hom ≫ canonicalTau P b' V' Λ hΛ (c.ofIsPullback sq) =
    (moduleObjectDerivedPullback Λ.X g).map (canonicalTau P b V Λ hΛ c) ≫
      compactExchange Λ sq c
        (((DerivedCategory.singleFunctor _ 0).obj (line P Λ hΛ V.E)) ⟦(2 : ℤ)⟧) ≫
      (rightDerivedLowerShriekOfCompactification Λ.X (c.ofIsPullback sq)).map
        (twistPull P Λ hΛ (V'.p ≫ b') (V.p ≫ b) gV).hom)

/-- Every local equation gives +∂κ(f), and any two frame presentations yield
identical arrows after their canonical closed-source comparisons.
Source: thm-pur-rank-one-thom, Step 1
(blueprint: lem-pur-rank-one-divisor-class-integral). -/
structure RankOneDivisorClassData (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ) : Prop where
  smooth_zero_family : Smooth (V.zeroSection ≫ V.p)
  codimension_one : ∀ x : B,
    ringKrullDim (V.E.presheaf.stalk (V.zeroSection x)) =
      ringKrullDim (B.presheaf.stalk x) + (1 : WithBot ℕ∞)
  local_equation : LocalEquationLaw P Λ hΛ (V.p ≫ b) V.zeroSection
    (rankOne_zero_ideal P b V) (rankOne_smoothPair P b V)
  frame_independent :
    ∀ (U : Scheme.{u}) (e : U ⟶ V.E) [IsOpenImmersion e]
      (f₁ f₂ : Γ(U, ⊤))
      (h₁ : (U.zeroLocusSubschemeι {f₁}).ker.IsInvertible)
      (h₂ : (U.zeroLocusSubschemeι {f₂}).ker.IsInvertible)
      (d₁ : U.zeroLocusSubscheme {f₁} ⟶ B) (d₂ : U.zeroLocusSubscheme {f₂} ⟶ B)
      (s₁ : IsPullback d₁ (U.zeroLocusSubschemeι {f₁}) V.zeroSection e)
      (s₂ : IsPullback d₂ (U.zeroLocusSubschemeι {f₂}) V.zeroSection e),
      closedSourcePull Λ s₁.toCommSq ≫ equationBoundary P Λ hΛ U (e ≫ V.p ≫ b) f₁ h₁ =
        closedSourcePull Λ s₂.toCommSq ≫ equationBoundary P Λ hΛ U (e ≫ V.p ≫ b) f₂ h₂
  base_change : ∀ (c : Compactification V.p)
    {B' : Scheme.{u}} (b' : B' ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b'] [LocallyOfFiniteType b'] [QuasiCompact b']
    (V' : PurityVectorBundle P B' b' 1) (g : B' ⟶ B) (gV : V'.E ⟶ V.E),
    g ≫ b = b' → (sq : IsPullback gV V'.p V.p g) →
    (hz : V'.zeroSection ≫ gV = g ≫ V.zeroSection) →
      RankOneBaseChangeLaw P b V Λ hΛ c b' V' g gV sq hz

/-- All local equations of the zero section have the positive Kummer-boundary formula.
Source: lem-pur-divisor-class(a), applied to the smooth zero divisor
(blueprint: lem-pur-rank-one-divisor-class-fixed-setting). -/
theorem rankOne_localEquation (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ) :
    LocalEquationLaw P Λ hΛ (V.p ≫ b) V.zeroSection
      (rankOne_zero_ideal P b V) (rankOne_smoothPair P b V) :=
  divisor_localEquation P Λ hΛ (V.p ≫ b) V.zeroSection
    (rankOne_zero_ideal P b V) (rankOne_smoothPair P b V)

/-- Two equation frames give identical actual class arrows on their common chart.
Source: the defining local-equation formula of the global frame class
(blueprint: lem-pur-rank-one-divisor-class-fixed-setting). -/
theorem rankOne_frameIndependent (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ)
    (U : Scheme.{u}) (e : U ⟶ V.E) [IsOpenImmersion e]
    (f₁ f₂ : Γ(U, ⊤))
    (h₁ : (U.zeroLocusSubschemeι {f₁}).ker.IsInvertible)
    (h₂ : (U.zeroLocusSubschemeι {f₂}).ker.IsInvertible)
    (d₁ : U.zeroLocusSubscheme {f₁} ⟶ B) (d₂ : U.zeroLocusSubscheme {f₂} ⟶ B)
    (s₁ : IsPullback d₁ (U.zeroLocusSubschemeι {f₁}) V.zeroSection e)
    (s₂ : IsPullback d₂ (U.zeroLocusSubschemeι {f₂}) V.zeroSection e) :
    closedSourcePull Λ s₁.toCommSq ≫ equationBoundary P Λ hΛ U (e ≫ V.p ≫ b) f₁ h₁ =
      closedSourcePull Λ s₂.toCommSq ≫ equationBoundary P Λ hΛ U (e ≫ V.p ≫ b) f₂ h₂ := by
  have hlocal := rankOne_localEquation P b V Λ hΛ
  exact (hlocal U e f₁ h₁ d₁ s₁).trans (hlocal U e f₂ h₂ d₂ s₂).symm

/-- The bounded-below single object has the published underlying single object. -/
private theorem rankOne_plusSingle_obj
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] (M : C) :
    ((DerivedCategory.Plus.singleFunctor C 0).obj M).obj =
      (DerivedCategory.singleFunctor C 0).obj M := rfl

/-- The global frame-independent rank-one divisor class, its canonical compact-support
normalization, and both arbitrary-base-change equalities, for every admissible Λ.

Source: latest blueprint thm-pur-rank-one-thom, Steps 1 and 3
(blueprint: lem-pur-rank-one-divisor-class-fixed-setting).
Proof: (1) lineZeroGeometry gives the smooth Cartier zero family; in a frame,
multiplication by t in C[t] is injective even for nonreduced C and remains so
after arbitrary base change. (2) Apply the all-admissible divisor-class interface
to this pair and take exactly its global glued frame class cl(D), with local
formula +∂κ(t). Finite type gives finite-dimensional stalks for frame independence.
The evaluation/cocycle-normalized supported-Hom identification gives thom.
(3) Proper coincidence for the closed section and unital direct-image composition
identify Rπ_!z_*Λ with Λ. The displayed properSectionMap realizes this specific
identification σ; applying Rπ_! to thom and precomposing with σ inverse defines τ.
(4) Exact coefficient pullback preserves the Kummer and localization boundary
diagrams, giving the equality of pulled-back global classes. Evaluation on one
and derived representable transport carry that equality to the actual arrows,
using precisely the closed exchange and the specified Tate comparison.
(5) Naturality of compact-support exchange on thom and the class equality give
the τ equation. Paste the section and projection squares: their composite is
the identity square, whose exchange is identity. Proper coincidence and unital
composition thus identify the source exchange with identity under σ.
No isomorphy of τ or reconstruction solely from finite reductions is asserted. -/
theorem rank_one_divisor_class_integral
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1)
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (hΛ : IsAdmissibleCoefficientFor P.coefficients Λ) :
    RankOneDivisorClassData P b V Λ hΛ := by
  refine ⟨?_, ?_, rankOne_localEquation P b V Λ hΛ,
    rankOne_frameIndependent P b V Λ hΛ, ?_⟩
  · rw [V.zeroSection_spec.1]
    infer_instance
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hdim, _⟩ :=
      PurityVectorBundle.lineZeroGeometry P B b V
    exact hdim
  · intro c B' b' _ _ _ V' g gV hg sq hz
    have hpaste : IsPullback g (V'.zeroSection ≫ V'.p)
        (V.zeroSection ≫ V.p) g := by
      rw [V'.zeroSection_spec.1, V.zeroSection_spec.1]
      exact IsPullback.of_id_snd
    have sqz : IsPullback g V'.zeroSection V.zeroSection gV :=
      hpaste.of_bot hz.symm sq
    have hbase : gV ≫ (V.p ≫ b) = V'.p ≫ b' := by
      rw [← Category.assoc, sq.w, Category.assoc, hg]
    have hclass := divisorArrow_pullback P Λ hΛ (V.p ≫ b) (V'.p ≫ b')
      V.zeroSection V'.zeroSection (rankOne_zero_ideal P b V)
      (rankOne_zero_ideal P b' V') (rankOne_smoothPair P b V)
      (rankOne_smoothPair P b' V') g gV hbase sqz
    refine ⟨hclass, ?_⟩
    let F := rightDerivedLowerShriekOfCompactification Λ.X c
    let G := rightDerivedLowerShriekOfCompactification Λ.X (c.ofIsPullback sq)
    let Q := moduleObjectDerivedPullback Λ.X g
    let R := moduleObjectDerivedPullback Λ.X gV
    let σ := canonicalSigma P b V Λ c
    let σ' := canonicalSigma P b' V' Λ (c.ofIsPullback sq)
    let u := unitPull Λ g
    let a := closedSourcePull Λ (CommSq.mk hz.symm)
    let β := (twistPull P Λ hΛ (V'.p ≫ b') (V.p ≫ b) gV).hom
    let t := canonicalThom P b V Λ hΛ
    let t' := canonicalThom P b' V' Λ hΛ
    let S := (DerivedCategory.singleFunctor (Modules Λ V.E) 0).obj
      (source Λ V.zeroSection)
    let T := ((DerivedCategory.singleFunctor (Modules Λ V.E) 0).obj
      (line P Λ hΛ V.E)) ⟦(2 : ℤ)⟧
    have ht : a ≫ t' = R.map t ≫ β := hclass
    have hs : Q.map σ.hom ≫ u.hom =
        compactExchange Λ sq c S ≫ G.map a ≫ σ'.hom :=
      rankOne_properSection_pullback P b V Λ c b' V' g gV sq hz
    have hi : u.hom ≫ σ'.inv =
        Q.map σ.inv ≫ compactExchange Λ sq c S ≫ G.map a := by
      apply (σ'.comp_inv_eq).2
      simp only [Category.assoc]
      apply ((Q.mapIso σ).eq_inv_comp).2
      simpa only [Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc] using hs
    change u.hom ≫ (σ'.inv ≫ G.map t') =
      Q.map (σ.inv ≫ F.map t) ≫ compactExchange Λ sq c T ≫ G.map β
    calc
      u.hom ≫ (σ'.inv ≫ G.map t') =
          (u.hom ≫ σ'.inv) ≫ G.map t' := (Category.assoc _ _ _).symm
      _ = Q.map σ.inv ≫ compactExchange Λ sq c S ≫ G.map (a ≫ t') := by
        rw [hi, G.map_comp]
        simp only [Category.assoc]
      _ = Q.map σ.inv ≫ compactExchange Λ sq c S ≫ G.map (R.map t) ≫ G.map β := by
        rw [ht, G.map_comp]
      _ = Q.map σ.inv ≫ Q.map (F.map t) ≫ compactExchange Λ sq c T ≫ G.map β := by
        have hn := compactExchange_naturality Λ sq c t
        simp only [rankOne_plusSingle_obj] at hn
        simpa only [Category.assoc] using
          congrArg (fun x ↦ Q.map σ.inv ≫ x ≫ G.map β) hn.symm
      _ = Q.map (σ.inv ≫ F.map t) ≫ compactExchange Λ sq c T ≫ G.map β := by
        rw [Q.map_comp]
        simp only [Category.assoc]

end AlgebraicGeometry.ProEtale.CondensedRing
