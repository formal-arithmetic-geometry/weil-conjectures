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
  sorry

/-- Compactifiability supplied by the projective completion of the line bundle.
Source: lem-pur-line-zero-geometry (blueprint: lem-pur-rank-one-divisor-class-integral).
Proof: the standard open chart of Proj Sym(O_B ⊕ E) is V, and its projection
is proper. This is the compactification recorded by lineZeroGeometry. -/
theorem rankOne_compactifiable (P : WeilConjectures.PurityFiniteSetting.{u})
    {B : Scheme.{u}} (b : B ⟶ Spec (CommRingCat.of P.field.k))
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (V : PurityVectorBundle P B b 1) : HasCompactification V.p := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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

/-- The global frame-independent rank-one divisor class, its canonical compact-support
normalization, and both arbitrary-base-change equalities, for every admissible Λ.

Source: latest blueprint thm-pur-rank-one-thom, Steps 1 and 3
(blueprint: lem-pur-rank-one-divisor-class-integral).
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
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
