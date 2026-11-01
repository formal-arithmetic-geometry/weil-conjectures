/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.VectorTensorSiteEquations
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.P1KummerTraceSiteTransport
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorBundlePurity
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegration
public import WeilConjectures.AlgebraicGeometry.VectorBundleZeroSection.VectorBundleZeroSection
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.ConstructibleExceptionalCoefficients.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescent
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundlePurity
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SpecifiedExceptionalClassHom
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteCoordinates
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleOrderedIntegration
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleFrameIntegration
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleVectorIntegration
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.ProEtaleVectorIntegrationArrows
public import WeilConjectures.AlgebraicGeometry.VectorIntegrationSite.FiniteSiteTensorProjection
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedSiteAdjunctionTranspose
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization

/-! # Coordinates for exponent transport of integration

Source: main-20261015, thm-amb-vector-bundle-purity.proof.md, paragraphs 1--2;
Stacks Tags 03PK, 099R and 0B65.
(blueprint: lem-pur-integration-exponent-transpose-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048

universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationSite

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E] (n : ℕ)

section Generic
variable (A : Type (u + 1)) [CommRing A] [Finite A]

end Generic

/-- Shifted root-power transition, fixed by finite Tate descent.
Source: Stacks 03PK (blueprint: lem-pur-integration-exponent-transpose-transport). -/
def integrationLineTransition (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) :
    (Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
      (l ^ (s + 1)) hs T)⟦(2 : ℤ)⟧ ≅
    (Etale.ordinaryFiniteLine (Scheme.finiteTateCoefficient l E n)
      (l ^ (r + 1)) hr T)⟦(2 : ℤ)⟧ :=
  (shiftFunctor _ (2 : ℤ)).mapIso ((DerivedCategory.singleFunctor _ 0).mapIso
    (exponentTransition l E n T hT r s hrs hr hs 1))

/-- Ordered tower transition through the existing coefficient descent.
Source: finite Tate descent and ordered affine coordinates
(blueprint: lem-pur-integration-exponent-transpose-transport). -/
def integrationTowerTransition (T : Scheme.{u}) (hT : IsUnit (l : Γ(T, ⊤)))
    (r s : ℕ) (hrs : r ≤ s)
    (hr : ((l ^ (r + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0)
    (hs : ((l ^ (s + 1) : ℕ) : Scheme.finiteTateCoefficient l E n) = 0) (d : ℕ) :
    (Etale.affineTraceRight (Scheme.finiteTateCoefficient l E n) (l ^ (s + 1)) hs T d).obj
      (Etale.ordinaryFiniteUnit _ T) ≅
    (Etale.affineTraceRight (Scheme.finiteTateCoefficient l E n) (l ^ (r + 1)) hr T d).obj
      (Etale.ordinaryFiniteUnit _ T) :=
  Etale.affineLinearCoefficientDescent _ (l ^ (s + 1)) hs
    (Etale.projectiveLineTraceTransport (l ^ (s + 1))
      (pow_pos (Fact.out : l.Prime).pos _) _ hs) T
    (by simpa only [Nat.cast_pow] using hT.pow (s + 1)) d ≪≫
  (Etale.ordinaryFinitePullback _ (affineTraceProjection T d)).mapIso
    (baseExponentComparison l E n T hT r s hrs hr hs d) ≪≫
  (Etale.affineLinearCoefficientDescent _ (l ^ (r + 1)) hr
    (Etale.projectiveLineTraceTransport (l ^ (r + 1))
      (pow_pos (Fact.out : l.Prime).pos _) _ hr) T
    (by simpa only [Nat.cast_pow] using hT.pow (r + 1)) d).symm

/-- The forward square for a two-component projective decomposition.
Source: Kummer functoriality (blueprint: def-pur-integration-exponent-transport-data). -/
def IntegrationDecompositionSquare {C : Type v} [Category.{w} C]
    [HasZeroMorphisms C] [HasBinaryBiproducts C]
    {Lr Ls U Rr Rs : C} (e : Ls ⟶ Lr) (q : Rs ⟶ Rr)
    (br : (Lr ⊞ U) ≅ Rr) (bs : (Ls ⊞ U) ≅ Rs) : Prop :=
  bs.hom ≫ q = biprod.map e (𝟙 U) ≫ br.hom

end AlgebraicGeometry.ProEtale.VectorIntegrationSite
