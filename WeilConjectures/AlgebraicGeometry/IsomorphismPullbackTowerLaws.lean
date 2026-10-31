/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.IsomorphismCoefficientInclusions

/-! # Tower coherence of normalized isomorphism pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
-- These clause packages do not need generated constructor injectivity or size lemmas.
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] constructibleIntegralPullback rationalDerivedPullback
  sfRationalScalarExtension rationalPullbackScalarComparison
  sfIntegralScalarComp sfIntegralScalarUnit
  GeneralAlgebraicallyClosedCoefficients.unitor GeneralAlgebraicallyClosedCoefficients.associator
  AlgebraicallyClosedCoefficients.coefficientInclusion
open AlgebraicallyClosedCoefficients
  (Index Coefficient coefficientInclusion coefficientInclusion_laws)

/-- Tower coherence of the specified completed and rational comparisons.
Source: current blueprint sec-poincare-duality/sk-thm-frobenius,
prop-constructible-truncations.proof.md, final automorphism sentence;
step 8 of lem-pod-isomorphism-pullback-texact-coefficients.
(blueprint: lem-pod-isomorphism-pullback-tower-laws).

Proof: First substitute the component normalizations hα to reduce the integral
family to the prescribed comparisons; taking Iso.hom preserves each component equality.
Choose the simultaneous normalized comparison system for the three coefficient
fields and both inclusions. Its scalarTower equation uses the same quotient models for
all three fields. The comparison-agreement theorem identifies its scalar maps with the
prescribed completed comparisons. The normalized completion comparison conjugates
ordinary tensor association to the specified completed scalar associator. Substitute
these identifications in scalarTower to get the integral equation. Rational localization
preserves composition and whiskering. The prescribed rational comparison and rational
associator have the localized integral components, so their normalizations and object
formulas transfer the integral equation. Transport through coefficientInclusion_laws
gives the displayed integral adapter and canonical rational associator. This includes
identity and ramified inclusions. -/
theorem isomorphismPullbackTowerLaws
    (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (α : ∀ (E L : Index l Ω) (h : E ≤ L),
      constructibleIntegralPullback l (Coefficient.{u} l Ω E) g ⋙
        GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X E L h ≅
      GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h ⋙
        constructibleIntegralPullback l (Coefficient.{u} l Ω L) g)
    (hα : ∀ (E L : Index l Ω) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (α E L h).app K = integralPullbackScalarComparison l (Coefficient.{u} l Ω E)
        (Coefficient.{u} l Ω L) (isomorphismCoefficientInclusion l Ω E L h) g K) :
    (∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω X L M k).map
          ((α E L h).hom.app K) ≫
        (α L M k).hom.app
          ((GeneralAlgebraicallyClosedCoefficients.integralTransition l Ω Y E L h).obj K) ≫
        (constructibleIntegralPullback l (Coefficient.{u} l Ω M) g).map
          ((isomorphismCoefficientIntegralAssociator l Ω Y E L M h k).hom.app K) =
      (isomorphismCoefficientIntegralAssociator l Ω X E L M h k).hom.app
          ((constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).obj K) ≫
        (α E M (h.trans k)).hom.app K) ∧
    (∀ (E L M : Index l Ω) (h : E ≤ L) (k : L ≤ M)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (sfRationalScalarExtension l (Coefficient.{u} l Ω L) X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω M)
          (isomorphismCoefficientInclusion l Ω L M k)).map
          ((rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω L) (isomorphismCoefficientInclusion l Ω E L h) g).hom.app K) ≫
        (rationalPullbackScalarComparison l (Coefficient.{u} l Ω L)
          (Coefficient.{u} l Ω M) (isomorphismCoefficientInclusion l Ω L M k) g).hom.app
          ((sfRationalScalarExtension l (Coefficient.{u} l Ω E) Y 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
          (isomorphismCoefficientInclusion l Ω E L h)).obj K) ≫
        (rationalDerivedPullback l (Coefficient.{u} l Ω M) g).map
          ((GeneralAlgebraicallyClosedCoefficients.associator l Ω Y E L M h k).hom.app K) =
      (GeneralAlgebraicallyClosedCoefficients.associator l Ω X E L M h k).hom.app
          ((rationalDerivedPullback l (Coefficient.{u} l Ω E) g).obj K) ≫
        (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω M)
          (isomorphismCoefficientInclusion l Ω E M (h.trans k)) g).hom.app K) := by
  sorry

end WeilConjectures
