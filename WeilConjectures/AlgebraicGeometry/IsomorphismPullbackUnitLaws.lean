/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.IsomorphismCoefficientInclusions

/-! # Unit coherence of normalized isomorphism pullback -/

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

/-- Unit coherence of the specified completed and rational comparisons.
Source: current blueprint sec-poincare-duality/sk-thm-frobenius,
prop-constructible-truncations.proof.md, final automorphism sentence;
step 8 of lem-pod-isomorphism-pullback-texact-coefficients.
(blueprint: lem-pod-isomorphism-pullback-unit-laws).

Proof: First substitute the component normalizations hα to reduce the integral
family to the prescribed comparisons; taking Iso.hom preserves each component equality.
Use the scalarIdentity field of a normalized integral comparison system.
The comparison-agreement theorem identifies its whole-system map with the prescribed
completed comparison. The normalized scalar unit is ordinary multiplication, conjugated
by completion, so the identity equation is precisely the displayed integral unit law.
Apply the integral-to-rational functor: the prescribed rational comparison and rational
scalar unitor are its images componentwise. Their fixed object formulas identify all
endpoints; functoriality transfers the equation. No morphism is discarded, including
integral torsion morphisms, whose images may vanish. Finally transport through the
actual coefficient-inclusion identity. The rational unitor is the canonical one. -/
theorem isomorphismPullbackUnitLaws
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
    (∀ (E : Index l Ω)
    (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (α E E le_rfl).hom.app K ≫
        (constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).map
          ((isomorphismCoefficientIntegralUnitor l Ω Y E).hom.app K) =
      (isomorphismCoefficientIntegralUnitor l Ω X E).hom.app
        ((constructibleIntegralPullback l (Coefficient.{u} l Ω E) g).obj K)) ∧
    (∀ (E : Index l Ω)
    (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E) Y),
      (rationalPullbackScalarComparison l (Coefficient.{u} l Ω E)
          (Coefficient.{u} l Ω E) (isomorphismCoefficientInclusion l Ω E E le_rfl) g).hom.app K ≫
        (rationalDerivedPullback l (Coefficient.{u} l Ω E) g).map
          ((GeneralAlgebraicallyClosedCoefficients.unitor l Ω Y E).hom.app K) =
      (GeneralAlgebraicallyClosedCoefficients.unitor l Ω X E).hom.app
        ((rationalDerivedPullback l (Coefficient.{u} l Ω E) g).obj K)) := by
  sorry

end WeilConjectures
