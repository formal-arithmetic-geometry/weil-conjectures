/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CanonicalCoefficientPullbackModels
import all WeilConjectures.AlgebraicGeometry.CanonicalCoefficientUnitNormalization
import all WeilConjectures.AlgebraicGeometry.CanonicalCoefficientChainNormalization
import all WeilConjectures.AlgebraicGeometry.CanonicalCoefficientFiniteCompatibility
public import WeilConjectures.AlgebraicGeometry.ConstantWeilStructure
public import WeilConjectures.AlgebraicGeometry.ProEtale.InverseImagePullbackComparison
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientGerm
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedOperationsOnSlices
public import WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.AlgebraicGeometry.ConstantWeilStructure

/-!
# Canonical coefficient pullback and its finite quotient projections

Source: Stacks Tags 03D6 and 08TC; blueprint prop-cohomological-finiteness, Step 7
(blueprint: lem-pod-canonical-coefficient-pullback-reduction).

The sectionwise inverse image used by the specified kappa is compared with the
normalized constant Weil structure through the actual regular-module coefficient
maps. Finite multiplication and projection from the strict Roos cone are retained
as morphisms, including their transition maps before localization. Level n means
positive exponent n+1 throughout.

## Main definitions

* `canonicalCoefficientKappa`: the recorded comparison on the regular good complex.
* `canonicalCoefficientLambda`, `canonicalCoefficientLambdaFinite`: the normalized
  integral comparison and finite multiplication, with coefficient-model transport.
* `canonicalCoefficientRho`: the actual quotient-cone projection and reduction.
* `canonicalCoefficientProjection`, `canonicalCoefficientInverseProjection`: the
  two coefficient projections in the same integral derived category.
* `canonicalCoefficientPullbackTransition`, `canonicalCoefficientInverseTransition`:
  the strict finite quotient transitions.

## Main statements

* `canonicalCoefficientModelMaps_isIso`: the regular coefficient identifications.
* `canonicalCoefficientPullbackReduction`: inverse and projection identities,
  strict transition compatibility, and the published constant-Weil normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] regularExtensionIso regularExtensionPresheafIso
  identityRestrictionIso scalarReductionExistence HasDerivedCategory.standard
  unrestrictedIntegralReductionExistence limit finiteRegularIso finiteSingleRegularIso
  finitePullbackRegularIso pullbackLevelRegularIso pullbackUnitLevel chainUnitCandidate
  integralDerivedPullback integralDerivedPullbackComparison
  constantWeilIntegralRoosComparison
  constantWeilIntegralLambda constantWeilDerivedCoefficientComparison
  SheafOfModules.monoidalCategory constantSheaf
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] canonicalCoefficientIntegralComparison
  canonicalCoefficientInverseImageTransport
  canonicalCoefficientLambda canonicalCoefficientKappa canonicalCoefficientLambdaFinite
  canonicalCoefficientFiniteComparison canonicalCoefficientPullbackReductionIso
  canonicalCoefficientRho canonicalCoefficientProjection canonicalCoefficientInverseProjection
  canonicalCoefficientTheta canonicalCoefficientPullbackTransition canonicalCoefficientTransition
  canonicalCoefficientInverseTransition

attribute [local irreducible] canonicalCoefficientIntegralUnit
  canonicalCoefficientFiniteUnit canonicalCoefficientFiniteKappaComplex
/-- The normalized comparison inverts the specified kappa and preserves its quotient
projections, including the theta projection and strict transition compatibility.
Source: Stacks 03D6, 08TC; blueprint prop-cohomological-finiteness, Proof Step 7
(blueprint: lem-pod-canonical-coefficient-pullback-reduction).
Proof:
1. The pro-etale isomorphism inverse-image theorem relabels sheaves, actions and
products; c_R and c_n transport actions by their inverse coefficient maps.
2. Multiplication x tensor b to c_n inverse(b)*x is inverse to x to x tensor 1.
These are the actual finite chain maps used in lambda_n and commute with reduction.
3. Apply multiplication in both coordinates of Cone(1-s)[-1], using its actual
product projections. This gives L and F(e_n)*L = mu_n*e'_n strictly.
4. Exact countable products and strict Roos comparison identify these concrete
complexes and projections with the specified completed derived pullback model.
5. The regular complex is K-flat with flat terms. Its zero-shifted-coordinate
augmentation is the canonical completeness map eta, invertible by constant
coefficient constructibility and the finite-free-completed-scalar comparison at L=E.
6. The specified kappa is the zero-homotopy augmentation. Multiplication sends
that augmentation to F(eta) in both cone coordinates. Thus the normalized
lambda = F(eta)^(-1)*L has both inverse identities with this actual kappa.
7. The reduction identification is multiplication, transposed from pi_n under the
normalized scalar adjunction. Its quotient and transition equations follow on
pure tensors, so rho is exactly the defining cone projection followed by it.
8. Naturality of multiplication and the cone-projection equation give
Res(lambda_n)*rho_n = F(pi_n)*lambda_R. Compose with c_n and use the coefficient
square to obtain pi_n,X*theta_R = Res(c_n*lambda_n)*rho_n. The strict multiplication
squares give compatibility before localization; the cone homotopy gives rho
compatibility in the derived category.
9. The transport between the two inverse-image models uses only c_R. Consequently
theta is the published normalized constantWeilIntegralTheta, including its
geometric-Frobenius specialization, without a cohomological Frobenius assertion. -/
theorem canonicalCoefficientPullbackReduction (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g]
    (hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    canonicalCoefficientKappa l E g hX hY ≫ (canonicalCoefficientLambda l E g).hom = 𝟙 _ ∧
      (canonicalCoefficientLambda l E g).hom ≫ canonicalCoefficientKappa l E g hX hY =
        𝟙 _ ∧
      (∀ n : ℕ,
        canonicalCoefficientRho l E g n ≫ DerivedCategory.Q.map
            ((canonicalCoefficientRes l E X n).map
              (canonicalCoefficientLambdaFinite l E g n).hom) =
          (canonicalCoefficientLambda l E g).hom ≫
            canonicalCoefficientInverseProjection l E g n) ∧
      (∀ n : ℕ,
        (canonicalCoefficientTheta l E g).hom ≫ canonicalCoefficientProjection l E X n =
          canonicalCoefficientRho l E g n ≫ DerivedCategory.Q.map
            ((canonicalCoefficientRes l E X n).map
              ((canonicalCoefficientLambdaFinite l E g n).hom ≫
                (canonicalCoefficientFiniteComparison l E g n).hom))) ∧
      (∀ n : ℕ,
        canonicalCoefficientPullbackTransition l E g n ≫
            (canonicalCoefficientRes l E X n).map
              (canonicalCoefficientLambdaFinite l E g n).hom =
          (canonicalCoefficientRes l E X (n + 1)).map
              (canonicalCoefficientLambdaFinite l E g (n + 1)).hom ≫
            canonicalCoefficientInverseTransition l E g n) ∧
      (∀ n : ℕ,
        canonicalCoefficientRho l E g (n + 1) ≫
            DerivedCategory.Q.map (canonicalCoefficientPullbackTransition l E g n) =
          canonicalCoefficientRho l E g n) ∧
      canonicalCoefficientTheta l E g = constantWeilIntegralTheta l E g := by
  have hi : canonicalCoefficientKappa l E g hX hY =
      (canonicalCoefficientLambda l E g).inv := by
    rw [coefficientKappa_factor l E g hX hY, coefficientLambda_factor]
    rfl
  refine ⟨?_, ?_, ?_, coefficientTheta_projection l E g,
    coefficientStrictTransition l E g, coefficientRho_compatible l E g,
    coefficientTheta_eq l E g⟩
  · rw [hi]
    exact (canonicalCoefficientLambda l E g).inv_hom_id
  · rw [hi]
    exact (canonicalCoefficientLambda l E g).hom_inv_id
  · intro n
    exact coefficientProjection_inverse l E g n (coefficientTheta_projection l E g n)

end WeilConjectures
