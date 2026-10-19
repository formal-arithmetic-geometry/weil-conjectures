/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q48
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing

import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Irreducible
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# Affine charts of componentwise normalization

Source: Stacks Project, Morphisms, Tag 035P (parts (1), (3), (4)) and Tag 0CDV
(blueprint: lem-per-componentwise-normalization-affine-charts).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The inverse image of an affine open under componentwise normalization is the finite
coproduct of the spectra of the integral closures of the minimal-prime component rings.
Source: Stacks Project, Morphisms, Tag 035P (parts (1), (3), (4)) and Tag 0CDV.

Proof plan (blueprint: lem-per-componentwise-normalization-affine-charts):
1. By `pqf-lem-affine-open-locnoeth`, the affine ring is Noetherian. Its finitely many
minimal primes (`lem-sc-finite-minimal-primes-over-ideal`) index its irreducible components
(`lem-weil-pbc-spec-irreducible-components-minimal-primes`).
2. Restriction bijects components of X meeting U with components of U: injectivity is
`lem-sc-components-open-injection`; surjectivity follows by containing each irreducible
component of U in a component of X (`lem-sc-irreducible-components-cover`) and maximality.
3. By `lem-weil-pbc-reduced-induced-closed-subscheme`, the reduced component chart is
Spec(A/p). Its function field is the fraction field of A/p by
`lem-sc-integral-function-field-affine-fraction`, with the canonical germ inclusion.
4. Apply the affine description in `def-fin-normalization-extension` to the degree-one
extension of this function field, obtaining the spectrum of its integral closure.
5. Restrict the coproduct defining `def-weil-pbc-reduced-normalization` to U. Components
missing U contribute empty schemes; the others give precisely these affine charts.
The coproduct description uses `lem-weil-pbc-scheme-coproduct-family`.
6. Apply `lem-weil-pbc-finite-affine-coproduct-spectrum` for the second isomorphism.
Its coprojections are the spectra of the product projections. On each factor the map is
A → A/p → B; `def-weil-affine-spectrum` identifies the structural map with their product.
7. If U is empty, A is the zero ring and has no prime ideals. The index is empty,
the product is the zero ring, and the coproduct and inverse image are empty. -/
theorem componentwise_normalization_affine_charts
    (X : Scheme.{u}) [IsReduced X] [IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (t : ℕ) (p : Fin t → Ideal Γ(X, U)),
      (∀ i, p i ∈ minimalPrimes Γ(X, U)) ∧ Function.Injective p ∧
      Set.range p = minimalPrimes Γ(X, U) ∧
      ∃ (q : ∀ i, Γ(X, U) →+* (integralClosure
        (Γ(X, U) ⧸ p i) (FractionRing (Γ(X, U) ⧸ p i)))),
      (∀ (i : Fin t) (a : Γ(X, U)),
        q i a = algebraMap (Γ(X, U) ⧸ p i)
          (integralClosure (Γ(X, U) ⧸ p i) (FractionRing (Γ(X, U) ⧸ p i)))
          (Ideal.Quotient.mk (p i) a)) ∧
      ∃ (e₁ : ((X.fromReducedNormalization ⁻¹ᵁ U).toScheme) ≅
          (∐ fun i : Fin t ↦ Spec (.of (integralClosure
            (Γ(X, U) ⧸ p i) (FractionRing (Γ(X, U) ⧸ p i))))))
        (e₂ : (∐ fun i : Fin t ↦ Spec (.of (integralClosure
            (Γ(X, U) ⧸ p i) (FractionRing (Γ(X, U) ⧸ p i))))) ≅
          Spec (.of (∀ i : Fin t, integralClosure
            (Γ(X, U) ⧸ p i) (FractionRing (Γ(X, U) ⧸ p i)))))
        (φ : Γ(X, U) →+* (∀ i : Fin t, integralClosure
          (Γ(X, U) ⧸ p i) (FractionRing (Γ(X, U) ⧸ p i)))),
        (∀ (a : Γ(X, U)) (i : Fin t), φ a i = q i a) ∧
        (e₁.hom ≫
            Sigma.desc (fun i : Fin t ↦ Spec.map (CommRingCat.ofHom (q i))) ≫
              hU.isoSpec.inv = X.fromReducedNormalization ∣_ U) ∧
        (e₂.hom = sigmaSpec (fun i : Fin t ↦ .of (integralClosure
          (Γ(X, U) ⧸ p i) (FractionRing (Γ(X, U) ⧸ p i))))) ∧
        (e₂.hom ≫ Spec.map (CommRingCat.ofHom φ) =
          Sigma.desc (fun i : Fin t ↦ Spec.map (CommRingCat.ofHom (q i)))) ∧
        (U = ⊥ →
          t = 0 ∧ IsEmpty ((X.fromReducedNormalization ⁻¹ᵁ U).toScheme) ∧
            IsEmpty (∐ fun i : Fin t ↦ Spec (.of (integralClosure
              (Γ(X, U) ⧸ p i) (FractionRing (Γ(X, U) ⧸ p i))))) ∧
            ∀ b : (∀ i : Fin t, integralClosure
              (Γ(X, U) ⧸ p i) (FractionRing (Γ(X, U) ⧸ p i))), b = 0) := by
  sorry

end AlgebraicGeometry
