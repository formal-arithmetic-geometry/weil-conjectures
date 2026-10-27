/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import Sheaf.AlgebraicGeometry.ReducedNormalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Irreducible
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-!
# Affine charts of componentwise normalization

Source: Stacks Project, Morphisms, Tags 035P (parts (1), (3), (4)) and 0CDV
(blueprint: lem-per-componentwise-normalization-affine-charts).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The inverse image of an affine open under componentwise normalization is the disjoint
union of the spectra of the integral closures of its minimal-prime quotients, and hence
is the spectrum of their product. The second isomorphism is the canonical `sigmaSpec`;
the structural equation specifies the first over the affine open. The index `ULift (Fin t)`
is just a finite enumeration in the scheme universe, including `t = 0`.

Source: Stacks Project, Morphisms, Tags 035P (1), (3), (4) and 0CDV
(blueprint: lem-per-componentwise-normalization-affine-charts).

Proof plan:
1. The affine ring is Noetherian (pqf-lem-affine-open-locnoeth), so it has finitely many
   minimal primes (lem-sc-finite-minimal-primes-over-ideal). Their zero loci are exactly
   its irreducible components (lem-weil-pbc-spec-irreducible-components-minimal-primes).
2. Components of X meeting U restrict injectively to components of U
   (lem-sc-components-open-injection). Every component of U lies in one of X
   (lem-sc-irreducible-components-cover), so maximality gives surjectivity.
3. The reduced induced component over U is Spec of the minimal-prime quotient
   (lem-weil-pbc-reduced-induced-closed-subscheme). Its function field is canonically
   the fraction field of that quotient (lem-sc-integral-function-field-affine-fraction).
4. The affine construction of function-field normalization (def-fin-normalization-extension,
   specialized to the identity field extension) gives the integral-closure chart with its
   canonical quotient-induced structural map. No finiteness of normalization is used.
5. Restrict the defining component coproduct of def-weil-pbc-reduced-normalization to U.
   The disjoint open cover of lem-weil-pbc-scheme-coproduct-family retains exactly the
   components meeting U. Their charts give the first isomorphism over U.
6. Apply lem-weil-pbc-finite-affine-coproduct-spectrum. Its coprojections are the spectra
   of the product projections; hence the structural ring map has precisely the displayed
   quotient-and-inclusion coordinate maps (def-weil-affine-spectrum).
7. If U is empty its section ring is the zero ring, with no prime ideals. Thus t = 0,
   the product ring is the zero ring, and both the coproduct and the inverse image are empty.
-/
theorem componentwise_normalization_affine_charts
    (X : Scheme.{u}) [IsReduced X] [IsLocallyNoetherian X] (U : X.affineOpens) :
    ∃ (t : ℕ) (p : ULift.{u} (Fin t) → PrimeSpectrum Γ(X, U)),
      Function.Injective p ∧
      Set.range (fun i ↦ (p i).asIdeal) = minimalPrimes Γ(X, U) ∧
      ∃ (e₁ : (X.fromReducedNormalization ⁻¹ᵁ U.1).toScheme ≅
          ∐ (fun i : ULift.{u} (Fin t) ↦
            Spec (.of (integralClosure (Γ(X, U) ⧸ (p i).asIdeal)
              (FractionRing (Γ(X, U) ⧸ (p i).asIdeal))))))
        (e₂ : (∐ (fun i : ULift.{u} (Fin t) ↦
            Spec (.of (integralClosure (Γ(X, U) ⧸ (p i).asIdeal)
              (FractionRing (Γ(X, U) ⧸ (p i).asIdeal)))))) ≅
          Spec (.of (Π i : ULift.{u} (Fin t),
            integralClosure (Γ(X, U) ⧸ (p i).asIdeal)
              (FractionRing (Γ(X, U) ⧸ (p i).asIdeal))))),
        e₂.hom = sigmaSpec (fun i : ULift.{u} (Fin t) ↦
          .of (integralClosure (Γ(X, U) ⧸ (p i).asIdeal)
            (FractionRing (Γ(X, U) ⧸ (p i).asIdeal)))) ∧
        e₁.hom ≫ e₂.hom ≫
            Spec.map (CommRingCat.ofHom (RingHom.pi (fun i : ULift.{u} (Fin t) ↦
              (algebraMap (Γ(X, U) ⧸ (p i).asIdeal)
                (integralClosure (Γ(X, U) ⧸ (p i).asIdeal)
                  (FractionRing (Γ(X, U) ⧸ (p i).asIdeal)))).comp
                    (Ideal.Quotient.mk (p i).asIdeal)))) ≫ U.2.isoSpec.inv =
          X.fromReducedNormalization ∣_ U.1 ∧
        (U.1 = ⊥ → t = 0 ∧
          Subsingleton (Π i : ULift.{u} (Fin t),
            integralClosure (Γ(X, U) ⧸ (p i).asIdeal)
              (FractionRing (Γ(X, U) ⧸ (p i).asIdeal))) ∧
          IsEmpty (∐ (fun i : ULift.{u} (Fin t) ↦
            Spec (.of (integralClosure (Γ(X, U) ⧸ (p i).asIdeal)
              (FractionRing (Γ(X, U) ⧸ (p i).asIdeal)))))) ∧
          IsEmpty (X.fromReducedNormalization ⁻¹ᵁ U.1).toScheme) := by
  sorry

end AlgebraicGeometry
