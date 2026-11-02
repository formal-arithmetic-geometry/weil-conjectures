/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CohomologyTransport.CondensedIsomorphismCohomologyTransport
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite

/-! # Finite and integral coefficients for canonical condensed cohomology transport

Source: latest blueprint, global geometric Frobenius, ordinary and compact-support composites;
the positive-characteristic integral and finite clauses of the transport lemma.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport)

The existing field-coefficient theorem and all its normalized constructions are reexported.
Finite coefficients use the discrete topology on the actual coefficient-extension quotient.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport

/-- The discrete condensed ring of the dependency's actual quotient O_E/(pi_E^n).
Source: the finite coefficient clause of the transport lemma.
(blueprint: lem-weil-condensed-isomorphism-cohomology-transport) -/
def finiteCoefficient (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E] (n : ℕ) :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} := by
  letI : TopologicalSpace (Padic.coefficientExtensionRing ℓ E n) := ⊥
  letI : DiscreteTopology (Padic.coefficientExtensionRing ℓ E n) :=
    discreteTopology_bot _
  letI : IsTopologicalRing (Padic.coefficientExtensionRing ℓ E n) :=
    DiscreteTopology.topologicalRing
  exact Profinite.continuousCoefficientRingObj (Padic.coefficientExtensionRing ℓ E n)

end AlgebraicGeometry.ProEtale.CondensedRing.CohomologyTransport
