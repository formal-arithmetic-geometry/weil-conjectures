/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

/-! # Componentwise curve assertions for finite biproducts

Source: Stacks Project, Theorem 03SC, proof; Lemma 0A5C
(blueprint: lem-pbc-f1-prime-biproduct-unconditional). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.IsCurve

/-- Componentwise equivalence for the unconditional assertions of a finite sum.
Source: Stacks Project, Theorem 03SC, proof, fourth paragraph; Lemma 0A5C.
(blueprint: lem-pbc-f1-prime-biproduct-unconditional).

Proof: Forgetting coefficients, inverse image, and every cohomology functor are additive,
so they carry the given finite biproduct to a finite biproduct. Naturality identifies
cohomology pullback and restriction with sums of the component maps. A finite sum of
abelian groups is subsingleton or finite iff all its components are, and a diagonal
finite sum of maps is bijective or surjective iff every component map is. Apply these
facts degree by degree to C1, C2, C5, C7 and C8. The affine and proper hypotheses
are common to all components. Constructibility of H follows from constructibility of
all G a, closure under finite sums and transport along e; thus the conditional C5
hypotheses can be applied in both directions. Empty sums give the zero sheaf and
zero cohomology, while an empty conjunction of component assertions is true.
The cohomology here is Mathlib's Ext-based `Sheaf.H`: its coefficient functor is
additive, and `Abelian.Ext.addEquivBiproduct` identifies it with the finite product
of component groups. No derived-global-sections bridge is needed. The product
identification sends a class to its images under the projections, with inverse
the sum of its images under the injections. Thus vanishing is tested coordinatewise.
For a scheme map a, naturality `Etale.cohomologyMap_map` with each injection and
projection identifies the comparison with the product of component comparisons.
Injectivity is tested on one coordinate at a time. Surjectivity follows by choosing
preimages for each coordinate and summing the injections; conversely a preimage of
a vector supported in one coordinate gives a preimage in that component. A finite
product is finite iff each factor is finite (each factor is a retract, and all
cohomology groups contain zero). This also proves the asserted finiteness tests. -/
theorem prime_biproduct_unconditional_iff (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    {ι : Type} [Finite ι]
    (G : ι → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hGc : ∀ a, Scheme.IsConstructibleSheaf (G a))
    {H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : H ≅ ⨁ G)
    (hHc : Scheme.IsConstructibleSheaf H) :
    (VanishingAboveTwo Λ H ∧ VanishingAboveOneOfIsAffine Λ H ∧
      FiniteOfIsProper Λ f H ∧ BaseChangeOfIsProper Λ f H ∧
      SurjectiveRestrictionTwo Λ H) ↔
      ∀ a, VanishingAboveTwo Λ (G a) ∧ VanishingAboveOneOfIsAffine Λ (G a) ∧
        FiniteOfIsProper Λ f (G a) ∧ BaseChangeOfIsProper Λ f (G a) ∧
        SurjectiveRestrictionTwo Λ (G a) := by sorry

end AlgebraicGeometry.IsCurve
