/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions

/-! # Componentwise curve assertions for finite biproducts

Source: Stacks Project, Theorem 03SC, proof; Lemma 0A5C
(blueprint: lem-pbc-f1-prime-biproduct-invertible). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.IsCurve

/-- Componentwise equivalence for the invertible assertions of a prime-killed finite sum.
Source: Stacks Project, Theorem 03SC, proof, fourth paragraph; Lemma 0A5C.
(blueprint: lem-pbc-f1-prime-biproduct-invertible).

Proof: If r is invertible in k, every stalk of each G a and H has invertible-order
torsion, since r kills it. Constructibility of the finite sum and transport along e
supply the C4 hypothesis for H. Cohomology and inverse image are additive and
comparison maps natural, so finiteness and bijectivity are equivalent to the same
properties for all components. This proves both C4 and C6 in this case. If r is
not invertible in the field k, the characteristic is r. Any r-killed sheaf with
invertible-order torsion has zero stalks: each stalk element is killed by r and
by an integer invertible in k, hence coprime to r; Bezout then kills it by 1.
Stalk conservativity makes it the zero sheaf. Its cohomology is zero, finite,
and all comparison maps bijective. This proves all exceptional conditional
assertions for H and for any individual component. Empty sums are zero.
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
theorem prime_biproduct_invertible_iff (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (r : ℕ) [Fact r.Prime] {ι : Type} [Finite ι]
    (G : ι → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hGc : ∀ a, Scheme.IsConstructibleSheaf (G a)) (hGr : ∀ a, r • 𝟙 (G a) = 0)
    {H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : H ≅ ⨁ G)
    (hHr : r • 𝟙 H = 0)
    (hHc : Scheme.IsConstructibleSheaf H) :
    (FiniteOfInvertibleOrder Λ H k ∧ BaseChangeOfInvertibleOrder Λ f H) ↔
      ∀ a, FiniteOfInvertibleOrder Λ (G a) k ∧
        BaseChangeOfInvertibleOrder Λ f (G a) := by sorry

end AlgebraicGeometry.IsCurve
