/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions

/-! # Componentwise curve assertions for finite biproducts

Source: Stacks Project, Theorem 03SC, proof; Lemma 0A5C
(blueprint: lem-pbc-f1-prime-biproduct-primary). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.IsCurve

/-- Componentwise equivalence for the primary assertions of a prime-killed finite sum.
Source: Stacks Project, Theorem 03SC, proof, fourth paragraph; Lemma 0A5C.
(blueprint: lem-pbc-f1-prime-biproduct-primary).

Proof: At any geometric stalk, all components and H are killed by r. For a prime p
which is the characteristic of k, if p = r every component and H is p-primary.
The C3 conditions then say vanishing of the same cohomology degrees, which is
componentwise by additivity. If p differs from r, any p-primary r-killed stalk
is zero: for each element, Bezout for the coprime integers r and p^n expresses
1 as an integer combination of its two annihilators. Conservativity of geometric
stalks makes any sheaf satisfying this exceptional hypothesis zero. Hence the C3
conclusion is automatic, both when that hypothesis holds for a component and
when it holds for H. Transport cohomology and stalks along e. The empty sum is
zero, and its C3 assertion and the empty universal quantifier are both true.
The cohomology here is Mathlib's Ext-based `Sheaf.H`: its coefficient functor is
additive, and `Abelian.Ext.addEquivBiproduct` identifies it with the finite product
of component groups. No derived-global-sections bridge is needed. The product
identification sends a class to its images under the projections, with inverse
the sum of its images under the injections. Thus vanishing is tested coordinatewise. -/
theorem prime_biproduct_primary_iff (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (r : ℕ) [Fact r.Prime] {ι : Type} [Finite ι]
    (G : ι → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hGr : ∀ a, r • 𝟙 (G a) = 0)
    {H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : H ≅ ⨁ G)
    (hHr : r • 𝟙 H = 0) :
    VanishingAboveOneOfIsPrimaryTorsionSheaf Λ H k ↔
      ∀ a, VanishingAboveOneOfIsPrimaryTorsionSheaf Λ (G a) k := by sorry

end AlgebraicGeometry.IsCurve
