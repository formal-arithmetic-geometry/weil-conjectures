/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalIntegralGaloisFunctor

/-! # Reconstruction for a normalized continuous integral fibre functor

Source: Weil II (1.1.1) b), (1.1.6); Stanford L19, Proposition 1.1.9.
(blueprint: new-e7-integral-galois-equivalence).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme

/-- A normalized integral fibre functor is fully faithful and essentially surjective.
Source: Weil II (1.1.1) b), (1.1.6); Stanford L19, Proposition 1.1.9, third bullet.
(blueprint: new-e7-integral-galois-equivalence).

Faithfulness is already supplied by d.faithful. For fullness, conjugate a representation
morphism by d.τ. Its linearity
preserves every maximal-ideal power, hence the surjective finite fibre projections
induce quotient maps. The evaluation field identifies each quotient action with
c.γ under the canonical set-stalk comparison. Regard each sheaf level as a module
over the finite coefficient quotient. The given finite correspondence is fully
faithful, so the equivariant quotient map lifts uniquely to a map of these finite
module sheaves; restriction of scalars gives the desired integral-level map.
Compatibility of the quotient maps, and faithfulness at a common larger coefficient
quotient, prove naturality of these level maps. Thus they form a morphism of towers.
Completeness and equality after every projection identify its fibre map with the
starting map. The supplied faithfulness proves uniqueness.

For essential surjectivity, reduce a continuous finite integral representation M
modulo every positive power of the maximal ideal. These are finite continuous
representations: their discrete quotient actions are continuous since the adic
quotient maps are open. Apply the inverse of the finite correspondence at each
quotient ring. Restrict scalars to the integer ring. Finite full faithfulness lifts
the reduction arrows, and faithfulness makes their identities and composites
agree. The finite scalar compatibility and the fibre comparisons identify the
stalks with the specified quotients of M at y. At every other geometric point a
fibre path transports these quotient maps and their exact kernel equations, so
the defining lisse integral tower conditions hold there as well. The reconstructed
sheaf F therefore belongs to LisseIntegralSheaf. Completeness of the finite module
M identifies its quotient-system limit with M. Under d.τ the evaluation field
makes this identification equivariant on every quotient, hence on the limit.
It gives d.T(F) isomorphic to M, proving essential surjectivity. Assemble these
fullness, faithfulness and essential-surjectivity results as IsEquivalence.
-/
theorem integral_galois_functor_isEquivalence
    {Y : Scheme.{u}} [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    [IsFundamentalGroup (FiniteEtale.fiber y) G]
    (c : GaloisLisseFiniteCorrespondence y G)
    (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (d : IntegralGaloisForwardData y G c P δ l E) :
    d.T.IsEquivalence := by
  sorry

end AlgebraicGeometry.Scheme
