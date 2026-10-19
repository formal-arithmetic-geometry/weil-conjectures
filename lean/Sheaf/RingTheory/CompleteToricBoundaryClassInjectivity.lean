/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module
public import Sheaf.RingTheory.WeilDivisorClassGroup
public import Sheaf.RingTheory.SharpMonoidFacetForms
public import Sheaf.RingTheory.CompleteToricLocalModel
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Sheaf.RingTheory.CompletedMonoidSupportProjection
import Sheaf.RingTheory.SerreCriterionNormal
import Sheaf.RingTheory.SerreS2TotalFractionMembership
import Sheaf.GroupTheory.SharpConeLatticeIntersection
import Sheaf.RingTheory.CompleteToricFacetValuations
import Sheaf.RingTheory.LogRegularSaturationNormality
import WeilConjectures.RingTheory.CohenRing

/-!
# Injection of toric boundary divisor classes into the complete local class group

Source: ILO, Travaux de Gabber, Exposé VI 1.4 and 1.6(i)--(ii), printed pp. 69--70,
for the complete models; the theorem is the auxiliary agent-formulated class-group
input recorded in the DAG, with Stacks Tags 031S, 031T and 00PD
(blueprint: lem-trf-complete-toric-boundary-class-injectivity).
-/

@[expose] public section

universe u v w t

open Algebra

namespace AddMonoidAlgebra

/-- The primitive facet cokernel `ℤ^𝓕/ν(G)` injects into the Weil divisor class group of
either complete toric model, by `[(m_F)] ↦ [∑ m_F [𝔭_F]]`. The formula on every
representative specifies the boundary map and asserts its well-definedness;
injectivity is the only class-group conclusion (no surjectivity).

Source: ILO VI 1.4 and 1.6(i)--(ii), printed pp. 69--70 (the complete models only; the
argument is the agent's direct divisor route); Stacks Tags 00PD, 031S, 031T
(blueprint: lem-trf-complete-toric-boundary-class-injectivity).

Proof: (1) For `g = a - b`, `div(z^a/z^b) = ∑_F ν_F(g)[𝔭_F]`: the valuation formula
at `𝔭_F`, and at every other height-one prime both monomials are units by the
exhaustive list. Valuations add, so the map is a homomorphism killing `ν(G)`. If
`P = 0` the source is zero. (2) By lem-trf-sharp-cone-lattice-intersection and
lem-trf-complete-toric-facet-valuations, `G ↪ G ⊗ ℚ`, `σ` is pointed,
`P = {g : ν_F(g) ≥ 0 ∀ F}` and `ν` is injective; with `M = ν(G) ⊂ ℤ^r`,
`ν(P) = M ∩ ℕ^r`, and for generators `q_j` and `c = ∑ q_j`, `w = ν(c)` is strictly
positive. (3) With `A = L[[X₁..X_r, t₁..t_n]]`, lem-trf-completed-monoid-support-projection
identifies `B = B_L(P,n)` with the series supported in `ν(P) × ℕ^n`, `z^q ↦ X^{ν(q)}`,
with a `B`-linear retraction `ρ : A → B`. (4) Case (i): `D = A`; case (ii):
`D = A/(Θ)`, `Θ = ι(θ)`; `ρ(Θa) = θρ(a)` gives `B ∩ ΘA = θB`, so `R ⊂ D` with an
`R`-linear retraction `ρ̄`, `ρ̄(X^v) = 0` for `v ∉ M`, `ρ̄(X^{ν(a)}) = z^a`.
(5) By lem-weil-pbc-power-series-local-ring and residue fields, `B`, `R`, `D` are local
with the same residue field and `ρ̄(D^×) ⊂ R^×`. (6) `D` is a complete model for `ℕ^r`;
lem-trf-log-regular-saturation-normality and lem-trf-complete-toric-facet-valuations make
it a normal domain in which the `X_i` are nonzero prime elements. (7) If `(m_F)` is in
the kernel, `div f = ∑ m_F[𝔭_F]`; for large `N, H` the fractions `h = f z^{Nc}` and
`h' = f⁻¹ z^{Hc}` have nonnegative valuation at every height-one prime, hence lie in
every `R_𝔮` (Stacks 00PD). (8) lem-weil-pbc-serre-criterion-normal gives `(S₂)`, and
lem-weil-pbc-serre-s2-total-fraction-membership (Stacks 031S, 031T) gives `h, h' ∈ R`
with `hh' = z^{(N+H)c}`. (9) In `D`, `hh' = X^s`; peeling off the prime `X_i` by
induction on `∑ s_i` gives `h = X^e v`, `v ∈ D^×`. (10) `e ∈ M`: otherwise for
`a = Kw - e ∉ M`, `0 = h ρ̄(X^a) = ρ̄(X^{Kw} v) = z^{Kc} ρ̄(v)`, contradicting
`z^{Kc} ≠ 0` and step 5. (11) Writing `e = ν(a₀)`, `h = z^{a₀} u` with `u = ρ̄(v) ∈ R^×`,
so `f = u z^{a₀}/z^{Nc}` and `(m_F) = ν(a₀ - Nc) ∈ ν(G)`. (12) `P = 0` and `n = 0`
are included; no perfectness, surjectivity or recognition theorem is used. -/
theorem completeToric_boundaryClass_injective
    (P : Type u) [AddCommMonoid P]
    (hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative P))
    (hsharp : ∀ q : Multiplicative P, IsUnit q → q = 1)
    (n : ℕ) (R : Type w) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (z : P → R) (hmodel : IsCompleteToricLocalModel.{t, u, w} n R z)
    (hmonomial : ∀ q : P, z q ≠ 0)
    (F : Type v) [Fintype F] (facets : F ≃ MonoidFacetForm P)
    (primes : F → Ring.WeilHeightOnePrime R) (hdistinct : Function.Injective primes)
    (hboundary : ∀ i : F, (primes i).1.asIdeal =
      Ideal.span {b | ∃ q : P, (facets i).1 (GrothendieckAddGroup.of q) ≠ 0 ∧ b = z q})
    (hvaluation : ∀ (i : F) (q : P),
      Ring.weilOrder (primes i) (z q) = (facets i).1 (GrothendieckAddGroup.of q))
    (hexhaustive : ∀ q : Ring.WeilHeightOnePrime R,
      (∃ a : P, z a ∈ q.1.asIdeal) ↔ ∃ i : F, primes i = q) :
    ∃ β : ((F → ℤ) ⧸ (monoidFacetVector facets).range) →+ Ring.AffineWeilClassGroup R,
      Function.Injective β ∧ ∀ m : F → ℤ,
        β (QuotientAddGroup.mk m) =
          QuotientAddGroup.mk (∑ i : F, Finsupp.single (primes i) (m i)) := by
  sorry

end AddMonoidAlgebra
