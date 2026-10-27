/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q24
-/
module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Sheaf.RingTheory.CompleteToricModel
public import Sheaf.RingTheory.WeilDivisorClassGroup
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.Basic
import Sheaf.RingTheory.CompleteToricFacetValuations
import Sheaf.RingTheory.CompleteToricBoundaryClassInjectivity
import Sheaf.GroupTheory.SharpConeLatticeIntersection

/-!
# Divisors of units after monomial localization of complete toric models

Source: the agent-formulated divisor-lifting input for the two complete models of
ILO, Travaux de Gabber, Exposé VI 1.6(i)--(ii), printed p. 70; the retained direct
recognition proof, steps 1 and 4--7. ILO VI 1.4 motivates recognition and is not used
as a converse theorem (blueprint: lem-trf-complete-toric-localized-unit-divisor-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace ToricMonoid

/-- An element of either complete toric model that becomes a unit after inverting
chart monomials is nonzero and has the same order as one chart monomial at every
height-one prime. The orders are the normalized additive DVR valuations: for these
nonzero elements of the normal domain, `Ring.weilOrder` is the length of the local
quotient by the element. Pointwise equality is equivalently equality of principal
Weil divisors. The multiplicative closure of the chart image is exactly that image,
since the model condition gives `z 0 = 1` and `z (a + b) = z a * z b`.

Source: agent-formulated intermediate for ILO VI 1.6(i)--(ii), printed p. 70,
retained direct recognition proof steps 1 and 4--7
(blueprint: lem-trf-complete-toric-localized-unit-divisor-lift).

Proof:
1. Represent the inverse of `f` by `b/z^a`. The fraction relation gives
   `h * (f*b - z^a) = 0` for a chart monomial `h`. Nonzero monomials and the domain
   property give `f*b = z^a ≠ 0`, in particular `f ≠ 0`.
2. By lem-trf-complete-toric-facet-valuations the boundary primes are precisely the
   height-one primes meeting the monomials, with primitive forms `ν_F` giving their
   monomial valuations. By lem-trf-normal-domain-principal-divisor-kernel principal
   divisors have finite support and elements of each local ring have nonnegative
   valuation. Away from the boundary `b/z^a` is a local inverse of `f`, so its order
   is zero. Thus `div(f) = ∑ m_F [p_F]`, with all `m_F ≥ 0`.
3. Apply lem-trf-complete-toric-boundary-class-injectivity to these boundary primes.
   The image of the integer vector `m` is the principal class of `f`, hence zero.
   Injectivity gives an integral lattice point `g` with `ν_F(g) = m_F` for all `F`.
4. By lem-trf-sharp-cone-lattice-intersection the monoid is the lattice intersection
   with its cone. The half-space description in the facet theorem and `m_F ≥ 0`
   put `g` in that cone. Thus `g` is the image of an exponent `a₀ : P`.
5. At a boundary prime the monomial formula gives `v_F(z^a₀) = m_F = v_F(f)`.
   At every other height-one prime both elements are local units, so both orders
   vanish by lem-trf-normal-domain-principal-divisor-kernel. This proves pointwise
   equality, hence equality of divisors. If `P = {0}`, the facet set is empty,
   step 1 gives `f*b = 1`, and `a₀ = 0` works. No step needs a parameter if `n = 0`.
-/
theorem complete_toric_localized_unit_divisor_lift
    (P : Type u) [AddCommMonoid P]
    (hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative P))
    (hsharp : ∀ q : P, IsUnit (Multiplicative.ofAdd q) → q = 0)
    (n : ℕ) (R : Type w) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (z : P → R) (hmodel : IsCompleteModel.{u, v, w} P n R z)
    (hmonomial : ∀ q : P, z q ≠ 0) (f : R)
    (hf : IsUnit (algebraMap R (Localization (Submonoid.closure (Set.range z))) f)) :
    f ≠ 0 ∧ ∃ a₀ : P, ∀ q : Ring.WeilHeightOnePrime R,
      Ring.weilOrder q f = Ring.weilOrder q (z a₀) := by
  sorry

end ToricMonoid
