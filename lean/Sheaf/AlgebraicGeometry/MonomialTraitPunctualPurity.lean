/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.AlgebraicGeometry.PunctualPurity
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Sheaf.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra
import WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.TFAE
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic

/-!
# Punctual purity of monomial models over an arbitrary trait

Source: ILO, Exposé XVI, Definition 3.5.11, Proposition 3.5.12 and Lemma 3.5.13,
printed pp.250--251 (blueprint: lem-per-monomial-trait-punctual-purity).

Punctual purity is the existing predicate `IsPunctuallyPure` from
`Sheaf.AlgebraicGeometry.PunctualPurity` (blueprint: def-per-punctual-purity).
It tests invertibility of the canonical Kummer class at every local closed point.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The coordinate ring `R[T₁,…,Tₙ]/(∏ Tᵢ^eᵢ - π)`, retaining zero exponents.
Source: ILO XVI Definition 3.5.11 (blueprint: lem-per-monomial-trait-punctual-purity). -/
abbrev monomialTraitRing (R : Type u) [CommRing R] (π : R) (n : ℕ) (e : Fin n → ℕ) :=
  MvPolynomial (Fin n) R ⧸ Ideal.span
    {(∏ i : Fin n, MvPolynomial.X i ^ e i) - MvPolynomial.C π}

/-- Monomial hypersurfaces over an arbitrary trait are Noetherian, regular and
punctually cohomologically pure. There is no restriction on positive multiplicities,
and no excellence, henselianity or completeness assumption.
Source: ILO XVI Proposition 3.5.12, pp.250--251
(blueprint: lem-per-monomial-trait-punctual-purity).

Proof plan:
1. Use lem-sc-principal-ideal-dvr to identify R as a DVR. Divide the exponent tuple
   by its gcd and use lem-sbc-dvr-uniformizer-root-algebra to adjoin that root of π.
   Eliminating the new uniformizer identifies the original model with the primitive
   model, which is regular by lem-per-primitive-monomial-trait-geometry.
2. Delete zero exponents. The original model is affine space over the remaining one;
   sbc-lem-affine-space-smooth and lem-per-smooth-punctual-purity-ascent restore purity.
3. lem-per-semistable-coordinate-divisor-purity and
   lem-per-monomial-boundary-purity-criterion prove the all-one case. Adjoining a d-th
   root uniformizer and eliminating it gives the equal-exponent case for every d > 0.
4. For exponents prime to ℓ use their lcm d. The coordinate-power cover from the
   equal-exponent model is finite free, with basis the bounded coordinate monomials.
   Its degree is prime to ℓ; use def-pc-finite-locally-free and
   lem-sc-affine-standard-cover-finite-free-local-fp-flat. The reduced preimages of
   coordinate divisors are coordinate divisors. Apply
   lem-per-finite-flat-regular-divisor-purity-descent and the boundary criterion.
5. Multiplying one positive exponent by ℓ is a Kummer root cover. The coordinate
   divisors on both sides are affine spaces over the residue field and are pure by
   lem-per-prime-field-punctual-purity. Use lem-per-kummer-root-regular-divisor-purity
   and lem-per-punctual-purity-two-of-three along those divisors. Off the divisors,
   the cover is surjective etale; use lem-per-punctual-purity-etale-locality.
6. Induct on the sum of the ℓ-adic valuations of the positive exponents, using Step 5
   and Step 4 as base case. Step 2 restores the zero exponents.
-/
theorem monomial_trait_punctual_purity
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (hdim : ringKrullDim R = 1) (π : R)
    (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hunit : IsUnit (ℓ : R))
    (n : ℕ) (hn : 1 ≤ n) (e : Fin n → ℕ) (he : ∃ i, e i ≠ 0) :
    ∃ (_hN : IsNoetherian (Spec (.of (monomialTraitRing R π n e)))),
      IsRegularScheme (Spec (.of (monomialTraitRing R π n e))) ∧
      IsPunctuallyPure ℓ hℓ (Spec (.of (monomialTraitRing R π n e))) := by
  sorry

end AlgebraicGeometry.Etale
