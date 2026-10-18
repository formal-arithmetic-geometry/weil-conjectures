/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization

/-!
# Normalization algebra of local curve branches

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
sk-prop-a1-kummer/def-exc-local-curve-branches.md,
node def-exc-local-curve-branches (blueprint: def-exc-local-curve-branches).

## Main definitions

* `excLocalCurveBranchIndex`: the minimal-prime branches.
* `excLocalCurveQ`: the product of the branch fraction fields.
* `excLocalCurveB`: the product of the branch integral closures.
* `excLocalCurveBAlgebraMap`: the canonical structural map.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- The index type of the minimal-prime branches of a commutative ring.
Source: blueprint node def-exc-local-curve-branches (blueprint: def-exc-local-curve-branches). -/
abbrev excLocalCurveBranchIndex (R : Type u) [CommRing R] : Type u :=
  {p : Ideal R // p ∈ (⊥ : Ideal R).minimalPrimes}

/-- The quotient of a ring by one of its minimal primes.
Source: blueprint node def-exc-local-curve-branches (blueprint: def-exc-local-curve-branches). -/
abbrev excLocalCurveBranchQuotient (R : Type u) [CommRing R]
    (p : excLocalCurveBranchIndex R) : Type u := R ⧸ p.1

/-- A minimal-prime quotient is a domain, by Mathlib's prime-quotient instance.
Source: blueprint node def-exc-local-curve-branches (blueprint: def-exc-local-curve-branches). -/
instance excLocalCurveBranchQuotientIsDomain (R : Type u) [CommRing R]
    (p : excLocalCurveBranchIndex R) : IsDomain (excLocalCurveBranchQuotient R p) :=
  @Ideal.Quotient.isDomain R _ p.1 _ p.2.isPrime

/-- The fraction field of a minimal-prime quotient.
The quotient is a domain because the indexing ideal is prime.
Source: blueprint node def-exc-local-curve-branches (blueprint: def-exc-local-curve-branches). -/
abbrev excLocalCurveBranchFractionRing (R : Type u) [CommRing R]
    (p : excLocalCurveBranchIndex R) : Type u :=
  FractionRing (excLocalCurveBranchQuotient R p)

/-- The integral closure of a minimal-prime quotient in its fraction ring, viewed as an
`R`-subalgebra by restriction of scalars.
Source: blueprint node def-exc-local-curve-branches (blueprint: def-exc-local-curve-branches). -/
noncomputable def excLocalCurveBranchIntegralClosure (R : Type u) [CommRing R]
    (p : excLocalCurveBranchIndex R) :
    Subalgebra R (excLocalCurveBranchFractionRing R p) :=
  (integralClosure (excLocalCurveBranchQuotient R p)
    (excLocalCurveBranchFractionRing R p)).restrictScalars R

/-- The product of the fraction fields of the minimal-prime quotients.
Source: blueprint node def-exc-local-curve-branches (blueprint: def-exc-local-curve-branches). -/
abbrev excLocalCurveQ (R : Type u) [CommRing R] [IsReduced R]
    [IsLocalRing R] [IsNoetherianRing R] : Type u :=
  (p : excLocalCurveBranchIndex R) → excLocalCurveBranchFractionRing R p

/-- The branch algebra, the product of the integral closures of the minimal-prime quotients
in their fraction rings.
Source: blueprint node def-exc-local-curve-branches (blueprint: def-exc-local-curve-branches). -/
abbrev excLocalCurveB (R : Type u) [CommRing R] [IsReduced R]
    [IsLocalRing R] [IsNoetherianRing R] : Type u :=
  (p : excLocalCurveBranchIndex R) → excLocalCurveBranchIntegralClosure R p

/-- The canonical algebra map from `R` to one integral-closure factor.
Source: blueprint node def-exc-local-curve-branches (blueprint: def-exc-local-curve-branches). -/
noncomputable def excLocalCurveBranchAlgebraMap (R : Type u) [CommRing R]
    (p : excLocalCurveBranchIndex R) :
    R →ₐ[R] excLocalCurveBranchIntegralClosure R p := by
  let A := excLocalCurveBranchQuotient R p
  let K := excLocalCurveBranchFractionRing R p
  let q : R →ₐ[R] A := Ideal.Quotient.mkₐ R p.1
  let f : A →ₐ[R] K := IsScalarTower.toAlgHom R A K
  let g : R →ₐ[R] K := f.comp q
  exact g.codRestrict (excLocalCurveBranchIntegralClosure R p) (by
    intro r
    change algebraMap A K (q r) ∈ integralClosure A K
    exact (mem_integralClosure_iff A K).2 isIntegral_algebraMap)

/-- The canonical `R`-algebra map into the branch algebra, coordinatewise induced by the
quotient maps and the inclusions into the integral closures.
Source: blueprint node def-exc-local-curve-branches (blueprint: def-exc-local-curve-branches). -/
noncomputable def excLocalCurveBAlgebraMap (R : Type u) [CommRing R] [IsReduced R]
    [IsLocalRing R] [IsNoetherianRing R]
    (_hRdim : ringKrullDim R = (1 : WithBot ℕ∞)) :
    R →ₐ[R] excLocalCurveB R :=
  AlgHom.pi (fun p => excLocalCurveBranchAlgebraMap R p)

end AlgebraicGeometry
