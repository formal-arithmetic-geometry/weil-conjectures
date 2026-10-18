/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Maximal
import Sheaf.RingTheory.UniversallyCatenaryDimensionFormula

/-!
# Dimension of maximal localizations of a finite normalization

Source: Stacks Project, Algebra, Tag 02IJ (dimension formula), specialized to the finite
birational normalization; Greco, Two theorems on excellent rings (1976), Lemma 5.5,
printed p. 147 (blueprint: lem-exc-weakly-etale-normalization-dimension).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace IsUniversallyCatenary

/-- Every maximal localization of the finite normalization of a Noetherian universally
catenary local domain, at a maximal ideal contracting to its maximal ideal, has the
same Krull dimension as the domain.
Source: Stacks Project, Algebra, Tag 02IJ; Greco, Two theorems on excellent rings (1976),
Lemma 5.5, printed p. 147 (blueprint: lem-exc-weakly-etale-normalization-dimension).

Proof:
1. Set C' = integralClosure C K and p = maximalIdeal C. By
   def-weil-pbc-integral-closure, C is a subring of C' inside K and C' is integral over C.
   Fractions from C generate K, so the fraction field of C' is K as well. Finite module
   generators of C' also generate it as an algebra (def-weil-pbc-finite-type-algebra).
   The residue extension at m over p is integral, hence algebraic: reduce the monic
   equations modulo m. Each fraction a/b in K satisfies the nonzero polynomial bT-a.
   Thus both transcendence degrees in def-kun-transcendence-degree are zero.
2. Apply lem-exc-dimension-formula-universally-catenary-finite-type-domain to C inside C'
   and the primes p and m. Noetherianity, universal catenarity, finite type and contraction
   are exactly the stated hypotheses and step 1. The zero transcendence degrees give
   height(m) = height(p).
3. By lem-weil-pbc-localization-dimension-chains-below-prime, dim(C'_m) is the supremum
   of lengths of prime chains ending below m. Append m to a chain ending strictly below
   it, or retain a chain ending at m, to identify this supremum with height(m). Every
   prime of C is below p: lem-weil-pbc-proper-ideal-contained-in-maximal and locality.
   Appending p in the same way gives dim C = height(p). Combine with step 2 to obtain
   dim(C'_m) = dim C. The argument also includes dimension zero.
-/
theorem ringKrullDim_localization_integralClosure_eq
    {C : Type u} [CommRing C] [IsNoetherianRing C] [IsLocalRing C] [IsDomain C]
    {K : Type v} [Field K] [Algebra C K] [IsFractionRing C K]
    [Module.Finite C (integralClosure C K)]
    (hC : IsUniversallyCatenary C)
    (m : Ideal (integralClosure C K)) [m.IsMaximal]
    (hm : m.comap (algebraMap C (integralClosure C K)) = IsLocalRing.maximalIdeal C) :
    ringKrullDim (Localization.AtPrime m) = ringKrullDim C := by
  sorry

end IsUniversallyCatenary
