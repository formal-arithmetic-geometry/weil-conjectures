/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.Ideal.Pointwise
public import WeilConjectures.RingTheory.StrictlyHenselianNormal
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
import Sheaf.RingTheory.IntegralComponentHenselianPermanence

/-!
# Henselian normalization and localization

Source: Stacks Project, `pione.tex`, Tag 0BSW (`lemma-identify-inertia`), together with
Algebra Tag 092X (`lemma-integral-over-henselian`).
(blueprint: lem-dl-a1-henselian-normalization-localization)

The theorem states the comparison between the integral closure of an ordinary henselization
and the chosen localization of the normalization, including the decomposition-group identity.
-/

@[expose] public section
set_option autoImplicit false

universe u v w z

open IsLocalRing
open scoped Pointwise

namespace Algebra

/-- The henselian normalization is the chosen localization and its stabilizer is the
fraction-field automorphism subgroup.
Source: Stacks Project, pione.tex Tag 0BSW (`lemma-identify-inertia`), and Algebra Tag 092X.
(blueprint: lem-dl-a1-henselian-normalization-localization)

Proof, following the six steps of the DAG node:
1. The integral closure C of H is a subring of a field, hence a nonzero domain with only
   zero-one idempotents. Apply lem-trf-integral-component-henselian-permanence to H to C
   to obtain henselian locality, with unique maximal ideal n.
2. A monic equation over A is also a monic equation over H, so B is contained in C.
   A monic equation over H is one over T; since T is normal with fraction field Omega,
   every element of C lies in T. Thus B is contained in C, which is contained in T.
3. The maximal ideal of T contracts to q in B by the localization-at-prime definition.
   Its contraction to C is proper, hence contained in n. Thus q is contained in the
   proper contraction of n to B. Maximality of q makes that contraction equal to q.
4. Every denominator of B outside q is outside n, so is a unit in C. Its inverse in C
   is its inverse in Omega. Thus every fraction b/s in T lies in C, proving C = T.
5. Each K-automorphism preserves B by applying it and its inverse to monic equations.
   An automorphism stabilizing q acts locally on T by b/s mapped to sigma(b)/sigma(s).
   Its composite with H to T and the given embedding are local A-maps to a henselian
   local ring. Uniqueness in def-weil-pbc-henselization-at-prime makes it fix H, hence
   every fraction of H. This gives one inclusion of the two subgroups.
6. Conversely, an automorphism fixing Frac(H) fixes H, so preserves C by the same monic
   equation argument. It preserves the unique maximal ideal n of C and preserves B.
   It therefore preserves q = B intersect n, proving the reverse subgroup inclusion.
-/
theorem henselianNormalization_localization
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A]
    (Ω : Type v) [Field Ω] [Algebra A Ω]
    (H : Type z)
    (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra K Ω] [IsScalarTower A K Ω] [Algebra.IsAlgebraic K Ω]
    (q : Ideal (integralClosure A Ω)) [q.IsMaximal]
    (_hq : q.comap (algebraMap A (integralClosure A Ω)) = maximalIdeal A)
    [IsIntegrallyClosed (Localization.AtPrime q)]
    [HenselianLocalRing (Localization.AtPrime q)]
    [Algebra (Localization.AtPrime q) Ω] [IsFractionRing (Localization.AtPrime q) Ω]
    (_hTΩ : algebraMap (Localization.AtPrime q) Ω = Ideal.atPrimeToField q)
    [CommRing H] [HenselianLocalRing H] [Algebra A H]
    (_hHdomain : IsDomain H)
    [Algebra (Localization.AtPrime (maximalIdeal A)) H]
    [IsScalarTower A (Localization.AtPrime (maximalIdeal A)) H]
    (_hH : IsHenselizationAtPrime' A (maximalIdeal A) H)
    [Algebra H (Localization.AtPrime q)]
    [IsScalarTower A H (Localization.AtPrime q)]
    (_hHT : IsLocalHom (algebraMap H (Localization.AtPrime q)))
    (_hHTinj : Function.Injective (algebraMap H (Localization.AtPrime q)))
    [Algebra H Ω] [IsScalarTower A H Ω]
    [IsScalarTower H (Localization.AtPrime q) Ω]
    [Algebra (FractionRing H) Ω] [IsScalarTower H (FractionRing H) Ω]
    [Algebra.IsAlgebraic (FractionRing H) Ω] :
    ∃ (_ : HenselianLocalRing (integralClosure H Ω)),
      Set.range (algebraMap (integralClosure H Ω) Ω) =
        Set.range (algebraMap (Localization.AtPrime q) Ω) ∧
      {b : integralClosure A Ω | (b : Ω) ∈
        (integralClosure H Ω).val '' (maximalIdeal (integralClosure H Ω) : Set _)} =
          (q : Set (integralClosure A Ω)) ∧
      MulAction.stabilizer (Ω ≃ₐ[K] Ω) q =
        (IntermediateField.adjoin K
          (Set.range (algebraMap (FractionRing H) Ω))).fixingSubgroup := by
  sorry

end Algebra
