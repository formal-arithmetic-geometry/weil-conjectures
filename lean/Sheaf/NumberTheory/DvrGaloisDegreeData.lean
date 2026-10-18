/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.LinearAlgebra.Determinant
import Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import Sheaf.RingTheory.DvrNormValuationSum

/-!
# Global degree data for a finite Galois extension of a DVR

Source: literature/stacks-project/more-algebra.tex, Tags 09E8, 09EA and 09EB
(blueprint: lem-exc-dvr-galois-degree-data).
-/

@[expose] public section

universe u v w z

open scoped Pointwise
open Algebra Module

namespace NumberTheory

/-- For a finite normal separable extension of the fraction field of a DVR, the
integral closure has finitely many maximal ideals above the maximal ideal, the
Galois group acts transitively on them, and all local ramification indices and
residue degrees agree; their product with the number of primes is the field
extension degree.  This is the statement of Stacks Tags 09E8, 09EA and 09EB.
(blueprint: lem-exc-dvr-galois-degree-data)

Proof, following Stacks Tags 09E8, 09EA and 09EB and the node's eight steps:

1. A DVR is a PID, hence Noetherian and normal
   (`lem-weil-pbc-pid-noetherian-normal`), and has dimension one
   (`lem-sc-dvr-dimension-one`).
2. Finite separability gives finite normalization
   (`lem-weil-pbc-noetherian-normal-separable-integral-closure-finite`). The closure
   is normal with fraction field `L`
   (`lem-weil-pbc-integral-closure-finite-extension-normal`), and is Dedekind with
   surjective spectrum, finite fibres and finite residue extensions
   (`lem-sc-integral-closure-dedekind-surjective-fibres`).
3. Maximal ideals contract to the base maximal ideal by integrality
   (`lem-weil-pbc-integral-algebra-ideal-in-radical`). Conversely primes over it
   are nonzero, hence maximal in this one-dimensional domain. This identifies
   `X` with the finite nonempty fibre.
4. Localizations at these maximal ideals are DVRs
   (`lem-sc-dedekind-localization-dvr`). Their maximal ideals contract to the
   base maximal ideal, so the maps are local. The residue field is `B / q`:
   the map `b/s` to the quotient sends denominators to units, is surjective,
   and has kernel `q B_q`. Thus its degree is finite and positive.
5. The image of any base uniformizer is nonzero and a nonunit. Apply
   `lem-weil-pbc-dvr-unit-times-uniformizer-power` in the local DVR to write it
   as a unit times a power of any local uniformizer. The exponent is positive.
   Cancellation shows uniqueness: two distinct exponents would make a unit
   divisible by a nonunit. Two uniformizers differ by a unit, so changing
   either uniformizer leaves the exponent unchanged. This exponent is the
   length of `B_q / πA B_q`, namely `Ideal.ramificationIdx q A`.
6. The canonical restriction action is transitive on primes with the same
   contraction (`lem-exc-finite-galois-prime-residue-lifting`). It therefore
   acts transitively on `X`.
7. Conjugation gives `A`-algebra isomorphisms between the localizations,
   preserving the base uniformizer. Uniqueness of its exponent identifies
   the ramification indices. The induced residue-field isomorphisms preserve
   residue degrees. Nonemptiness supplies common positive integers `e,f`.
8. Apply `lem-exc-dvr-norm-valuation-sum` to the base uniformizer. Its norm,
   the determinant of scalar multiplication (`def-weil-endomorphism-determinant`),
   is `πA^[L:K]`. The normalized valuation gives `[L:K] = Σ_q e_q f_q`.
   All summands equal `e*f`, giving `[L:K] = |X|*e*f`.
-/
theorem dvr_galois_degree_data
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type w) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (B : Type z) [CommRing B] [IsDomain B] [Algebra A B] [Algebra B L]
    [IsScalarTower A B L] [IsIntegralClosure B A L] :
    ((IsLocalRing.maximalIdeal A).primesOver B).Finite ∧
      ((IsLocalRing.maximalIdeal A).primesOver B).Nonempty ∧
      (∀ q : Ideal B,
        q.IsMaximal ↔ q ∈ (IsLocalRing.maximalIdeal A).primesOver B) ∧
      MulAction.IsPretransitive (Gal(L / K))
        {q : Ideal B // q ∈ (IsLocalRing.maximalIdeal A).primesOver B} ∧
      (∀ q : {q : Ideal B // q ∈ (IsLocalRing.maximalIdeal A).primesOver B},
        IsDiscreteValuationRing (Localization.AtPrime q.1) ∧
        IsLocalHom (algebraMap A (Localization.AtPrime q.1))) ∧
      (∀ πA : A, Irreducible πA →
        ∀ q : {q : Ideal B // q ∈ (IsLocalRing.maximalIdeal A).primesOver B},
          ∀ tq : Localization.AtPrime q.1, Irreducible tq →
            ∃ e_q f_q : ℕ, 0 < e_q ∧ 0 < f_q ∧
              ∃ u_q : (Localization.AtPrime q.1)ˣ,
                algebraMap A (Localization.AtPrime q.1) πA =
                    (u_q : Localization.AtPrime q.1) * tq ^ e_q ∧
                  e_q = Ideal.ramificationIdx q.1 A ∧
                  f_q = Ideal.inertiaDeg q.1 A) ∧
      (∃ e f g : ℕ,
        0 < e ∧ 0 < f ∧
        g = ((IsLocalRing.maximalIdeal A).primesOver B).ncard ∧
        (∀ q : {q : Ideal B // q ∈ (IsLocalRing.maximalIdeal A).primesOver B},
          Ideal.ramificationIdx q.1 A = e ∧
            Ideal.inertiaDeg q.1 A = f) ∧
        Module.finrank K L = g * e * f) := by
  sorry

end NumberTheory
