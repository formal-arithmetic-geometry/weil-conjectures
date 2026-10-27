/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q112
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Sheaf.RingTheory.ExcellentRing
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.RationalRoot
import WeilConjectures.RingTheory.GRing
import WeilConjectures.RingTheory.DVRCompletionRegular
import Sheaf.AlgebraicGeometry.IsRegularScheme
import Sheaf.RingTheory.RegularRingUniversallyCatenary
import Sheaf.RingTheory.JTwoResidueFieldCriterion

/-!
# Excellence of characteristic-zero Dedekind domains

Source: Stacks Project, More on Algebra, Tag 07QW, proposition-ubiquity-excellent,
clauses (1) and (4); Algebra, Tag 00PD, lemma-characterize-dvr
(blueprint: lem-per-characteristic-zero-dedekind-excellent).

## Main statements

* `isExcellent_of_dedekind_of_charZero` includes fields among the Dedekind domains.
* `IsDiscreteValuationRing.isExcellent_of_fractionField_charZero` is its DVR specialization.
-/

@[expose] public section

set_option autoImplicit false

universe u v

/-- A Noetherian integrally closed domain in which every nonzero prime is maximal is
excellent when its fraction field has characteristic zero. No nonzero prime is required,
so fields are included. Source: Stacks Project, More on Algebra, Tag 07QW,
proposition-ubiquity-excellent, clauses (1) and (4)
(blueprint: lem-per-characteristic-zero-dedekind-excellent).

Proof:
1. The prime-ideal hypothesis bounds strict prime chains by one. At each nonzero prime
   `p`, `lem-sc-dedekind-localization-dvr` therefore makes `A_p` a DVR. At zero the
   localization is the fraction field `K`. The fraction field of every `A_p` is again
   `K`: a fraction `(a/s)/(b/t)` is `at/(sb)`, and `a/b` is `(a/1)/(b/1)`.
2. A DVR is Noetherian and has a principal maximal ideal by `def-sc-discrete-valuation-ring`.
   Its dimension is one by `lem-sc-dvr-dimension-one`, so it is regular local by
   `def-weil-regular-scheme`. The zero-prime localization is regular by
   `lem-weil-pbc-field-regular-ring`. Thus `A` is a Noetherian regular ring.
3. Apply `lem-trf-regular-ring-universally-catenary` to obtain universal catenarity.
4. At every nonzero prime use `lem-weil-pbc-dvr-completion-regular`, with the fraction
   field identified in step 1, to get a regular completion map. At zero the completion
   of `K` at its zero ideal is `K`: its quotient system is constant from index one on.
   The completion map is the identity, hence flat, and its sole fibre is geometrically
   regular, since every field extension base changes it to that field, a regular ring
   by `lem-weil-pbc-field-regular-ring`. By `def-weil-pbc-g-ring`, `A` is a G-ring.
5. Check `lem-exc-j2-residue-field-criterion`. At zero a finite purely inseparable
   extension of `K` is trivial in characteristic zero, by
   `def-weil-pbc-finite-purely-inseparable-extension`. Use the image of `A` inside `K`
   as the finite model, with its whole spectrum regular and nonempty by step 2.
   At a nonzero prime `p`, maximality identifies the residue field with `A/p`.
   For a finite purely inseparable residue-field extension `L`, use `B = L`.
   A finite residue-field basis generates `L` over `A`, because coefficients lift
   along `A → A/p`. The fraction field of `B` is `L` and its whole spectrum is a
   nonempty regular open by `lem-weil-pbc-field-regular-ring`. The criterion gives J-2.
6. Noetherianity, the G-ring condition, J-2 and universal catenarity give excellence
   by `def-exc-excellent-ring`. These arguments include the case with no nonzero prime.
-/
theorem isExcellent_of_dedekind_of_charZero
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (hmax : ∀ p : Ideal A, p.IsPrime → p ≠ ⊥ → p.IsMaximal)
    (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] :
    IsExcellent A := by
  sorry

/-- Every DVR with characteristic-zero fraction field is excellent. The DVR hypothesis
is Mathlib's local principal ideal domain with nonzero maximal ideal, equivalent to the
Noetherian local normal dimension-one condition of Stacks Algebra, Tag 00PD.
No completeness, henselianity, or finite-type assumption is imposed.
Source: Stacks Project, More on Algebra, Tag 07QW, clause (4), and Algebra, Tag 00PD,
lemma-characterize-dvr, equivalences (1), (4) and (5)
(blueprint: lem-per-characteristic-zero-dedekind-excellent).

Proof (step 7 of the node): By `def-sc-discrete-valuation-ring`, `R` is a local PID.
`lem-weil-pbc-pid-noetherian-normal` supplies Noetherianity and integral closedness.
`lem-sc-dvr-dimension-one` gives dimension one. A nonzero prime strictly below the
maximal ideal would give a length-two chain from zero, contradicting that dimension
(`def-weil-pbc-krull-dimension-ring`). Hence every nonzero prime is maximal. Apply
`isExcellent_of_dedekind_of_charZero` to `R` and its given fraction field `K`.
-/
theorem IsDiscreteValuationRing.isExcellent_of_fractionField_charZero
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] [CharZero K] :
    IsExcellent R := by
  sorry
