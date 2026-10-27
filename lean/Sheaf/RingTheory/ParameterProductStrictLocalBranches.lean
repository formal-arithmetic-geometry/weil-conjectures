/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Sheaf.RingTheory.StrictHenselizationPresentationIn
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Nilpotent.Lemmas

import WeilConjectures.RingTheory.StrictHenselizationRegular
import WeilConjectures.RingTheory.StrictHenselizationLocalMaximalIdeal
import WeilConjectures.RingTheory.StrictHenselizationDimension
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.LocalRing.Quotient
import Sheaf.RingTheory.StrictHenselizationSurjectiveQuotientCore

/-!
# Branches of a parameter product after strict henselization

Source: Stacks Project, Tags 00NQ, 00NP, 05WS, 06LN, 06LK and 07QM;
ILO, Expose VIII, 4.1.6 (printed p.118)
(blueprint: lem-trf-parameter-product-strict-local-branches).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- Distinct positions in a regular parameter list give precisely the minimal primes
of their product after strict henselization. The explicit equations for `F`, `I` and `J`
only name the product and its principal ideals in the two rings. Reduction is the
quotient by `nilradical`, and an equivalence with `Fin r` expresses exactly `r` primes.
The quotient actions on `K` and `H ⧸ J` are required to commute with the quotient map;
thus the separable closure in the final clause is the induced residue-field choice.

Source: Stacks Project, Tags 00NQ, 00NP, 05WS, 06LN, 06LK and 07QM;
ILO VIII 4.1.6 (blueprint: lem-trf-parameter-product-strict-local-branches).

Proof: (1) For `r = 0` the product is one, its ideal is the whole ring, and the quotient
is the zero ring with empty spectrum. All assertions about positions are vacuous.
(2) Otherwise strict henselization is regular local by
`lem-sc-strict-henselization-regular`; its maximal ideal is the extended maximal ideal
by `lem-sc-ring-strict-henselization-local-maximal-ideal`, and its dimension is unchanged
by `lem-sc-strict-henselization-dimension`. Thus the full parameter list stays regular.
(3) Permute each marked parameter to the front. The quotient is regular local by
`lem-weil-pbc-regular-local-generators-regular-sequence`, hence a nonzero domain by
`lem-sc-regular-local-domain`. Permuting two marked parameters to the first two positions
makes the second a nonzerodivisor modulo the first, by `def-weil-pbc-regular-sequence`.
It cannot vanish in that nonzero quotient. Hence the principal primes are incomparable.
(4) A prime containing the product contains a factor. Incomparability now shows that
its minimal possibilities are precisely these distinct principal primes.
(5) The ideal correspondence for quotients preserves prime ideals and their inclusion.
Every prime contains every nilpotent element. Apply the correspondence to `H → H/J`
and then to its reduction to obtain the displayed images and exactly `r` minimal primes.
(6) For `r > 0`, the product belongs to the maximal ideal. The quotient is nonzero local
by `lem-weil-pbc-quotient-local-structure`, and its residue field is canonically that of
`A`. Tag 05WS, in `lem-sbc-strict-henselization-surjective-quotient-core`, identifies
`H/J` as its strict henselization with the quotient-induced actions.
(7) Any other presentation is isomorphic to this one by uniqueness of the pointed-etale
colimit (`def-sc-ring-strict-henselization`). Ring isomorphisms preserve nilpotents and
minimal primes, so its reduction has the same number of minimal primes. -/
theorem parameterProduct_strictLocal_branches
    (A : Type u) (K H : Type (max u v)) [CommRing A] [IsRegularLocalRing A]
    [Field K] [Algebra (IsLocalRing.ResidueField A) K]
    [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing H] [Algebra A H]
    (_P : StrictHenselizationPresentationIn.{u, v} A K H)
    (t : List A) (_ht : IsLocalRing.IsRegularSystemOfParameters t)
    (r : ℕ) (positions : Fin r ↪ Fin t.length)
    (F : A) (_hF : F = ∏ i : Fin r, t.get (positions i))
    (I : Ideal A) (_hI : I = Ideal.span {F})
    (J : Ideal H) (_hJ : J = Ideal.span {algebraMap A H F}) :
    (∀ i : Fin r,
      IsRegularLocalRing (H ⧸ Ideal.span {algebraMap A H (t.get (positions i))}) ∧
      IsDomain (H ⧸ Ideal.span {algebraMap A H (t.get (positions i))}) ∧
      (Ideal.span {algebraMap A H (t.get (positions i))}).IsPrime ∧
      Ideal.span {algebraMap A H (t.get (positions i))} ≠ ⊤) ∧
    (∀ i j : Fin r, i ≠ j →
      algebraMap A H (t.get (positions i)) ∉
        Ideal.span {algebraMap A H (t.get (positions j))}) ∧
    J.minimalPrimes = Set.range
      (fun i : Fin r ↦ Ideal.span {algebraMap A H (t.get (positions i))}) ∧
    minimalPrimes ((H ⧸ J) ⧸ nilradical (H ⧸ J)) = Set.range
      (fun i : Fin r ↦
        (Ideal.span {algebraMap A H (t.get (positions i))}).map
          ((Ideal.Quotient.mk (nilradical (H ⧸ J))).comp (Ideal.Quotient.mk J))) ∧
    Nonempty (↥(minimalPrimes ((H ⧸ J) ⧸ nilradical (H ⧸ J))) ≃ Fin r) ∧
    (0 < r →
      ∃ (_ : IsLocalRing (A ⧸ I)) (_ : Algebra (A ⧸ I) K),
        (algebraMap (A ⧸ I) K).comp (Ideal.Quotient.mk I) = algebraMap A K ∧
        ∃ (_ : Algebra (IsLocalRing.ResidueField (A ⧸ I)) K)
          (_ : IsSepClosure (IsLocalRing.ResidueField (A ⧸ I)) K)
          (_ : IsScalarTower (A ⧸ I) (IsLocalRing.ResidueField (A ⧸ I)) K)
          (_ : Algebra (A ⧸ I) (H ⧸ J)),
          (algebraMap (A ⧸ I) (H ⧸ J)).comp (Ideal.Quotient.mk I) =
            (Ideal.Quotient.mk J).comp (algebraMap A H) ∧
          Nonempty (StrictHenselizationPresentationIn.{u, v} (A ⧸ I) K (H ⧸ J)) ∧
          ∀ (C : Type (max u v)) [CommRing C] [Algebra (A ⧸ I) C],
            Nonempty (StrictHenselizationPresentationIn.{u, v} (A ⧸ I) K C) →
              Nonempty (↥(minimalPrimes (C ⧸ nilradical C)) ≃ Fin r)) ∧
    (r = 0 → F = 1 ∧ Subsingleton (H ⧸ J) ∧ IsEmpty (PrimeSpectrum (H ⧸ J))) := by
  sorry

end Algebra
