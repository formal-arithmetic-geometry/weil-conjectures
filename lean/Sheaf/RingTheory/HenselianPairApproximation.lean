/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Sheaf.RingTheory.GRing
import Sheaf.Paper.SmoothSectionEtaleLift
import Sheaf.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.EtaleSectionLiftingOfGabberRoots
import Sheaf.RingTheory.GRingCompletionRegular
import Sheaf.RingTheory.HenselianFactorizationCriterion
import Sheaf.RingTheory.PopescuSmoothing
import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Approximation for henselian pairs with a Noetherian G-ring

Source: Stacks Project, Smoothing Ring Maps, Lemma 0AH5 (case (2))
(blueprint: lem-weil-pbc-henselian-pair-approximation).
-/

@[expose] public section

universe u

/- The polynomial equations in the source are represented by multivariate
polynomials, and the completion congruence by membership in the extended ideal. -/
/--
For a henselian pair whose ring is a G-ring, every solution of a finite system
of polynomial equations in the adic completion is approximated to every
positive order by a solution in the original ring.
Source: Stacks Project, Smoothing Ring Maps, Lemma 0AH5 (case (2))
(blueprint: lem-weil-pbc-henselian-pair-approximation).

Proof: since `A` is a G-ring, `A → A^` is regular (More on Algebra 0AH2); by Popescu's
theorem (Smoothing 07GC) the solution `ahat`, an `A`-algebra map from
`A[x]/(f)` to `A^`, factors through a smooth `A`-algebra `B`. Composing with
`A^ → A/I^N` gives a section `B → A/I^N`, which lifts to an étale `A`-algebra
(More on Algebra 07M7); the henselian property of the pair gives a retraction to
`A` (More on Algebra 09XI), agreeing with the section modulo `I^N` by uniqueness of
`A`-algebra maps to `A/I^N`; the image of the variables is the solution `a`, and the
congruence holds because the kernel of `A^ → A/I^N` is `I^N A^`.
-/
theorem henselian_pair_approximation
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    (hA : IsGRing A) {m n : ℕ}
    (f : Fin m → MvPolynomial (Fin n) A)
    (ahat : Fin n → AdicCompletion I A)
    (hzero : ∀ j : Fin m,
      MvPolynomial.eval₂ (algebraMap A (AdicCompletion I A)) ahat (f j) = 0) :
    ∀ N : ℕ, 1 ≤ N →
      ∃ a : Fin n → A,
        (∀ j : Fin m,
          MvPolynomial.eval₂ (RingHom.id A) a (f j) = 0) ∧
        (∀ k : Fin n,
          ahat k - algebraMap A (AdicCompletion I A) (a k) ∈
            Ideal.map (algebraMap A (AdicCompletion I A)) (I ^ N)) := by
  sorry
