/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.RingTheory.GRing
public import Mathlib.Algebra.Polynomial.Basic
import Sheaf.RingTheory.RegularBaseChange
import Sheaf.RingTheory.LocalizationRegular
import Sheaf.RingTheory.RegularThroughLocalization
import Sheaf.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.PolynomialCompleteLocalFormalFibres
import Sheaf.RingTheory.RegularComposition

/-!
# A comparison local ring for polynomial formal fibres

Source: Stacks Project, More on Algebra, Proposition 07PV, the completion square
in the second paragraph of the proof.
(blueprint: lem-weil-pbc-polynomial-g-ring-comparison).
-/

@[expose] public section

universe u

/-- At a maximal ideal of a polynomial ring over a G-ring, there is a flat local
comparison map into a Noetherian local ring whose composite with completion is regular.
Source: Stacks Project, More on Algebra, Proposition 07PV, the completion square.
(blueprint: lem-weil-pbc-polynomial-g-ring-comparison).

Proof: Let p be the contraction of Q to R and put A = R_p. The localization
A[x] at the extension of Q is canonically R[x]_Q; the extended ideal is maximal
and contracts to the maximal ideal of A. The G-ring hypothesis makes A → Ahat
regular. The ring Ahat is Noetherian complete local. Base change A → Ahat along
A → A[x], then localize at the prime Q' of Ahat[x] lying over Q. This prime is
maximal and contracts to the maximal ideal of Ahat: modulo that ideal the
polynomial rings and Q are unchanged, since A and Ahat have the same residue
field. Set B = Ahat[x]_(Q'). The resulting map φ : R[x]_Q → B is regular,
hence flat, and is local by the contraction identity. Both rings are
Noetherian. The complete-local polynomial formal-fibre theorem makes B → Bhat
regular. The fibres of Bhat over R[x]_Q are Noetherian, being localizations of
quotients of the Noetherian completion Bhat. Composition of regular maps then
gives regularity of R[x]_Q → Bhat. This is only the bottom and right sides of
the comparison square; regularity of the completion of R[x]_Q still requires
completion of φ and faithfully-flat descent. -/
theorem exists_polynomial_flat_local_regular_completion_comparison
    (R : Type u) [CommRing R] (hR : IsGRing R)
    (Q : Ideal (Polynomial R)) [Q.IsMaximal] :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsNoetherianRing B),
      ∃ φ : Localization.AtPrime Q →+* B,
        φ.Flat ∧
        (∀ x : Localization.AtPrime Q,
          x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) →
            φ x ∈ IsLocalRing.maximalIdeal B) ∧
        ((algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)).comp φ).IsRegular := by
  sorry
