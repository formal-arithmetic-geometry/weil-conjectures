/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.RingTheory.GRing
import Sheaf.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.CompleteLocalGRing
import Sheaf.RingTheory.LocalizationRegular
import Sheaf.RingTheory.RegularComposition
import Sheaf.RingTheory.RegularThroughLocalization

/-!
# A comparison local ring for the maximal-ideal G-ring criterion

Source: Stacks Project, More on Algebra, proof of Lemma 07PT, up to the
regularity of the map from the prime localization into the comparison completion.
(blueprint: lem-weil-pbc-g-ring-maximal-ideal-comparison).
-/

@[expose] public section

universe w

/-- Maximal-local regularity supplies a flat local comparison map whose composite
with the comparison ring's completion map is regular.

Source: Stacks Project, More on Algebra, proof of Lemma 07PT, the diagram and
argument preceding the final application of Lemma 07NT.
(blueprint: lem-weil-pbc-g-ring-maximal-ideal-comparison).

Proof: Choose a maximal ideal m containing p, and put A = R_m. The completion
Ahat is Noetherian by the Noetherian-completion theorem, and local and complete
at its maximal ideal by the local-completion and adic-completeness theorems.
The completion map c : A → Ahat is faithfully flat, so choose a prime q of
Ahat lying over pA. Set B = Ahat_q. Localizing c at q gives a flat local map
A_(pA) → B between Noetherian local rings. The canonical identification
A_(pA) = R_p gives the required map φ. Its locality is precisely the inclusion
of the source maximal ideal into the target maximal ideal.

Since Ahat is complete Noetherian local, it is a G-ring (Tag 07PS), and hence
B → Bhat is regular. The map c is regular by the maximal-ideal hypothesis,
and Ahat → B is regular because it is a localization. Compose these three
regular maps twice using Tag 07QI. Its Noetherian-fibre hypotheses hold because
B and Bhat are Noetherian, and a fibre is a quotient of a localization of
the target. This makes A → Bhat regular. The map factors through the
localization A → A_(pA) = R_p, so regularity through localization makes
B → Bhat composed with φ regular. This proves the stated comparison assertion;
it does not assert regularity of R_p → its own completion. -/
theorem exists_flat_local_regular_completion_comparison
    (R : Type w) [CommRing R] [IsNoetherianRing R]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      RingHom.IsRegular
        (algebraMap (Localization.AtPrime m)
          (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime m))
            (Localization.AtPrime m))))
    (p : Ideal R) [p.IsPrime] :
    ∃ (B : Type w) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsNoetherianRing B),
      ∃ φ : Localization.AtPrime p →+* B,
        φ.Flat ∧
        (∀ x : Localization.AtPrime p,
          x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) →
            φ x ∈ IsLocalRing.maximalIdeal B) ∧
        ((algebraMap B (AdicCompletion (IsLocalRing.maximalIdeal B) B)).comp φ).IsRegular := by
  sorry
