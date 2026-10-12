/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.RingTheory.GRing
public import Mathlib.Algebra.Polynomial.Basic
import Sheaf.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.FibreRingNoetherian
import Sheaf.RingTheory.LocalizationRegular
import Sheaf.RingTheory.RegularBaseChange
import Sheaf.RingTheory.RegularComposition
import Sheaf.RingTheory.RegularThroughLocalization

/-!
# The regular comparison localization for a polynomial ring over a G-ring

Source: Stacks Project, More on Algebra, Proposition 07PV, second paragraph.
(blueprint: lem-weil-pbc-polynomial-g-ring-regular-comparison).
-/

@[expose] public section

universe u

/-- A polynomial localization over a G-ring maps regularly and locally to a polynomial
localization over a complete Noetherian local ring, at a maximal ideal over its closed point.

Source: Stacks Project, More on Algebra, Proposition 07PV, second paragraph, the bottom
map of the completion square.
(blueprint: lem-weil-pbc-polynomial-g-ring-regular-comparison).

Proof: Contract Q to p in R and let A = R_p. Extend Q to A[x], obtaining a maximal
ideal q whose contraction is the maximal ideal of A: coefficient localization
misses Q, and its quotient remains the field R[x]/Q. Localization at q identifies
A[x]_q with R[x]_Q by the universal properties of successive localization and
polynomial extension. Set S = Ahat, the completion at the maximal ideal m of A.
It is Noetherian and local, with maximal ideal mS. It is complete for mS because
m is finitely generated; thus it is complete at its own maximal ideal. Its
residue field agrees with that of A. Thus q modulo the maximal ideal of A determines
a maximal ideal q' in S[x] modulo the maximal ideal of S, and its inverse image Q'
is maximal and contracts to the maximal ideal of S. The G-ring assumption says
A → S is regular. Base change along the finite type map A → A[x] gives a regular
map A[x] → S[x], using the canonical tensor-product identification. Compose with
the regular localization S[x] → S[x]_(Q'); the composite has Noetherian fibres,
since its target is Noetherian. Its denominators outside q become units, so it
factors through A[x]_q. Regularity through localization makes this factored map
regular. Transport along A[x]_q ≃ R[x]_Q to obtain φ. The contraction of Q' to
A[x] is q (the residue-field identification), so the induced map on localizations
sends the maximal ideal into the maximal ideal, proving the asserted locality.
This constructs only the bottom map; regularity after completion is a separate step. -/
theorem exists_polynomial_regular_local_comparison
    (R : Type u) [CommRing R] (hR : IsGRing R)
    (Q : Ideal (Polynomial R)) [Q.IsMaximal] :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsNoetherianRing S) (_ : IsLocalRing S)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal S) S),
      ∃ (Q' : Ideal (Polynomial S)) (_ : Q'.IsMaximal),
        Q'.comap (Polynomial.C : S →+* Polynomial S) = IsLocalRing.maximalIdeal S ∧
        ∃ φ : Localization.AtPrime Q →+* Localization.AtPrime Q',
          φ.IsRegular ∧
          (∀ x : Localization.AtPrime Q,
            x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q) →
              φ x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q')) := by
  sorry
