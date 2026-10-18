/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Sheaf.RingTheory.QuasiRegularNoetherianLocal

/-!
# Koszul acyclicity detects regular sequences over Noetherian local rings

Source: Stacks Project, More on Algebra, Tag 09CC,
lemma-noetherian-finite-all-equivalent, implication (2) to (1), with `M = R`
(blueprint: lem-per-noetherian-local-koszul-criterion).
-/

@[expose] public section

universe u

namespace RingTheory.Sequence

/-- A sequence in the maximal ideal of a Noetherian local ring is regular if its
Koszul complex has zero homology in every positive degree. The empty sequence is included;
`IsLocalRing R` includes the nontriviality of `R`.
Source: Stacks Project, Tag 09CC, implication (2) to (1), specialized to `M = R`
(blueprint: lem-per-noetherian-local-koszul-criterion).

Proof:
1. If `r = 0`, the injectivity conditions are empty and the final quotient is the
   nonzero ring `R`, so def-weil-pbc-regular-sequence applies. For `r > 0`, put
   `I = (f_1, ..., f_r)` and `B = R/I` using def-weil-pbc-algebra-hom-quotient.
   Since the generators lie in the maximal ideal, `I` is proper and `B` is nonzero.
   Taking degree one in the hypothesis gives vanishing of first Koszul homology.
2. Apply lem-per-h1-koszul-quasi-regular (Stacks Tag 062I) to obtain the canonical
   graded `B`-algebra isomorphism `B[T_1, ..., T_r] → gr_I(R)`, sending `T_j` to
   the degree-one class of `f_j` and coefficients identically to degree zero.
   In degree `n`, it sends a monomial with coefficient `a` to the class of `a f^α`.
   This step needs neither locality nor Noetherianity.
3. Apply lem-pur-quasi-regular-noetherian-local (Stacks Tag 061S) to this same
   canonical isomorphism. The ring is nonzero, local and Noetherian and the
   generators lie in its maximal ideal, as required. Its conclusion gives each
   successive multiplication injective and the final quotient nonzero, exactly
   def-weil-pbc-regular-sequence. Together with Step 1 this covers every `r`. -/
theorem isRegular_of_koszul_homology_vanishing
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (r : ℕ) (f : Fin r → R)
    (hf : ∀ j : Fin r, f j ∈ IsLocalRing.maximalIdeal R)
    (hK : ∀ i : ℕ, 0 < i →
      CategoryTheory.Limits.IsZero ((ExteriorAlgebra.koszulComplex R r f).homology i)) :
    RingTheory.Sequence.IsRegular R (List.ofFn f) := by
  sorry

end RingTheory.Sequence
