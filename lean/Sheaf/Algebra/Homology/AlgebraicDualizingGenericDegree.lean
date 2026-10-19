/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q18
-/
module

public import Sheaf.Algebra.Homology.AlgebraicNormalizedDualizing
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Support
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import Sheaf.Algebra.Homology.PseudoCoherentRHomFlatBaseChange
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.Algebra.Homology.HomComplex
import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses

/-! # The generic degree of a normalized algebraic dualizing complex

Source: Stacks Project, dualizing.tex, Tag 0A7V,
Lemma lemma-nonvanishing-generically-local
(blueprint: lem-per-algebraic-dualizing-generic-degree).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped TensorProduct

namespace DerivedCategory

/-- At a minimal prime, the localized cohomology of a normalized algebraic dualizing
complex is nonzero exactly in minus the dimension of the corresponding quotient.
Source: Stacks Project, Tag 0A7V, lemma-nonvanishing-generically-local
(blueprint: lem-per-algebraic-dualizing-generic-degree).

Proof:
1. Set R = A_p. Noetherianity and minimality give radical(0) = pR. Finite
   generation and the radical-power lemma give n > 0 with p^n R = 0. The ring R
   is nonzero, since a denominator outside p cannot annihilate 1.
2. Set B = A/p^n and pbar = p/p^n. This is a nonzero Noetherian local ring,
   B_pbar = R, and its prime chains identify with those of A/p, so dim B = e.
3. By lem-per-algebraic-dualizing-quotient, RHom_A(B,omega) is normalized
   dualizing over B. Finite bounded cohomology implies pseudo-coherence for omega
   and B[0] by lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion.
4. Localization is flat. Exact tensor computes derived tensor and commutes with
   cohomology. Apply lem-trf-pseudocoherent-rhom-flat-base-change and
   lem-pur-derived-change-of-rings to identify the localization of this B-dualizing
   complex with that of omega; RHom_R(R,W) = W by evaluation at 1.
5. Apply lem-per-algebraic-dualizing-ext-bounds to the B-module B: its cohomology
   N_i vanishes outside [-e,0], and dim Supp(N_i) is at most -i.
6. If (N_i)_pbar is nonzero, the finite-module support-annihilator criterion
   puts Ann(N_i) inside pbar. All primes of B contain pbar, so Supp(N_i) is all
   of Spec B and has dimension e. The bounds force i = -e.
7. Localize the defining homothety and use flat RHom base change again to get
   R[0] = RHom_R(W,W), with W the localization of omega. As R is nonzero, W
   cannot be zero.
8. All cohomology of W except possibly degree -e vanishes by step 6. If that
   degree vanished too, W would be zero in the derived category, contradicting
   step 7. This proves both directions for every integer i. -/
theorem nontrivial_localized_homology_iff_of_isNormalizedAlgebraicDualizing
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [HasDerivedCategory.{u} (RingSiteModules A)]
    (ω : DerivedCategory (RingSiteModules A))
    (hω : IsNormalizedAlgebraicDualizing A ω)
    (p : PrimeSpectrum A) (hp : p.asIdeal ∈ minimalPrimes A)
    (e : ℕ) (he : ringKrullDim (A ⧸ p.asIdeal) = e) (i : ℤ) :
    Nontrivial (Localization.AtPrime p.asIdeal ⊗[A]
      (((homologyFunctor (RingSiteModules A) i).obj ω).val.obj (op ⟨PUnit.unit⟩))) ↔
      i = -(e : ℤ) := by
  sorry

end DerivedCategory
