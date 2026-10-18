/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization
import Sheaf.AlgebraicGeometry.IsRegularScheme

/-!
# Coprime generators in a regular local surface

Source: Stacks Project, Curves, Tag 0C48, proof of
`lemma-reduced-quotient-regular-ring-dim-2` (blueprint:
`lem-trf-coprime-generators-mprimary-or-unit`).
-/

@[expose] public section

universe u

namespace RingTheory

/-- Let `(A, 𝔫)` be a regular local ring of Krull dimension two.  If a finite
family of elements has no common nonunit divisor, its generated ideal is the
unit ideal or has radical the maximal ideal.

Source: Stacks Project, Curves, Tag 0C48, proof of
`lemma-reduced-quotient-regular-ring-dim-2`, the paragraph beginning
“Thus the gcd of g_1, ..., g_r is 1”.

Proof. The regular-local UFD statement
`lem-trf-regular-local-ufd-boundary-factorization` gives that `A` is a
Noetherian domain and a UFD.  If the generated ideal is proper, every prime
above it is contained in the maximal ideal.  A nonmaximal such prime has
height one by the dimension-two prime-chain argument, hence is principal by
`lem-trf-ufd-height-one`; its generator would be a common divisor and thus a
unit, a contradiction.  The maximal ideal is therefore the only prime above
the generated ideal, and `PrimeSpectrum.zeroLocus_eq_iff` together with the
radical/intersection description gives the stated radical equality.
(blueprint: lem-trf-coprime-generators-mprimary-or-unit)
-/
theorem coprimeGeneratorsMprimaryOrUnit
    (A : Type u) [CommRing A] [IsRegularLocalRing A]
    (hdim : ringKrullDim A = (2 : WithBot ℕ∞))
    (r : ℕ) (g : Fin r → A)
    (hdiv : ∀ d : A, (∀ i : Fin r, d ∣ g i) → IsUnit d) :
    Ideal.span (Set.range g) = ⊤ ∨
      (Ideal.span (Set.range g)).radical = IsLocalRing.maximalIdeal A := by
  sorry

end RingTheory
