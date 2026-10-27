module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finite image from generic constancy on every prime closed subset

Source: `literature/stacks-project/more-morphisms.tex`, Tag 0ASY,
`lemma-generic-flatness-stratification`; algebra.tex Tags 00IK and 00FR
(blueprint: lem-sfb-noetherian-generically-constant-finite-image).
-/

@[expose] public section
set_option autoImplicit false

universe u v

open Set

namespace WeilConjectures

/-- A function on the prime spectrum of a commutative Noetherian ring which is constant on
a nonempty principal open of every prime closed subset has finite image on every closed subset.
Source: Stacks Project, Tag 00IK, `lemma-Noetherian-basic`, and the induction pattern
of Tag 0ASY, `lemma-generic-flatness-stratification`. The finite-image adaptation is
the agent-written maximal-bad-ideal argument recorded in this node.
(blueprint: lem-sfb-noetherian-generically-constant-finite-image)

Proof plan:
1. For an ideal `J`, let `F J` be the image of `f` on the primes containing `J`.
   If some `F J` were infinite, maximality for submodules of the finite module `A` gives a
   maximal such ideal `I`. Here `1` generates the regular module `A`, so
   `lem-weil-pbc-noetherian-finite-module-acc` and `def-weil-finitely-generated-module`
   apply. Since no prime contains the unit ideal, its image is empty and `I ≠ ⊤`.
2. A maximal bad ideal is prime: if `a * c ∈ I` with neither factor in `I`, then the two
   strictly larger ideals `I + (a)` and `I + (c)` have finite images and cover `V(I)`.
   Indeed a prime containing `I` contains one of `a` and `c`; conversely either larger
   ideal contains `I`. This uses `def-weil-affine-spectrum`.
3. The hypothesis supplies `b ∉ I` and a value `t` on `V(I) ∩ D(b)`. The remaining points
   lie in `V(I + (b))`, whose image is finite by maximality since `b ∉ I`. Thus the
   bad image is contained in the union of `{t}` with a finite set, a contradiction.
4. Hence every `F J` is finite; `F (⊥)` is the range of `f`, including the zero-ring and
   empty-target cases: the zero ring has no proper primes, and a map to the empty
   target can exist only from the empty spectrum.
-/
theorem finite_image_of_generically_constant
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (T : Type v) (f : PrimeSpectrum A → T) :
    (∀ (I : Ideal A), I.IsPrime →
      ∃ b : A, b ∉ I ∧ ∃ t : T,
        ∀ p : PrimeSpectrum A, I ≤ p.asIdeal → b ∉ p.asIdeal → f p = t) →
    (∀ (J : Ideal A), (f '' {p : PrimeSpectrum A | J ≤ p.asIdeal}).Finite) ∧
      (Set.range f).Finite := by
  sorry

end WeilConjectures
end
