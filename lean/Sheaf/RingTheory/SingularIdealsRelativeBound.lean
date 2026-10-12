module

public import Sheaf.RingTheory.SingularIdeal
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

universe u v w
namespace Algebra

/-- Relative singular-ideal containment from an annihilator bound.

This is the flat-prime support argument in Stacks Project, Tag 07CT, second paragraph.
At primes where `D` is flat over `R`, the annihilator quotient vanishes by flat base change;
finite support then supplies an annihilator outside the prime. The assumed annihilator bound
makes the corresponding image lie in the relative singular ideal, and the zero-locus
criterion gives the inclusion. The proof is postponed while the requisite support lemmas
are formalized.
(blueprint: lem-weil-pbc-singular-ideals-relative-bound)
-/
theorem singularIdeal_map_le_relative_of_annihilator_bound
    (R : Type u) (D : Type v) (B : Type w)
    [CommRing R] [CommRing D] [CommRing B]
    [Algebra R D] [Algebra R B] [IsNoetherianRing R] [FinitePresentation R D]
    (dB : D →ₐ[R] B)
    (hfp : @FinitePresentation D B _ _ dB.toRingHom.toAlgebra)
    (π : R) (hR : ∀ r : R, r * π = 0 ↔ r * π ^ 2 = 0)
    (hbound : Ideal.span (dB ''
      {r : D | ∀ x : D, (algebraMap R D π) ^ 2 * x = 0 →
        r * algebraMap R D π * x = 0}) ≤
      @singularIdeal D B _ _ dB.toRingHom.toAlgebra) :
    Ideal.map dB.toRingHom (singularIdeal R D) ≤
      @singularIdeal D B _ _ dB.toRingHom.toAlgebra := by
  sorry

end Algebra
