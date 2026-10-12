module

public import Sheaf.RingTheory.SingularIdeal
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

universe u v w
namespace Algebra

/-- Absolute singular-ideal containment from an annihilator bound.

This is the smooth-composition paragraph in Stacks Project, Tag 07CT. The relative
containment makes every prime outside the extended singular ideal smooth for `D → B`; smooth
base change and composition then make it smooth for `R → B`, and the radical zero-locus
criterion gives the absolute inclusion. The proof is postponed while the requisite
smooth-composition lemmas are formalized.
(blueprint: lem-weil-pbc-singular-ideals-absolute-bound)
-/
theorem singularIdeal_map_le_absolute_of_annihilator_bound
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
    Ideal.map dB.toRingHom (singularIdeal R D) ≤ singularIdeal R B := by
  sorry

end Algebra
