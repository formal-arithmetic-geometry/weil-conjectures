module

public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

universe u

namespace Algebra

/-- Formal smoothness gives injectivity of the augmented polynomial truncations.

Source: Stacks Project, Tag 05D5, lifting and correction in the truncation induction.
(blueprint: lem-sbc-formally-smooth-augmentation-truncations-injective)

Proof: The surjectivity component gives surjectivity at every degree. At degree zero
both quotients are zero, and at degree one both augmentations identify the quotients
with B; degree two is the given bijection. Assume bijectivity at degree r ≥ 2.
Lift its inverse composed with C → C/I^r to C → B[X]/J^(r+1) by formal smoothness.
The projection kernel J^r/J^(r+1) is square-zero. Reduction to B shows that this lift
sends I into J/J^(r+1), so it descends through C/I^(r+1). Its composite with f sends
each variable Xᵢ to Xᵢ + δᵢ, with δᵢ in J^r/J^(r+1). Substitution Xᵢ ↦ Xᵢ - δᵢ
inverts this composite: substitution changes a degree-r correction only in degrees
at least 2r-1 ≥ r+1. Thus the composite is injective, and so is f at degree r+1.
Combine this with the separately known surjectivity to continue the induction.
The same calculation uses empty sums for n = 0 and also covers the zero base ring. -/
theorem bijective_augmented_polynomial_truncations_injective
    (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
    [FormallySmooth B C] (ε : C →ₐ[B] B) (n : ℕ)
    (f : MvPolynomial (Fin n) B →ₐ[B] C)
    (hf : MvPolynomial.idealOfVars (Fin n) B ≤
      (RingHom.ker ε.toRingHom).comap f.toRingHom)
    (h₂ : Function.Bijective
      (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ 2) f
        ((pow_le_pow_left' hf 2).trans (Ideal.le_comap_pow f.toRingHom 2)))) :
    ∀ k : ℕ, Function.Injective
      (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ k) f
        ((pow_le_pow_left' hf k).trans (Ideal.le_comap_pow f.toRingHom k))) := by
  sorry

end Algebra
