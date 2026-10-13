module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

universe u

namespace Algebra

/-- First-order surjectivity propagates to every augmented polynomial truncation.

Source: Stacks Project, Tag 05D5, surjectivity in the finite-truncation induction.
(blueprint: lem-sbc-formally-smooth-augmentation-truncations-surjective)

Proof: Write I = ker ε and J for the variables ideal. Since f preserves augmentation,
surjectivity modulo I² implies that every element of I is congruent modulo I² to
f(p) for some p in J: the constant coefficient of p must vanish. Therefore every
product of r elements of I is congruent modulo I^(r+1) to an image of a product of
r elements of J. Expanding finite sums gives the same assertion for every element
of I^r. Here coefficients in C can be replaced by their augmentations in B, since
the difference is in I. Start at degree one, where constants represent every class
because c - algebraMap B C (ε c) lies in I. Given a representative modulo I^r,
correct its error in I^r by the polynomial just constructed to obtain a representative
modulo I^(r+1). Degree zero is the zero quotient. This induction proves surjectivity
for every r, including n = 0 and the zero base ring; formal smoothness is not used. -/
theorem bijective_augmented_polynomial_truncations_surjective
    (B C : Type u) [CommRing B] [CommRing C] [Algebra B C]
    (ε : C →ₐ[B] B) (n : ℕ)
    (f : MvPolynomial (Fin n) B →ₐ[B] C)
    (hf : MvPolynomial.idealOfVars (Fin n) B ≤
      (RingHom.ker ε.toRingHom).comap f.toRingHom)
    (h₂ : Function.Surjective
      (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ 2) f
        ((pow_le_pow_left' hf 2).trans (Ideal.le_comap_pow f.toRingHom 2)))) :
    ∀ k : ℕ, Function.Surjective
      (Ideal.quotientMapₐ ((RingHom.ker ε.toRingHom) ^ k) f
        ((pow_le_pow_left' hf k).trans (Ideal.le_comap_pow f.toRingHom k))) := by
  sorry

end Algebra
