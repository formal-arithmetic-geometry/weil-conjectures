module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Symbolic powers under flat extension

Source: Stacks Project, Algebra, Tag 0BC0, lemma-symbolic-power-flat-extension;
symbolic powers are defined in Tag 0313, definition-symbolic-power
(blueprint: lem-sfb-symbolic-powers-flat-prime-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Ideal

/-- Symbolic powers commute with a flat homomorphism of Noetherian rings when the
extended prime remains prime. Each symbolic power is written explicitly as the
contraction of the ordinary power extended to the localization at the prime.

Source: Stacks Project, Algebra, Tag 0BC0, lemma-symbolic-power-flat-extension,
with the definition of symbolic power in Tag 0313, definition-symbolic-power
(blueprint: lem-sfb-symbolic-powers-flat-prime-extension).

Proof following the seven steps of the node:
1. For n = 0 both sides are the unit ideal. For n > 0, first show that q = pS
   contracts to p. If t is outside p, multiplication by t on R/p is injective.
   By `lem-weil-pbc-flat-tensor-exact` and `lem-weil-pbc-tensor-over-quotient-ring`,
   multiplication by f(t) on S/q is injective. Since q is proper, f(t) is outside q.
   The other inclusion follows from the definition of ideal extension.
2. Put A = R_p, m = pA, k = A/m, B = (R ∖ p)⁻¹S and C = S_q. Step 1 gives B → C.
   By `lem-weil-pbc-localization-tensor-over-base`, A ⊗[R] S is B, with the map
   (r/t) ⊗ s ↦ f(r)s/f(t). By `lem-weil-pbc-module-tensor-cancel-base-change`,
   H ⊗[R] S is H ⊗[A] B for every A-module H, taking h ⊗ s to h ⊗ (s/1).
   These identifications are S-linear. The local ring and residue field come from
   `def-weil-pbc-localization-at-prime`.
3. The kernel of R → A/mⁿ is the symbolic power of p. Tensor this exact sequence
   with S, using `lem-weil-pbc-flat-tensor-exact`. The first image is precisely
   the extended symbolic power: the tensors map to finite sums of f(x)s.
   Step 2 and `lem-weil-pbc-tensor-over-quotient-ring` identify the last tensor
   with B/mⁿB. Thus the left side is the kernel of S → B/mⁿB.
4. Filter A/mⁿ by Fᵢ = mⁱ/mⁿ for 0 ≤ i ≤ n. Flat tensor exactness identifies
   the images Eᵢ of Fᵢ ⊗[R] S inside B/mⁿB with a filtration from E₀ = B/mⁿB
   to Eₙ = 0, whose factors are (mⁱ/mⁱ⁺¹) ⊗[A] B. These identifications
   commute with multiplication by elements of S.
5. Put Gᵢ = mⁱ/mⁱ⁺¹ and D = B/mB. Since m annihilates Gᵢ, the quotient tensor
   identification of `lem-weil-pbc-tensor-over-quotient-ring` makes each factor
   Gᵢ ⊗[k] D. Here D is (R ∖ p)⁻¹(S/q), a nonzero domain by step 1.
   Every s outside q has nonzero image in D. Choose a k-basis of Gᵢ using
   `lem-weil-pbc-vector-space-free`. The unique finite basis expansion in
   Gᵢ ⊗[k] D shows that multiplication by s is injective on each factor.
6. Descending induction on the filtration shows that multiplication by every
   s outside q is injective on B/mⁿB: if sx = 0, the factor calculation puts x
   in the next filtration term, where induction gives x = 0. This implies
   B/mⁿB → C/mⁿC is injective. Explicitly, for a kernel element b/f(t), write
   its image as a finite sum of f(aⱼ)sⱼ/vⱼ, with aⱼ in pⁿ and vⱼ outside q.
   Clearing the denominators in C gives w outside q such that, with V = ∏ vⱼ,
   wVb belongs to pⁿS. Thus wV kills b/f(t) modulo mⁿB; injectivity of its
   multiplication forces that class to be zero. For an empty sum take V = 1.
7. Extension respects ideal products, so qⁿC = pⁿC = mⁿC. The right side is
   the kernel of S → C/mⁿC. By step 6 this equals the kernel of S → B/mⁿB,
   which is the left side by step 3. Together with n = 0 this proves the result.
-/
theorem map_symbolic_power_of_flat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    (f : R →+* S) (hf : f.Flat) (p : Ideal R) [p.IsPrime]
    [(Ideal.map f p).IsPrime] (n : ℕ) :
    Ideal.map f
        (Ideal.comap (algebraMap R (Localization.AtPrime p))
          (Ideal.map (algebraMap R (Localization.AtPrime p)) (p ^ n))) =
      Ideal.comap (algebraMap S (Localization.AtPrime (Ideal.map f p)))
        (Ideal.map (algebraMap S (Localization.AtPrime (Ideal.map f p)))
          ((Ideal.map f p) ^ n)) := by
  sorry

end Ideal
