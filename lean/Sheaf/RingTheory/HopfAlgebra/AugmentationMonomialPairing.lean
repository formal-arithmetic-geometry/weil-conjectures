/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q39
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.FiniteType
public import WeilConjectures.RingTheory.AssociatedGradedRing

/-!
# Augmentation monomials and their convolution pairing

Source: Milne, Algebraic Groups (2017), Sections 11e, 11.24--11.26,
printed pp.216--218, and Lemma 11.27, printed p.218
(blueprint: lem-sfb-hopf-augmentation-monomial-pairing).

The graded pieces are the existing `Ideal.associatedGradedPiece`. Convolution
uses Mathlib's `WithConv` linear dual. Its ordered product is a list product,
so no cocommutativity is required. The ideal parameter is fixed to the kernel
of the counit by `hI`; it only names that canonical ideal.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace HopfAlgebra

/-- The augmentation cotangent space is finite-dimensional. For any lifts of a
basis, the tangent coordinate functionals, characterized uniquely by their
three defining conditions, give the factorial pairing with the degree-`|a|`
monomials in every degree, and these monomials form a basis of every graded
piece whose degree factorial is nonzero. Their ordered convolution words
annihilate the next augmentation power, without any restriction on the word
degree. Empty families and degree zero are included.

Source: Milne, Algebraic Groups (2017), Sections 11e, 11.24--11.26,
printed pp.216--218, and Lemma 11.27, printed p.218
(blueprint: lem-sfb-hopf-augmentation-monomial-pairing).

Proof:
1. Subtract the counit values from finitely many algebra generators. Modulo I^2,
   their classes span I/I^2, proving finite-dimensionality. The splitting
   C = k + I and the dual coordinates of the chosen basis give unique v_i with
   v_i(1) = 0, v_i(I^2) = 0 and v_i(x_j) = delta_ij. Expanding two factors using
   this splitting shows that v_i is a derivation at the counit.
2. By lem-sfb-convolution-linear-map-algebra, the full linear dual has the
   associative convolution product and unit counit. Thus the ordered words
   represented by the list product below have the specified empty product.
3. Apply lem-sfb-bialgebra-counit-word-product-rule to a word of length r and
   r+1 factors in I. Every assignment leaves an empty fibre, whose contribution
   is the counit of a factor in I, hence zero. Such products span I^(r+1),
   proving annihilation for every r, also r = 0.
4. Apply that product rule to n labelled factors in a degree-n monomial. Only
   bijections matching tangent labels to variable labels survive. There are
   no such bijections for different exponent vectors, and exactly prod_i a_i!
   for equal vectors. This proves the displayed factorial evaluation.
5. Expand each of n factors in I in the chosen basis modulo I^2. All terms
   containing an I^2 remainder vanish modulo I^(n+1), proving spanning by the
   degree-n monomials. Evaluate a linear relation with each convolution word.
   Since every a_i! divides n! and n! is nonzero in the field, the factorial
   pairing proves independence, and hence the asserted basis.
6. For n = 0 the sole monomial is 1 and C/I = k. For d = 0, I/I^2 = 0 gives
   I = I^2; the positive graded pieces are zero with empty monomial bases.
   The only exponent vector has degree zero, its monomial is 1, and its word
   is the counit, which kills I. No global identity D_i(x_j) = delta_ij is used:
   the calculation is only after evaluation at the identity. -/
theorem augmentation_monomial_pairing
    (k : Type u) (C : Type v) [Field k] [CommRing C] [HopfAlgebra k C]
    [Algebra.FiniteType k C]
    (I : Ideal C) (hI : I = RingHom.ker (Bialgebra.counitAlgHom k C)) :
    FiniteDimensional k I.Cotangent ∧
      ∀ (d : ℕ) (x : Fin d → I) (b : Module.Basis (Fin d) k I.Cotangent),
        (∀ i : Fin d, b i = I.toCotangent (x i)) →
        ∃ v : Fin d → C →ₗ[k] k,
          (∀ v' : Fin d → C →ₗ[k] k,
            ((∀ i : Fin d, v' i 1 = 0) ∧
              (∀ (i : Fin d) (c : C), c ∈ I ^ 2 → v' i c = 0) ∧
              (∀ i j : Fin d, v' i (x j) = if i = j then 1 else 0)) ↔ v' = v) ∧
          (∀ n : ℕ, (n.factorial : k) ≠ 0 →
            ∃ B : Module.Basis {a : Fin d → ℕ // ∑ i, a i = n} k
                (Ideal.associatedGradedPiece I n),
              ∀ a : {a : Fin d → ℕ // ∑ i, a i = n},
                ∃ ha : (∏ i, (x i : C) ^ a.val i) ∈ I ^ n,
                  B a = Submodule.Quotient.mk
                    (⟨∏ i, (x i : C) ^ a.val i, ha⟩ : (I ^ n : Ideal C))) ∧
          (∀ a b : Fin d → ℕ, (∑ i, a i) = ∑ i, b i →
            (List.ofFn (fun i : Fin d ↦ WithConv.toConv (v i) ^ a i)).prod
                (∏ i, (x i : C) ^ b i) =
              if a = b then ∏ i, (Nat.factorial (a i) : k) else 0) ∧
          (∀ (a : Fin d → ℕ) (c : C), c ∈ I ^ ((∑ i, a i) + 1) →
            (List.ofFn (fun i : Fin d ↦ WithConv.toConv (v i) ^ a i)).prod c = 0) := by
  sorry

end HopfAlgebra
