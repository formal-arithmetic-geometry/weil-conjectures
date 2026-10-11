/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Regular sequences and short exact sequences

Source: literature/stacks-project/algebra.tex, Algebra, Lemma Tag 0F1T
(blueprint: lem-weil-pbc-regular-sequence-short-exact-sequence).
-/

universe u v₁ v₂ v₃

namespace RingTheory.Sequence

/-- (blueprint: lem-weil-pbc-regular-sequence-short-exact-sequence) Let `R` be a
commutative ring, let `0 → M₁ → M₂ → M₃ → 0` be a short exact sequence of
`R`-modules, and let `f` be a finite sequence in `R`. If every entry is a
nonzerodivisor on the corresponding quotients of `M₁` and `M₃`, then it is a
nonzerodivisor on the corresponding quotients of `M₂`, and all induced
quotient sequences are exact; consequently regularity on the two outer terms
implies regularity on the middle term.

Source: Stacks Project, Algebra, Tag 0F1T.

Proof:
1. Linearity sends `I M₁` into `I M₂` and `I M₂` into `I M₃`, giving the induced
   quotient maps. For `Iᵢ = (f₁, ..., fᵢ)`, the cokernel of multiplication by `fᵢ`
   on `N / Iᵢ₋₁ N` is `N / Iᵢ N`; under this identification the cokernel maps
   are the induced quotient maps.
2. Induct on `i`, maintaining short exactness modulo `Iᵢ` and injectivity of
   multiplication on all preceding middle quotients. At `i = 0`, the ideal
   is zero and the given short exact sequence supplies the base case.
3. Apply the snake lemma (lem-weil-pbc-snake-lemma-modules, Stacks Tag 07JW)
   to multiplication by `fᵢ` between two copies of the preceding exact row.
   Both outer kernels vanish by hypothesis, so the middle kernel vanishes.
   The connecting map has zero domain, giving injectivity of the first
   cokernel map; exactness at the middle cokernel and surjectivity of the
   last map give the next short exact row. Step 1 identifies it modulo `Iᵢ`.
4. For part (b), `IsRegular` (def-weil-pbc-regular-sequence) supplies both
   outer nonzerodivisor conditions, hence part (a) supplies the middle one.
   The final quotient of `M₃` is nonzero and is a surjective image of the
   final quotient of `M₂`, so the latter is nonzero as well. -/
theorem isRegular_of_shortExact
    (R : Type u) [CommRing R]
    (M₁ : Type v₁) (M₂ : Type v₂) (M₃ : Type v₃)
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (α : M₁ →ₗ[R] M₂) (β : M₂ →ₗ[R] M₃)
    (hα : Function.Injective α) (hβ : Function.Surjective β)
    (hex : Function.Exact α β)
    (f : List R) :
    (((∀ (i : Fin f.length) (x : M₁ ⧸ ((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₁))),
        f.get i • x = 0 → x = 0) ∧
      ∀ (i : Fin f.length) (x : M₃ ⧸ ((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₃))),
        f.get i • x = 0 → x = 0) →
      (∀ (i : Fin f.length) (x : M₂ ⧸ ((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₂))),
          f.get i • x = 0 → x = 0) ∧
      ∀ (i : Fin (f.length + 1)),
        ∃ (a : M₁ ⧸ ((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₁)) →ₗ[R]
              M₂ ⧸ ((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₂)))
          (b : M₂ ⧸ ((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₂)) →ₗ[R]
              M₃ ⧸ ((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₃))),
          Function.Exact a b ∧ Function.Injective a ∧ Function.Surjective b ∧
          (∀ x : M₁, a (((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₁)).mkQ x) =
            ((Ideal.ofList (f.take i.1) • (⊤ : Submodule R M₂)).mkQ (α x))) ∧
          (∀ x : M₂, b (((Ideal.ofList (f.take i.1)) • (⊤ : Submodule R M₂)).mkQ x) =
            ((Ideal.ofList (f.take i.1) • (⊤ : Submodule R M₃)).mkQ (β x)))) ∧
      ((IsRegular M₁ f ∧ IsRegular M₃ f) → IsRegular M₂ f) := by
  sorry

end RingTheory.Sequence
