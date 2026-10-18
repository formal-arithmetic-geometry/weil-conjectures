import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.TensorProduct.Maps
open scoped TensorProduct

/-!
# Localization of the separable algebraic diagonal

Source: literature/stacks-project/algebra.tex, Tag 0C2X, lemma-separable-algebraic-diagonal
(blueprint: lem-trf-separable-algebraic-diagonal-localization)

## Main statement

The multiplication map from the tensor square of a separable algebraic field extension
is a localization at a suitable multiplicative subset.
-/

universe u v

namespace Algebra

/--
Localization of the separable algebraic diagonal, following Stacks Project Tag 0C2X.
(blueprint: lem-trf-separable-algebraic-diagonal-localization)

For a separable algebraic extension `k₁/k` there is a submonoid `S` of `R = k₁ ⊗[k] k₁` such
that the multiplication `μ = Algebra.TensorProduct.lmul' k` is a localization map at `S`: every
`μ s` with `s ∈ S` is a unit, every `c : k₁` is `μ x * (μ s)⁻¹` with `s ∈ S`, and every kernel
element of `μ` is killed by an element of `S`.

Proof (blueprint, seven steps).
1. `R` is a commutative ring and `μ` a `k`-algebra map (tensor pushout, clause (2) with
   `f = g = id`). Put `S = {s | μ s ≠ 0}`; it is a submonoid since `k₁` is a field, each
   `μ s` is a unit, and `μ` is surjective since `μ (c ⊗ 1) = c`.
2. Fix `x` with `μ x = 0` and write `x = ∑ aᵢ ⊗ bᵢ`. The field `E = k(b₁, …, bₙ)` is finite
   over `k` (finite algebraic generation) and separable, so `E = k(α)` (primitive element);
   for an empty sum `E = k`.
3. Let `P` be the minimal polynomial of `α`; it is separable. Write `bᵢ = gᵢ(α)` with
   `gᵢ ∈ k[T]` (minimal-polynomial quotient iso), put `F = ∑ aᵢ gᵢ ∈ k₁[T]` and
   `t = 1 ⊗ α`; evaluating with coefficients `c ↦ c ⊗ 1` gives `F(t) = x` and `F(α) = 0`.
4. The geometric-sum identity gives `G(T) - G(α) = (T - α) D_G(T)`; hence `P = (T - α) Q`
   and `F = (T - α) H` with `Q = D_P`, `H = D_F`, and `Q(α) = P'(α)`.
5. Separability gives `U P + V P' = 1`; at `α` this reads `V(α) P'(α) = 1`, so
   `Q(α) ≠ 0` in every characteristic.
6. Put `s = Q(t)`. Then `μ s = Q(α) ≠ 0`, so `s ∈ S`; `P(t) = 1 ⊗ P(α) = 0` since the
   coefficients of `P` lie in `k`; hence `s x = Q(t) (t - α ⊗ 1) H(t) = P(t) H(t) = 0`.
7. On fractions, `r / s ↦ μ r * (μ s)⁻¹` is a well-defined ring map `S⁻¹R → k₁`, surjective
   by step 1 and injective by step 6, so it identifies `μ` with `R → S⁻¹R`; in particular
   the three conditions below hold.
-/
theorem separableAlgebraicDiagonalLocalization
    (k : Type u) (k₁ : Type v) [Field k] [Field k₁] [Algebra k k₁]
    [Algebra.IsSeparable k k₁] :
    ∃ S : Submonoid (k₁ ⊗[k] k₁),
      (∀ s : k₁ ⊗[k] k₁, s ∈ S → IsUnit (Algebra.TensorProduct.lmul' k s)) ∧
      (∀ c : k₁, ∃ x : k₁ ⊗[k] k₁, ∃ s : k₁ ⊗[k] k₁,
        s ∈ S ∧ c = Algebra.TensorProduct.lmul' k x * (Algebra.TensorProduct.lmul' k s)⁻¹) ∧
      (∀ x : k₁ ⊗[k] k₁, Algebra.TensorProduct.lmul' k x = 0 →
        ∃ s : k₁ ⊗[k] k₁, s ∈ S ∧ s * x = 0) := by
  sorry

end Algebra
