module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Filtration

/-!
# Initial ideals of nearby presentations with nearby relations

Source: Stacks Project, More on Algebra, Tags 07VE (lemma-approximate-complex)
and 07VF (lemma-approximate-complex-graded), the common-subquotient equality
in the proof of 07VF, with `L = Pᵗ`, `M = Pʳ`, `N = P`, and `I = q`
(blueprint: lem-sfb-adic-relation-matrix-initial-ideals).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Ideal

/-- In a Noetherian local ring, sufficiently small simultaneous perturbations
of a row and a relation matrix preserve every piece of its initial ideal,
provided the perturbed maps still form a complex. The ideal `q`, being maximal,
is the unique maximal ideal of `P`. Exactness uses the actual matrix action
`Matrix.mulVec K` and the row action `dotProduct b`.

Source: Stacks Project, More on Algebra, Tags 07VE (lemma-approximate-complex)
and 07VF (lemma-approximate-complex-graded), the equality of subquotients in
the proof of 07VF
(blueprint: lem-sfb-adic-relation-matrix-initial-ideals).

Proof (the node's four steps).
1. Apply `lem-weil-pbc-artin-rees`, namely
   `Ideal.exists_pow_inf_eq_pow_smul`, to the images of `K` and `b`.
   Enlarge the bounds to a common `c`. For either map `v`, lifting scalar
   multiples gives `im v ∩ qⁿV ⊆ v(qⁿ⁻ᶜU)` for `n ≥ c`. Take `h = c + 1`.
2. Coefficient congruence implies that both differences have image in the
   corresponding `q^(c+1)`-multiple. Apply
   `lem-sfb-perturbed-image-artin-rees-bound` with the finite free modules
   `Pᵗ`, `Pʳ`, `P` and maps `K`, `b`, `K'`, `b'`. The original exactness
   and `b'K' = 0` are precisely its complex hypotheses, and localness puts
   `q` in every maximal ideal. This gives the same image bound for `b'`.
3. For `d ≤ c`, an element `b(a)` differs from `b'(a)` by an element of
   `q^(c+1) ⊆ q^(d+1)`. Thus membership in `q^d` is preserved modulo
   `q^(d+1)` in both directions, giving equality of the two ideal sums.
4. For `d > c`, the two image bounds allow a preimage in `q^(d-c)Pʳ`
   for any element of either image lying in `q^d`. Using the same preimage
   for the other row changes its image by an element of
   `q^(c+1) * q^(d-c) = q^(d+1)`. The two inclusions again give equality.
-/
theorem exists_adic_relation_matrix_initial_ideals
    {P : Type u} [CommRing P] [IsNoetherianRing P] [IsLocalRing P]
    (q : Ideal P) [q.IsMaximal] {r t : ℕ}
    (b : Fin r → P) (K : Matrix (Fin r) (Fin t) P)
    (h_exact : Function.Exact (Matrix.mulVec K) (dotProduct b)) :
    ∃ h : ℕ, 1 ≤ h ∧
      ∀ (b' : Fin r → P) (K' : Matrix (Fin r) (Fin t) P),
        (∀ i : Fin r, b i - b' i ∈ q ^ h) →
        (∀ (i : Fin r) (j : Fin t), K i j - K' i j ∈ q ^ h) →
        Matrix.vecMul b' K' = 0 →
        ∀ d : ℕ,
          q ^ (d + 1) + (Ideal.span (Set.range b) ⊓ q ^ d) =
            q ^ (d + 1) + (Ideal.span (Set.range b') ⊓ q ^ d) := by
  sorry

end Ideal
