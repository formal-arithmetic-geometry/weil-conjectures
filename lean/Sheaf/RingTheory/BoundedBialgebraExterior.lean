module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-! # Exterior criterion for a bounded connected graded bialgebra

Source: Milne, Abelian Varieties, I Lemma 12.2, printed p.55, equality case.
(blueprint: lem-sfb-bounded-bialgebra-top-degree-exterior).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace GradedAlgebra

/-- A bounded connected graded bialgebra is the exterior algebra on its degree-one part.

Source: Milne, Abelian Varieties, I Lemma 12.2, printed p.55, equality case.
(blueprint: lem-sfb-bounded-bialgebra-top-degree-exterior).

Proof:
1. Apply lem-sfb-borel-graded-bialgebra-monomial-basis, using perfectness, finite
 dimension, connectedness, signed commutativity, the signed algebra-map condition,
 coassociativity and the two counit identities. Obtain homogeneous generators of positive
 degrees d_j and heights N_j >= 2, whose bounded ordered monomials form a basis.
2. Exactly g generators have degree one. The nonzero top monomial has degree
 D = sum_j (N_j - 1) d_j <= g. Each degree-one generator contributes at least one,
 and any additional generator contributes positively. Thus there are exactly g generators,
 all have degree one and height two. The basis consists of their squarefree products.
 For g = 0 the basis is the singleton consisting of 1.
3. Expand the square of a linear combination of the generators. Their individual squares
 vanish, and each mixed pair cancels by the sign rule. This requires no division by two.
4. Multiplication is alternating: commute repeated factors together and use their
 square-zero property. Apply lem-trf-exterior-power-universal-property in every degree,
 including degree zero, where the map sends a scalar to that scalar times 1.
5. By lem-weil-pbc-exterior-power-free-basis, increasing wedges form a basis. Their
 images are the squarefree monomial basis, giving bijectivity in every degree, including
 vanishing degrees above g. By def-weil-pbc-exterior-algebra, concatenation of pure wedges
 corresponds to multiplication in H. Thus the direct sum of these maps is the asserted
 graded algebra equivalence, canonically characterized by the displayed product formula.
-/
theorem bounded_bialgebra_exterior
    (k : Type u) [Field k] [PerfectField k]
    (H : Type v) [Ring H] [Algebra k H] [Nontrivial H] [FiniteDimensional k H]
    (𝒜 : ℕ → Submodule k H) [GradedAlgebra 𝒜]
    (hconnected : 𝒜 0 = Submodule.span k {(1 : H)})
    (hcomm : ∀ (i j : ℕ) (x : 𝒜 i) (y : 𝒜 j),
      (x : H) * (y : H) = (-1 : k) ^ (i * j) • ((y : H) * (x : H)))
    (Δ : H →ₗ[k] H ⊗[k] H) (ε : H →ₗ[k] k)
    (hdegree : ∀ (n : ℕ) (x : 𝒜 n), Δ x ∈
      Submodule.span k {z | ∃ (i j : ℕ) (a : 𝒜 i) (b : 𝒜 j),
        i + j = n ∧ z = (a : H) ⊗ₜ[k] (b : H)})
    (hunit : Δ 1 = (1 : H) ⊗ₜ[k] (1 : H))
    (hmul : ∀ x y : H,
      GradedTensorProduct.of k 𝒜 𝒜 (Δ (x * y)) =
        GradedTensorProduct.of k 𝒜 𝒜 (Δ x) * GradedTensorProduct.of k 𝒜 𝒜 (Δ y))
    (hcoassoc : ∀ x : H,
      TensorProduct.assoc k H H H (TensorProduct.map Δ LinearMap.id (Δ x)) =
        TensorProduct.map LinearMap.id Δ (Δ x))
    (hprojection : ∀ x : H, algebraMap k H (ε x) = GradedAlgebra.proj 𝒜 0 x)
    (hcounit : ∀ x : H,
      TensorProduct.lid k H (TensorProduct.map ε LinearMap.id (Δ x)) = x ∧
        TensorProduct.rid k H (TensorProduct.map LinearMap.id ε (Δ x)) = x)
    (g : ℕ) (hdim : Module.finrank k (𝒜 1) = g)
    (hbound : ∀ i : ℕ, g < i → 𝒜 i = ⊥) :
    (∀ x : 𝒜 1, (x : H) * (x : H) = 0) ∧
      ∃ e : ExteriorAlgebra k (𝒜 1) ≃ₐ[k] H,
        (∀ (n : ℕ) (x : Fin n → 𝒜 1),
          e (ExteriorAlgebra.ιMulti k n x) = (List.ofFn fun i ↦ (x i : H)).prod) ∧
        (∀ n : ℕ, (ExteriorAlgebra.exteriorPower k n (𝒜 1)).map e.toLinearMap = 𝒜 n) := by
  sorry

end GradedAlgebra
