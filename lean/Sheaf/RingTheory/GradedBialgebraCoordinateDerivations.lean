module

public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! # Coordinate derivations on a connected signed graded bialgebra

Source: Milne, Abelian Varieties, I Lemma 12.2, printed p.55, first sentence of the
proof (Borel structure input). This is the agent-written graded derivation prerequisite,
not a lemma stated in Milne.
(blueprint: lem-sfb-graded-bialgebra-coordinate-derivations).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace GradedAlgebra

/-- Homogeneous lifts of a basis of the augmentation indecomposables admit coordinate
signed derivations, over any field.

Source: Milne, Abelian Varieties, I Lemma 12.2, printed p.55, first sentence of the
proof (Borel structure input); agent-written prerequisite, not a lemma stated in Milne.
(blueprint: lem-sfb-graded-bialgebra-coordinate-derivations).

Proof:
1. Expanding homogeneous components shows that the span of products of two positive-degree
 elements is graded. The quotient Q = I/I² therefore inherits the grading. Let lambda_i
 be the coordinate functional of the homogeneous basis b, and define
 phi_i(a) = lambda_i([a - epsilon(a) * 1]). This vanishes on 1 and I², takes x_j to
 delta_ij, vanishes in degrees other than d_i, and satisfies
 phi_i(ab) = phi_i(a) epsilon(b) + epsilon(a) phi_i(b).
2. By def-weil-pbc-module-tensor-product, contract the first tensor factor against phi_i,
 obtaining C_i(u tensor v) = phi_i(u) v. Set D_i = C_i composed with Delta. Degree
 preservation gives degree -d_i, including zero in degrees below d_i; D_i(1) = 0.
3. Expand Delta(a) and Delta(b) in homogeneous pure tensors. The signed tensor product
 and the identity in step 1 split D_i(ab) into two sums. In the first, epsilon(b_1)
 forces degree b_1 = 0. In the second, epsilon(a_1) forces degree a_1 = 0 and phi_i(b_1)
 forces degree b_1 = d_i. The two counit identities yield exactly
 D_i(ab) = D_i(a)b + (-1)^(d_i deg a) a D_i(b).
4. The other contraction gives epsilon(D_i(a)) = phi_i(a). Hence a_ij = D_i(x_j)
 is zero when d_j < d_i, is delta_ij * 1 when d_j = d_i, and has degree d_j - d_i
 otherwise. Its entries of strictly larger column degree need not vanish.
5. If E has degree -e and h has degree e-d, then hE has degree -d and satisfies
 the signed rule: commute h past a to replace the sign e deg a by d deg a,
 since e + (e-d) and d have the same parity. Sums and differences preserve the rule.
6. In decreasing order of the finitely many generator degrees define
 partial_i = D_i - sum_{j : d_j > d_i} a_ij partial_j. All terms have degree -d_i
 by step 5. This finite recursion preserves linearity, vanishing at 1 and signed Leibniz.
7. In the same decreasing-degree induction, evaluate on each x_l. If d_l > d_i,
 only j = l contributes and cancels a_il. Otherwise all correction terms vanish and
 step 4 gives delta_il. Equal-degree generators are defined simultaneously. With no
 generators there is no i. No division, perfectness, cocommutativity or antipode is used.
-/
theorem exists_coordinate_derivations
    (k : Type u) [Field k]
    (A : Type v) [Ring A] [Algebra k A] [Nontrivial A] [FiniteDimensional k A]
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
    (hconnected : 𝒜 0 = Submodule.span k {(1 : A)})
    (hcomm : ∀ (m n : ℕ) (a : 𝒜 m) (b : 𝒜 n),
      (a : A) * (b : A) = (-1 : k) ^ (m * n) • ((b : A) * (a : A)))
    (Δ : A →ₗ[k] A ⊗[k] A) (ε : A →ₗ[k] k)
    (hdegree : ∀ (n : ℕ) (a : 𝒜 n), Δ a ∈
      Submodule.span k {z | ∃ (p q : ℕ) (b : 𝒜 p) (c : 𝒜 q),
        p + q = n ∧ z = (b : A) ⊗ₜ[k] (c : A)})
    (hunit : Δ 1 = (1 : A) ⊗ₜ[k] (1 : A))
    (hmul : ∀ a b : A,
      GradedTensorProduct.of k 𝒜 𝒜 (Δ (a * b)) =
        GradedTensorProduct.of k 𝒜 𝒜 (Δ a) * GradedTensorProduct.of k 𝒜 𝒜 (Δ b))
    (hcoassoc : ∀ a : A,
      TensorProduct.assoc k A A A (TensorProduct.map Δ LinearMap.id (Δ a)) =
        TensorProduct.map LinearMap.id Δ (Δ a))
    (hprojection : ∀ a : A, algebraMap k A (ε a) = GradedAlgebra.proj 𝒜 0 a)
    (hcounit : ∀ a : A,
      TensorProduct.lid k A (TensorProduct.map ε LinearMap.id (Δ a)) = a ∧
        TensorProduct.rid k A (TensorProduct.map LinearMap.id ε (Δ a)) = a)
    (I : Submodule k A) (hI : I = ⨆ n : {n : ℕ // 0 < n}, 𝒜 n.val)
    (J : Submodule k I)
    (hJ : J = (Submodule.span k {z : A | ∃ a ∈ I, ∃ b ∈ I, z = a * b}).comap I.subtype)
    (s : ℕ) (d : Fin s → ℕ) (hd : ∀ i : Fin s, 0 < d i)
    (x : Fin s → I) (hx : ∀ j : Fin s, (x j : A) ∈ 𝒜 (d j))
    (b : Module.Basis (Fin s) k (I ⧸ J)) (hb : ∀ j : Fin s, b j = J.mkQ (x j)) :
    ∀ i : Fin s, ∃ D : A →ₗ[k] A,
      (∀ (n : ℕ) (a : 𝒜 n),
        D a ∈ (if d i ≤ n then 𝒜 (n - d i) else ⊥)) ∧
      D 1 = 0 ∧
      (∀ j : Fin s, D (x j : A) = if i = j then 1 else 0) ∧
      (∀ (m n : ℕ) (a : 𝒜 m) (c : 𝒜 n),
        D ((a : A) * (c : A)) = D a * (c : A) +
          (-1 : k) ^ (d i * m) • ((a : A) * D c)) := by
  sorry

end GradedAlgebra
