module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Data.List.OfFn

/-! # Borel's homogeneous monomial basis for a finite graded bialgebra

Source: Milne, Abelian Varieties, I Lemma 12.2, printed p.55, first sentence of
the proof quoting Borel (1953), in the finite-dimensional bounded-monomial form.
(blueprint: lem-sfb-borel-graded-bialgebra-monomial-basis).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct BigOperators

namespace GradedAlgebra

/-- Homogeneous nilpotent generators whose bounded ordered monomials are a basis.

Source: Milne, Abelian Varieties, I Lemma 12.2, printed p.55, first sentence of
the proof quoting Borel (1953).
(blueprint: lem-sfb-borel-graded-bialgebra-monomial-basis).

The signed product is Mathlib's `GradedTensorProduct` multiplication. The index
of the basis records one exponent strictly below each height. `List.ofFn` fixes
the increasing order of the generators, and its product is 1 when r = 0.

Proof:
1. Let I be the positive-degree augmentation ideal and Q = I/I^2. Only finitely
many graded pieces are nonzero, so I is nilpotent. Lift a homogeneous basis of
Q to positive-degree elements u_i. Degree induction shows they generate H;
in particular Q = 0 implies H = k. Induct strongly on dim_k H, starting with
H = k and the empty generating list.
2. Apply lem-sfb-graded-bialgebra-coordinate-derivations to these lifts. In
characteristic zero an even generator of least vanishing exponent N would give
N u_i^(N-1) = 0 after applying its coordinate derivation, a contradiction.
All generators are odd and have square zero. The ordered squarefree products
span by signed commutativity. In a relation choose a nonzero coefficient with
maximal monomial length and apply its coordinate derivatives in reverse order.
Every other term is killed and the selected coefficient survives up to sign.
Thus these products are independent and all heights can be taken to be two.
3. In characteristic p > 0 let B be the image of h ↦ h^p. For p = 2 the
algebra is commutative. For odd p, odd elements have square zero and even
elements are central, so this power map is additive, multiplicative and
p-semilinear. Perfectness makes B a k-subalgebra. Its grading has B^(pn)
equal to the image of H^n and all other degrees zero. Expanding the coproduct
in homogeneous simple tensors and checking their signs shows that it restricts
to B. The counit and coassociativity restrict too. A smallest positive nonzero
degree of H is absent from B, so dim_k B < dim_k H unless H = k.
4. Apply induction to B, obtaining generators v_j and heights M_j. Their
classes form a basis of B_+/B_+^2 by independence of its bounded monomials.
The power map induces a semilinear surjection Q → B_+/B_+^2. Lift v_j to
homogeneous y_j with y_j^p = v_j, and extend their independent classes in Q
by homogeneous kernel classes z_l, degree by degree. For odd p the y_j are even.
5. Express z_l^p in B_+^2 as homogeneous bounded monomials in the v_j of
length at least two. Taking pth roots of coefficients and replacing v_j by
y_j gives a homogeneous c_l in I^2 with c_l^p = z_l^p. For odd z_l in odd
characteristic take c_l = 0. Replace z_l by z_l - c_l. Their classes in Q
are unchanged, z_l^p = 0, and y_j^(p M_j) = 0. Odd z_l also square to zero.
6. Apply lem-sfb-graded-bialgebra-coordinate-derivations to the corrected list.
Its coordinate derivations kill B by the signed Leibniz formula. Residue
monomials, with exponents below p (below two for odd generators in odd
characteristic), span H over B. For a relation choose a term of maximal total
exponent with nonzero B-coefficient, and apply the indicated coordinate
derivatives. They kill the other terms and give the chosen coefficient times
a sign and a product of factorials with arguments below p, all invertible.
Hence the residue monomials are B-linearly independent.
7. Combine this B-basis with the bounded k-basis of B. Unique division of
exponents n = p b + a gives the ordered monomial basis with heights p M_j
on the y_j and the residue heights on the z_l. Each height is at least two
and its corresponding power vanishes. Graded multiplication gives degree
sum_j a_j d_j for each monomial. The empty product is 1.
-/
theorem borel_bialgebra_monomial_basis
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
        TensorProduct.rid k H (TensorProduct.map LinearMap.id ε (Δ x)) = x) :
    ∃ (r : ℕ) (d : Fin r → ℕ) (x : Fin r → H) (N : Fin r → ℕ),
      (∀ j : Fin r, 0 < d j ∧ x j ∈ 𝒜 (d j) ∧ 2 ≤ N j ∧ x j ^ N j = 0) ∧
      ∃ b : Module.Basis ((j : Fin r) → Fin (N j)) k H,
        ∀ a : (j : Fin r) → Fin (N j),
          b a = (List.ofFn fun j : Fin r ↦ x j ^ (a j : ℕ)).prod ∧
            b a ∈ 𝒜 (∑ j : Fin r, (a j : ℕ) * d j) := by
  sorry

end GradedAlgebra
