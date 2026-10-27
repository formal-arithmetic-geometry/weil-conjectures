module

public import Mathlib.LinearAlgebra.TensorProduct.Graded.Internal
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Data.List.OfFn

import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Nonvanishing of independent primitive products

Source: Milne, Abelian Varieties, I Lemma 12.2, printed p.55; agent-supplied
elementary replacement for the primitive-product ingredient of the Hopf bound.
(blueprint: lem-sfb-graded-primitive-product).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace GradedAlgebra

/-- An ordered product of independent primitive degree-one elements is nonzero.

Source: Milne, Abelian Varieties, I Lemma 12.2, printed p.55; agent-supplied
elementary tensor-coordinate argument replacing only the primitive-product
ingredient of the Borel structure theorem.
(blueprint: lem-sfb-graded-primitive-product).

The coproduct is linear, unital, and multiplicative for Mathlib's signed tensor
product, whose homogeneous multiplication has sign (-1)^(deg b * deg c).
No commutativity, characteristic restriction, finite dimension, counit, or
vanishing of degree-one squares is assumed. The ordered product uses increasing
Fin r order; for r = 0, List.prod is 1.

Proof:
1. Induct on r, uniformly over all independent primitive families. The empty
product is 1, which is nonzero. The prefix of an independent family is
independent by extending each relation with zero coefficients. Thus its
ordered product y is nonzero by induction. Graded multiplication places an
ordered product of r degree-one elements in degree r.
2. Let P be the sum of all degrees other than one and the span of the prefix.
Projection onto degree one shows the last vector is outside P. Apply
lem-sfb-linear-map-extension-prescribed-value (LinearMap.exists_extend_of_notMem)
to the zero map on P, prescribing value 1 at the last vector. The resulting
lambda vanishes outside degree one and on the prefix.
3. Multiplicativity and primitivity expand Delta of the full product as the
sum over subsets S of the ordered factors placed on the right tensor axis.
Each term is (-1)^N(S) times x_(S complement) tensor x_S, with increasing
order on each side and N(S) counting pairs i < j with i in S and j outside S.
Adjoining a right factor adds no crossing; adjoining a left factor contributes
(-1)^card(S). This proves the expansion by induction from 1 tensor 1.
4. By def-weil-pbc-module-tensor-product, the bilinear map
(a,b) maps to lambda(b) times a induces a linear contraction T. It kills terms
with card(S) different from one by degree, and singleton terms in the prefix
by the choice of lambda. Only the last singleton survives, with crossing
number zero. Hence T(Delta(full product)) = y is nonzero. A zero full product
would have zero image, a contradiction. Only 0, 1, and -1 are used, so this
also works in characteristic two and when individual squares do not vanish.
-/
theorem primitive_product_ne_zero
    (k : Type u) [Field k]
    (H : Type v) [Ring H] [Algebra k H] [Nontrivial H]
    (𝒜 : ℕ → Submodule k H) [GradedAlgebra 𝒜]
    (hconnected : 𝒜 0 = Submodule.span k {(1 : H)})
    (Δ : H →ₗ[k] H ⊗[k] H)
    (hdegree : ∀ (n : ℕ) (a : 𝒜 n), Δ a ∈
      Submodule.span k {z | ∃ (p q : ℕ) (b : 𝒜 p) (c : 𝒜 q),
        p + q = n ∧ z = (b : H) ⊗ₜ[k] (c : H)})
    (hunit : Δ 1 = (1 : H) ⊗ₜ[k] (1 : H))
    (hmul : ∀ a b : H,
      GradedTensorProduct.of k 𝒜 𝒜 (Δ (a * b)) =
        GradedTensorProduct.of k 𝒜 𝒜 (Δ a) * GradedTensorProduct.of k 𝒜 𝒜 (Δ b))
    (hcoassoc : ∀ a : H,
      TensorProduct.assoc k H H H (TensorProduct.map Δ LinearMap.id (Δ a)) =
        TensorProduct.map LinearMap.id Δ (Δ a))
    (r : ℕ) (x : Fin r → 𝒜 1)
    (hindependent : LinearIndependent k (fun i : Fin r ↦ (x i : H)))
    (hprimitive : ∀ i : Fin r,
      Δ (x i : H) = (x i : H) ⊗ₜ[k] (1 : H) + (1 : H) ⊗ₜ[k] (x i : H)) :
    (List.ofFn fun i : Fin r ↦ (x i : H)).prod ∈ 𝒜 r ∧
      (List.ofFn fun i : Fin r ↦ (x i : H)).prod ≠ 0 := by
  sorry

end GradedAlgebra
