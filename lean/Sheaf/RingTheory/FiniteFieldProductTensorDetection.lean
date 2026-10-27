module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Tensor detection through a finite product of extension fields

Source: Stacks Project, Algebra, Tag 034N,
proof of `lemma-geometrically-reduced-any-reduced-base-change`, last two sentences
(blueprint: lem-trf-finite-field-product-tensor-detection).
-/

@[expose] public section

universe u v w t s

set_option autoImplicit false

open scoped TensorProduct

namespace Algebra

/-- Tensoring an embedding into a finite product of extension fields preserves injectivity
and detects reducedness after scalar extension.

Source: Stacks Project, Algebra, Tag 034N, proof of
`lemma-geometrically-reduced-any-reduced-base-change`, last two sentences
(blueprint: lem-trf-finite-field-product-tensor-detection).

Proof plan:
1. The finite-product tensor equivalence `TensorProduct.piLeft`
   (lem-weil-pbc-tensor-finite-product) has coordinates induced by the projections.
   Its inverse sums the tensors of the coordinate inclusions, which are linear but
   need not preserve the unit. This also works for the empty product.
2. On pure tensors the product formula is `(x tensor a)(y tensor b) = xy tensor ab`,
   and the unit is `1 tensor 1`. The coordinate map preserves both, hence the linear
   equivalence is a unital k-algebra equivalence. The same computation applies to
   the tensor of j with the identity of A (def-weil-pbc-module-tensor-product).
3. Every k-vector space is free, hence flat (lem-weil-pbc-module-over-field-flat).
   Tensor the injective linear map underlying j with A; flat exactness
   (lem-weil-pbc-flat-tensor-exact), using the module quotient P/j(B), preserves
   injectivity. Compose with the equivalence from step 1 to obtain the displayed
   coordinate map from B tensor A (Theta), which is therefore injective.
4. Swap the factors in each coordinate (lem-weil-pbc-module-tensor-comm).
   The swap preserves multiplication and the unit by the pure-tensor formulas.
   A nilpotent z in B tensor A maps under Theta to nilpotents in all K_i tensor A,
   and the swaps send them to zero by reducedness of A tensor K_i. Thus Theta(z)=0,
   and injectivity gives z=0. If I is empty, equality in the empty product gives
   the same conclusion. Zero A or B requires no separate assumption.
-/
theorem finite_field_product_tensor_detection
    (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A]
    (B : Type w) [CommRing B] [Algebra k B]
    (I : Type t) [Finite I] (K : I → Type s) [∀ i, Field (K i)]
    [∀ i, Algebra k (K i)] (j : B →ₐ[k] (∀ i, K i)) (hj : Function.Injective j) :
    (∃ Φ : ((∀ i, K i) ⊗[k] A) ≃ₐ[k] (∀ i, K i ⊗[k] A),
      ∀ (x : ∀ i, K i) (a : A) (i : I), Φ (x ⊗ₜ[k] a) i = x i ⊗ₜ[k] a) ∧
    Function.Injective
      (AlgHom.pi fun i : I ↦
        Algebra.TensorProduct.map ((Pi.evalAlgHom k K i).comp j) (AlgHom.id k A)) ∧
    ((∀ i : I, IsReduced (A ⊗[k] K i)) → IsReduced (B ⊗[k] A)) := by
  sorry

end Algebra
