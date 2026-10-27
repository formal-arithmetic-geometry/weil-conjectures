module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Nonzero coinvariants for a connected filtered coalgebra

Source: Milne, Algebraic Groups (2017), Definition 14.4, equation (91), printed p.281,
and Theorem 14.5, proof of (c) implies (a), printed pp.281–282.
(blueprint: lem-sfb-filtered-coalgebra-nonzero-coinvariant)

The finite supremum of tensor-image subspaces is their sum. Only the coalgebra
structure is used; no multiplication, antipode or cocommutativity is required.
-/

set_option autoImplicit false

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra

/-- A nonzero right comodule over an exhaustively filtered coalgebra whose degree-zero
piece is spanned by a group-like element has a nonzero coinvariant for that element.
Source: Milne, Algebraic Groups (2017), Definition 14.4, equation (91), printed p.281,
and Theorem 14.5, proof of (c) implies (a), printed pp.281–282.
(blueprint: lem-sfb-filtered-coalgebra-nonzero-coinvariant)

Proof:
1. Put T_r = image(V tensor F_r -> V tensor C) and V_r = c^{-1}(T_r).
   Monotonicity of F makes these increasing. Express c(v) as a finite sum of pure
   tensors by def-weil-pbc-module-tensor-product. Exhaustivity and the maximum of
   the finitely many coefficient degrees give v in V_r for some r; for an empty
   sum use r = 0. Thus the V_r exhaust V.
2. Let q_r : C -> C/F_r and d_r = (1 tensor q_r)c. Tensor right exactness
   (lem-weil-pbc-tensor-right-exact) identifies ker(1 tensor q_r) with T_r.
   Hence ker(d_r) = V_r, and V_r = 0 makes d_r injective.
3. The singleton-family case of lem-sfb-vector-space-tensor-family-zero-detection
   makes d_r tensor 1_{C/F_r} injective. Its composite with d_r is injective.
   Coassociativity identifies this composite with
   (1 tensor q_r tensor q_r)(1 tensor Delta)c, under the tensor associator.
   On V_{r+1} the filtration puts its value in the sum of images of
   V tensor F_i tensor F_{r+1-i}. Either i <= r or r+1-i <= r, so one quotient
   factor kills each summand. Injectivity gives V_{r+1} = 0 when V_r = 0.
4. If V_0 = 0, induction using step 3 gives V_r = 0 for every r. Exhaustivity
   then gives V = 0, a contradiction. Choose a nonzero v in V_0.
5. Since F_0 = k g, combine pure tensors to write c(v) = z tensor g.
   Apply the comodule counit identity and epsilon(g) = 1 to get v = z.
   Thus c(v) = v tensor g, as required. -/
theorem exists_nonzero_coinvariant_of_filtration
    {k : Type u} [Field k] {C : Type v} [AddCommGroup C] [Module k C]
    [Coalgebra k C] (g : C) (hg : IsGroupLikeElem k g)
    (F : ℕ → Submodule k C) (hmono : Monotone F)
    (hzero : F 0 = Submodule.span k {g})
    (hexhaustive : ∀ x : C, ∃ r : ℕ, x ∈ F r)
    (hcomul : ∀ r : ℕ,
      Submodule.map (Coalgebra.comul (R := k) (A := C)) (F r) ≤
        ⨆ i ≤ r, LinearMap.range (TensorProduct.map (F i).subtype (F (r - i)).subtype))
    {V : Type w} [AddCommGroup V] [Module k V] [Nontrivial V]
    (c : V →ₗ[k] V ⊗[k] C)
    (hcoassoc : (TensorProduct.assoc k V C C).toLinearMap ∘ₗ c.rTensor C ∘ₗ c =
      (Coalgebra.comul (R := k) (A := C)).lTensor V ∘ₗ c)
    (hcounit : (TensorProduct.rid k V).toLinearMap ∘ₗ
      (Coalgebra.counit (R := k) (A := C)).lTensor V ∘ₗ c = LinearMap.id) :
    ∃ x : V, x ≠ 0 ∧ c x = x ⊗ₜ[k] g := by
  sorry

end Coalgebra
