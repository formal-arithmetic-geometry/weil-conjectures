module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import Mathlib.GroupTheory.Finiteness

/-! # Regular two-cocycles of diagonalizable groups

Source: Conrad, Reductive group schemes, Appendix B.2, printed pp.283--285,
Lemma B.2.3 and Remark B.2.4 (blueprint: lem-sfb-diagonalizable-regular-two-cocycle).

The coordinate Hopf algebra is that of `AlgebraicGeometry.ringDiagonalizableGroup`.
We write the regular cochain identities on universal points directly as tensor-map identities.
Tensor products associate to the left, so the displayed associators flatten a comultiplication
back into the ordered list of cochain variables. The four terms in the hypothesis are
`h • c(k,l)`, `c(hk,l)`, `c(h,kl)`, and `c(h,k)`, respectively.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct AddMonoidAlgebra

namespace AlgebraicGeometry

/-- Every regular two-cocycle of a diagonalizable group is a regular coboundary.
Source: Conrad, Reductive group schemes, Appendix B.2, printed pp.283--285,
Lemma B.2.3 and Remark B.2.4 (blueprint: lem-sfb-diagonalizable-regular-two-cocycle).

Here `R[M]` is the coordinate Hopf algebra of `ringDiagonalizableGroup R M`;
its comultiplication sends `e_m` to `e_m ⊗ e_m` and its counit sends `e_m` to `1`.
The two identities on `τ` express coassociativity and counitality. Evaluation of the last
factor by an algebra map `R[M] →ₐ[R] T` gives the action on `E ⊗[R] T`.
On a pure tensor, evaluation of a cochain multiplies the values of its coordinate factors.
Thus the hypothesis is the cocycle identity on the universal triple and the conclusion
is the coboundary identity on the universal pair, rather than an identity only on R-points.
No flatness, projectivity, or finiteness assumption is made on `E`.

Proof (the four steps of the DAG node):
1. Using the group-algebra basis of def-sfb-ring-diagonalizable-group, let λ be the
coefficient of `e_0`. Then λ(1) = 1 and `(1 ⊗ λ) Δ(f) = λ(f) 1`, checked on each `e_m`.
Tensor maps exist by def-weil-pbc-module-tensor-product.
2. Set `b = (1_E ⊗ 1_B ⊗ λ)(c)`. The four terms on `x ⊗ a ⊗ f` are respectively
`τ(x) ⊗ a ⊗ f`, `x ⊗ Δ(a) ⊗ f`, `x ⊗ a ⊗ Δ(f)`, and `x ⊗ a ⊗ f ⊗ 1`.
3. Apply `1_E ⊗ 1_B ⊗ 1_B ⊗ λ` to the cocycle identity. On these four terms this
produces `h • b(k)`, `b(hk)`, `b(h)`, and `c(h,k)`. The third computation uses the
invariance of λ and the fourth uses λ(1) = 1. Pure tensors generate, so the computations
hold on every cochain by linearity, as in def-weil-pbc-module-tensor-product.
4. Rearranging the resulting equality yields the displayed coboundary formula.
There is no division or use of exactness of tensoring, including when `M` has torsion. -/
theorem diagonalizable_regular_two_cocycle
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [AddGroup.FG M]
    (E : Type w) [AddCommGroup E] [Module R E]
    (τ : E →ₗ[R] E ⊗[R] R[M])
    (hcoassoc : (TensorProduct.assoc R E R[M] R[M]).toLinearMap
        ∘ₗ τ.rTensor R[M] ∘ₗ τ =
      (Coalgebra.comul (R := R) (A := R[M])).lTensor E ∘ₗ τ)
    (hcounit : (TensorProduct.rid R E).toLinearMap
        ∘ₗ (Coalgebra.counit (R := R) (A := R[M])).lTensor E ∘ₗ τ = LinearMap.id)
    (c : E ⊗[R] R[M] ⊗[R] R[M])
    (hc : ((τ.rTensor R[M]).rTensor R[M]) c -
        (((TensorProduct.assoc R E R[M] R[M]).symm.toLinearMap ∘ₗ
          (Coalgebra.comul (R := R) (A := R[M])).lTensor E).rTensor R[M]) c +
        (TensorProduct.assoc R (E ⊗[R] R[M]) R[M] R[M]).symm
          ((Coalgebra.comul (R := R) (A := R[M])).lTensor (E ⊗[R] R[M]) c) -
        (TensorProduct.mk R (E ⊗[R] R[M] ⊗[R] R[M]) R[M]).flip 1 c = 0) :
    ∃ b : E ⊗[R] R[M],
      c = τ.rTensor R[M] b -
        (TensorProduct.assoc R E R[M] R[M]).symm
          ((Coalgebra.comul (R := R) (A := R[M])).lTensor E b) +
        (TensorProduct.mk R (E ⊗[R] R[M]) R[M]).flip 1 b := by
  sorry

end AlgebraicGeometry
