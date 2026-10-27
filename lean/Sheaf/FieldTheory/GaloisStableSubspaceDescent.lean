module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Descent of Galois-stable subspaces

Source: Milne, Algebraic Groups (2017), Appendix A.64, printed pp. 580–581;
A.65 applies this linear descent to a defining ideal.
(blueprint: lem-sfb-galois-stable-subspace-descent).

We use Mathlib's scalar-extension convention `L ⊗[k] M`. The canonical factor swap
`TensorProduct.comm k M L` identifies this with the node's `M ⊗[k] L`, carrying the
second-factor `L`-action to the first-factor action. Thus the automorphism acts on
`λ ⊗ m` as `σ(λ) ⊗ m`, the descent subspace is the preimage under `m ↦ 1 ⊗ m`,
and the scalar-extended inclusion sends `λ ⊗ w` to `λ ⊗ (w : M)`.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Submodule

/-- A Galois-stable subspace of a canonically scalar-extended vector space descends,
without finiteness assumptions on the extension or either vector space.

Here `IsGalois k L` means that `L/k` is algebraic, normal and separable.
The stability hypothesis is equality of the underlying `k`-subspaces because the
canonical action is `k`-linear and `σ`-semilinear over `L`. The comap is exactly
`W₀ = {m | 1 ⊗ m ∈ W}`. Its inclusion, extended by `LinearMap.baseChange`, is
injective and has range `W`, hence induces an `L`-linear isomorphism onto `W`.

Source: Milne, Algebraic Groups (2017), Appendix A.64, printed pp. 580–581.
(blueprint: lem-sfb-galois-stable-subspace-descent).

Proof (the node's finite-support argument, rather than Milne's Morita argument):
1. The map `ι(m) = 1 ⊗ m` is `k`-linear, so its preimage `W₀` is a subspace.
   The tensor universal property (def-weil-pbc-module-tensor-product) gives the
   displayed base-changed inclusion `F`. Its image is the `L`-span `N` of `ι(W₀)`:
   pure tensors generate and `F(λ ⊗ w) = λ • ι(w)`. Thus `N ≤ W`.
2. Choose a `k`-basis of `M` (lem-weil-pbc-vector-space-basis-through-vector).
   Its scalar extension is an `L`-basis (def-weil-vector-space-scalar-extension).
   Every vector has finite support in this basis, and applying `σ` applies `σ`
   to every coefficient, preserving support.
3. Given nonzero `x ∈ W`, choose nonzero `u ∈ W` of smallest support contained
   in the support of `x`. Normalize one nonzero coordinate, indexed by `p`, to 1.
   Each `σ(u) - u` lies in `W` with strictly smaller support, so it is zero.
   The coefficients of `u` are fixed by every automorphism and therefore lie in
   `k` (lem-exc-etale-galois-fixed-field-subgroup, with intermediate field `k`).
   Hence `u = ι(m)` for `m ∈ W₀`, so `u ∈ N`.
4. Strong induction on support size now proves `W ≤ N`. The zero vector is in
   `N`. Otherwise take `u` and `p` from step 3 and subtract from `x` its
   `p`-coordinate times `u`. This cancels that coordinate and creates none
   outside the support of `x`; induction applies, and then `x ∈ N`.
5. Choose a basis of `W₀` and extend its image to a basis of `M`, using
   lem-weil-pbc-vector-space-basis-through-vector. Scalar extension preserves
   both bases (def-weil-vector-space-scalar-extension). The images under `F`
   of the first basis are part of the second basis and therefore independent.
   Thus `F` is injective. Its range is `N = W`, giving the claimed isomorphism.
   Every coordinate sum is finite even in infinite dimension or an infinite
   algebraic Galois extension. -/
theorem galois_stable_subspace_descent
    (k : Type u) (L : Type v) (M : Type w)
    [Field k] [Field L] [Algebra k L] [IsGalois k L]
    [AddCommGroup M] [Module k M] (W : Submodule L (L ⊗[k] M))
    (hW : ∀ σ : L ≃ₐ[k] L,
      (W.restrictScalars k).map (σ.toLinearMap.rTensor M) = W.restrictScalars k) :
    Function.Injective
        (LinearMap.baseChange L
          ((W.restrictScalars k).comap (TensorProduct.mk k L M 1)).subtype) ∧
      LinearMap.range
        (LinearMap.baseChange L
          ((W.restrictScalars k).comap (TensorProduct.mk k L M 1)).subtype) = W := by
  sorry

end Submodule
