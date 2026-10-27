module

public import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tensor kernels of the legs of a two-summand presentation

Source: Stacks Project, algebra.tex, Tag 0AUM, proof of
lemma-domination-universally-injective; Tag 00DF, lemma-tensor-product-exact
(blueprint: lem-trf-quotient-pair-tensor-kernel).

The two-summand direct sum is represented by the product module, with its standard
inclusions. Tensoring a quotient presentation remains right exact for every module.
-/

@[expose] public section

universe uR uP uQ uQ' uE uL

open scoped TensorProduct

namespace LinearMap

/-- Tensor coordinates and the kernel of a quotient leg for an arbitrary tensor factor.

Source: Stacks Project, algebra.tex, Tag 0AUM, proof of
lemma-domination-universally-injective, and Tag 00DF, lemma-tensor-product-exact
(blueprint: lem-trf-quotient-pair-tensor-kernel).

Here `Q' × Q` is the two-summand direct sum, `b.prod (-a)` is the relation map
`x ↦ (b x, -a x)`, `inl` and `inr` are the two inclusions, and
`π.comp (inl R Q' Q)` is the first quotient leg. The equivalence `F` and its inverse
are the maps called `F` and `G` in the source statement.

Proof:
1. Tensor distribution over two summands (lem-weil-pbc-tensor-finite-product), or
   `TensorProduct.prodLeft`, gives `F` with the displayed pure-tensor formula.
   Its inverse sends `(s,t)` to the sum of the tensors of the two inclusions:
   checking the two composites on pure tensors proves both inverse identities.
   Pure tensors generate, so the coordinate formula determines `F` uniquely.
2. Evaluate the relation map on `x ⊗ l` to get `(b x ⊗ l, -a x ⊗ l)`;
   tensor generation extends this to every `w`. The inverse formula at `(s,0)`
   and functoriality of tensoring give `π_L (F.symm (s,0)) = j_L s`.
3. Apply tensor right exactness (lem-weil-pbc-tensor-right-exact) to the given
   surjective presentation: `π_L` is onto and its kernel is the image of `δ_L`.
   No flatness or injectivity is used.
4. If `j_L s = 0`, right exactness lifts `F.symm (s,0)` to some `δ_L w`.
   Applying `F` gives `b_L w = s` and `a_L w = 0`. Conversely, if `a_L w = 0`,
   the coordinate formula and invertibility give `δ_L w = F.symm (b_L w,0)`.
   Since `π_L δ_L = 0`, this implies `j_L (b_L w) = 0`. These two inclusions
   prove the submodule equality and the displayed elementwise description. -/
theorem quotient_pair_tensor_kernel
    {R : Type uR} [CommRing R]
    {P : Type uP} [AddCommGroup P] [Module R P]
    {Q : Type uQ} [AddCommGroup Q] [Module R Q]
    {Q' : Type uQ'} [AddCommGroup Q'] [Module R Q']
    {E : Type uE} [AddCommGroup E] [Module R E]
    (a : P →ₗ[R] Q) (b : P →ₗ[R] Q') (π : Q' × Q →ₗ[R] E)
    (hπ : Function.Surjective π) (hker : π.ker = (b.prod (-a)).range)
    (L : Type uL) [AddCommGroup L] [Module R L] :
    ∃! F : (Q' × Q) ⊗[R] L ≃ₗ[R] (Q' ⊗[R] L) × (Q ⊗[R] L),
      (∀ (y : Q') (z : Q) (l : L),
        F ((y, z) ⊗ₜ[R] l) = (y ⊗ₜ[R] l, z ⊗ₜ[R] l)) ∧
      (∀ (s : Q' ⊗[R] L) (t : Q ⊗[R] L),
        F.symm (s, t) = (inl R Q' Q).rTensor L s + (inr R Q' Q).rTensor L t) ∧
      (∀ w : P ⊗[R] L,
        F ((b.prod (-a)).rTensor L w) = (b.rTensor L w, -(a.rTensor L w))) ∧
      (∀ s : Q' ⊗[R] L,
        π.rTensor L (F.symm (s, 0)) = (π.comp (inl R Q' Q)).rTensor L s) ∧
      Function.Surjective (π.rTensor L) ∧
      (π.rTensor L).ker = ((b.prod (-a)).rTensor L).range ∧
      ((π.comp (inl R Q' Q)).rTensor L).ker =
        ((a.rTensor L).ker).map (b.rTensor L) ∧
      (∀ s : Q' ⊗[R] L, (π.comp (inl R Q' Q)).rTensor L s = 0 ↔
        ∃ w : P ⊗[R] L, a.rTensor L w = 0 ∧ b.rTensor L w = s) := by
  sorry

end LinearMap
