module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.Module.TransferInstance
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Common kernels of linear functionals under field extension

Source: Stacks Project, Algebra, Tag 00CX (`lemma-tensor-product`), and Fields,
Tag 09FN (`lemma-vector-space-is-free`); the coefficient-basis consequence recorded in
(blueprint: lem-sfb-common-linear-kernel-field-extension).

The second-factor `L`-action on `V ⊗[F] L` is the existing `AddEquiv.module` transport
along `TensorProduct.comm F V L`. The same additive equivalence, upgraded by
`AddEquiv.linearEquiv`, is `L`-linear for that action. Composing it with
`LinearMap.baseChange` and `TensorProduct.AlgebraTensorModule.rid` gives the canonical
extended functional, sending `v ⊗ₜ a` to `u v • a = algebraMap F L (u v) * a`.
-/

@[expose] public section

set_option autoImplicit false

universe uF uL uV uE

open scoped TensorProduct

namespace LinearMap

/-- Common kernels of an arbitrary family of linear functionals commute with field extension.
Source: the agent coefficient-basis consequence of Stacks Project, Algebra, Tag 00CX
(`lemma-tensor-product`), and Fields, Tag 09FN (`lemma-vector-space-is-free`)
(blueprint: lem-sfb-common-linear-kernel-field-extension).

Proof plan:
1. The composite of the transported tensor commutor, scalar extension of `u e`, and the
   tensor right unitor is `L`-linear and sends `v ⊗ₜ a` to `u e v • a`. This is the
   universal-property map of `def-weil-pbc-module-tensor-product`.
2. Choose an `F`-basis `(b i)` of `L` using `lem-weil-pbc-vector-space-free`
   (`Module.Free.of_divisionRing`). The index set need not be finite.
3. Write a tensor as a finite sum of pure tensors, expand the finitely many second
   factors in this basis, and collect terms to get `x = ∑ i ∈ S, v i ⊗ₜ b i` with `S` finite.
4. If every extended functional kills `x`, then for each `e` the relation
   `∑ i ∈ S, u e (v i) • b i = 0` has coefficients in `F`. Basis independence implies
   `u e (v i) = 0` for every `i` and `e`. Thus each `v i` is in the original common kernel,
   and `x = ∑ i ∈ S, b i • (v i ⊗ₜ 1)` is in the asserted `L`-span.
5. Conversely every generator `v ⊗ₜ 1` with all `u e v = 0` is killed by every extended
   functional, so `L`-linearity kills its span. For empty `E`, all conditions are vacuous
   and the same finite expansion spans the whole tensor product. Zero vector spaces,
   empty sums, and infinite-dimensional extensions require no changes.
-/
theorem common_kernel_field_extension
    {F : Type uF} {L : Type uL} [Field F] [Field L] [Algebra F L]
    {V : Type uV} [AddCommGroup V] [Module F V] {E : Type uE}
    (u : E → V →ₗ[F] F) :
    {x : V ⊗[F] L | ∀ e : E,
      TensorProduct.AlgebraTensorModule.rid F L L
        ((u e).baseChange L ((TensorProduct.comm F V L).toAddEquiv.linearEquiv L x)) = 0} =
      (↑(@Submodule.span L (V ⊗[F] L) _ _
        ((TensorProduct.comm F V L).toAddEquiv.module L)
        {x | ∃ v : V, (∀ e : E, u e v = 0) ∧ v ⊗ₜ[F] (1 : L) = x}) :
          Set (V ⊗[F] L)) := by
  sorry

end LinearMap
