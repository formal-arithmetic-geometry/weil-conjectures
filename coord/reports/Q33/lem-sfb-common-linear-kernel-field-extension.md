## Worker report

Item: `lem-sfb-common-linear-kernel-field-extension`.
Module: `Sheaf.LinearAlgebra.CommonLinearKernelFieldExtension`.
Declaration: `LinearMap.common_kernel_field_extension`.
The sole declaration is a theorem with `sorry`; it states the equality in the node without changing its statement or dependencies. There are no additional definitions, helper theorems, or assumptions. All variables and universes are explicit, and `autoImplicit` is disabled.

Hypothesis and clause correspondence:

- The fields F and L are `{F : Type uF} {L : Type uL} [Field F] [Field L]`; the extension F ⊆ L is `[Algebra F L]`. As recorded by `def-pc-field-extension`, this is the field homomorphism `algebraMap F L`, automatically injective. The universes are independent.
- The arbitrary F-vector space is `{V : Type uV} [AddCommGroup V] [Module F V]`. No finite-dimensionality is imposed.
- The arbitrary index set is `{E : Type uE}` and the family of F-linear forms is `(u : E → V →ₗ[F] F)`. There is no `Finite`, `Fintype`, or `Nonempty` assumption.
- The original common kernel K is expressed directly as the condition `∀ e : E, u e v = 0`; it is not replaced by a different subspace or a chosen object.
- V_L is exactly `V ⊗[F] L`, with the factor order in the node. Its L-action is the existing Mathlib transport `(TensorProduct.comm F V L).toAddEquiv.module L`, explicitly passed to `Submodule.span`. Transport sends `a • x` to the usual first-factor action on the swapped tensor, hence sends `a • (v ⊗ₜ b)` to `v ⊗ₜ (a * b)`. This supplies the specified action without assuming an L-action on V.
- The scalar-extended functional is the composite of the existing L-linear maps `(TensorProduct.comm F V L).toAddEquiv.linearEquiv L`, `(u e).baseChange L`, and `TensorProduct.AlgebraTensorModule.rid F L L`. These maps respectively send `v ⊗ₜ a` to `a ⊗ₜ v`, to `a ⊗ₜ u e v`, and to `u e v • a = algebraMap F L (u e v) * a`. Thus the composite is precisely the node's canonical L-linear map, not an arbitrary map or additional hypothesis. Its pure-tensor formula was checked in a compiler probe by `rfl`; the probe was removed from the delivery.
- The left side is the set of all tensors whose images under those composites vanish for every `e`.
- The right side is the underlying set of `Submodule.span L`, using the explicitly specified second-factor action. Its generating set is exactly `{x | ∃ v : V, (∀ e : E, u e v = 0) ∧ v ⊗ₜ[F] (1 : L) = x}`. This is the node's set of tensors v ⊗ 1 with v in K.
- Set equality states both inclusions with no additional conjunct or missing clause.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs`, including the algebraMap and scalar-action fields, used by `[Algebra F L]`.
- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, used for both fields.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.mk`, `TensorProduct.lift` and its uniqueness, and `LinearMap.rTensor`, read in Mathlib's TensorProduct Defs/Basic/Map modules. The statement uses this exact tensor construction via the public Tower import; scalar extension is the canonical `LinearMap.baseChange` from Tower, built from `AlgebraTensorModule.map`. No tensor construction is copied.
- Proof dependency `lem-weil-pbc-vector-space-free`: `Module.Free.of_divisionRing`, `Mathlib.LinearAlgebra.Basis.VectorSpace`, imported with plain `import` for the basis-existence step of the proof.
- Additional existing interfaces: `TensorProduct.comm` (Basic), `TensorProduct.AlgebraTensorModule.rid` and `LinearMap.baseChange` (Tower), `AddEquiv.module` and `AddEquiv.linearEquiv` (`Mathlib.Algebra.Module.TransferInstance`). Their full declarations and construction formulas were read before use.

Sources checked: Stacks algebra.tex, Tag 00CX (`lemma-tensor-product`), construction, universal property, generation by pure tensors and bilinearity relations; fields.tex, Tag 09FN (`lemma-vector-space-is-free`). The exact theorem is the node's agent coefficient-basis consequence, not represented as a verbatim Stacks theorem. The current latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md` was read for the inherited direct-image context. The full five-step coefficient proof from the node is recorded in the theorem docstring.

Edge cases checked before writing: E empty makes both common-kernel conditions vacuous and the span of all v ⊗ 1 is the whole tensor product by finite expansion. V zero gives the zero tensor space and span. If every u is zero, both sides are the whole tensor space. For L = F the equality reduces to the common kernel itself. Infinite E is allowed because independence is applied separately for each e, while each tensor involves only finitely many coefficients in a basis of L. Infinite-dimensional V and L/F cause no change to the finite expansion. Independent field, vector-space and index universes are supported.

Searches for an exact existing declaration:

- `msearch.py ... leanfinder "The common kernel of an arbitrary family of linear functionals commutes with field extension and is the span of the original common kernel"`: eight hits on dual-span/annihilator and root-pairing kernels. `mem_span_of_iInf_ker_le_ker` assumes a finite family, while `FiniteDimensional.mem_span_of_iInf_ker_le_ker` assumes a finite-dimensional space. Neither is this statement.
- `msearch.py ... loogle '"baseChange", "ker"'`: four hits; the tensor hit is `TensorProduct.AlgebraTensorModule.ker_baseChange_comp_cancelBaseChange_symm`, read at Tower:899. It cancels an already scalar-extended map and does not state the arbitrary-family identity. The other hits concern algebra presentations or differentials.
- `msearch.py ... grep 'iInf.*baseChange|baseChange.*iInf|ker_baseChange|baseChange_ker' LinearAlgebra`: only the above Tower cancellation lemma.
- `msearch.py ... leansearch "The common kernel of any family of linear forms after extending a field is the span over that field of tensors v tensor 1 from the original common kernel"`: eight hits. Besides the two finite dual-span lemmas, the hits include `LinearMap.tensorKerEquiv` and `LinearMap.kerLTensorEquivOfSurjective`. Reading Flat/Equalizer.lean shows these identify the scalar extension of one kernel; they do not assert the arbitrary simultaneous-kernel identity or the needed tensor-to-infinite-product injectivity.
- `rg -n 'common.*[Kk]ernel|[Kk]ernel.*[Ff]ield|iInf.*baseChange|baseChange.*iInf'` on the project's `lean/WeilConjectures` and `lean/Sheaf`: inspected the results (coefficient/operator kernels and geometric kernel discussions); no exact declaration. Narrowing to both LinearAlgebra directories found only unrelated root-datum material. `grep -rn` of this node id in `lean/WeilConjectures` found nothing.
- `rg` of the chosen declaration name in Mathlib, WeilConjectures, Sheaf and `dag/lean_names_upstream.json` found no collision.

Validation: the delivered module compiled cleanly through the prescribed `scompile.py` server wrapper, in sandbox and library modes. No warnings or errors were reported. The earlier probe confirmed that the original tensor additive structure is preserved by `AddEquiv.module`, the explicit span module argument elaborates, and the evaluation on pure tensors is definitionally the required formula. No probes remain in the delivered module.

No node fault or disputed statement was found. Only the item's `lean` field changes. The maintainer supplies the independent review, as required by this dispatcher's direct-delivery brief; no independent second reading is claimed here.

## Second reading by Q33

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
