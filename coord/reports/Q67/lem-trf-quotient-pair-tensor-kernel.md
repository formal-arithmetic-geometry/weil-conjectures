## Worker report

The module `Sheaf.LinearAlgebra.TensorProduct.QuotientPairKernel` states
`LinearMap.quotient_pair_tensor_kernel`, with one `sorry` and no new definitions.
The node is unchanged except for its `lean` field. No dependency interface repair,
new node, or statement correction is needed.

The source read was `literature/stacks-project/algebra.tex`,
`lemma-domination-universally-injective` (Tag 0AUM), especially its description
of the quotient of `M' ⊕ N` by the pairs `(g(x), -f(x))` and its tensor-kernel
sequence; also `lemma-tensor-product-exact` (Tag 00DF). The module docstring
contains all four proof steps of the node: tensor distribution and uniqueness,
the coordinate identities, right exactness, and both kernel inclusions.

### Hypothesis and clause correspondence

| Node text | Lean rendering |
| --- | --- |
| A commutative ring R | `{R : Type uR} [CommRing R]` |
| R-modules P, Q, Q', E, L | Each has its own explicitly bound universe, `AddCommGroup`, and `Module R` instances. L is an arbitrary final parameter. |
| Linear maps a:P→Q and b:P→Q' | `(a : P →ₗ[R] Q) (b : P →ₗ[R] Q')` |
| D=Q'⊕Q with componentwise operations | `Q' × Q`, the standard binary direct sum, exactly the identification made in the node's first proof step. For two entries every family has finite support; this represents the same module as the recorded `DirectSum` construction. No alternative direct-sum definition is introduced. |
| δ(x)=(b(x),−a(x)) | Mathlib's `b.prod (-a)`; `LinearMap.prod` is componentwise, and negation is pointwise. |
| A linear surjection π:D→E | `(π : Q' × Q →ₗ[R] E)` and `(hπ : Function.Surjective π)` |
| ker π=im δ | `(hker : π.ker = (b.prod (-a)).range)` |
| ι₁(y)=(y,0), ι₂(z)=(0,z) | Mathlib's `LinearMap.inl R Q' Q` and `LinearMap.inr R Q' Q`, with precisely these formulas. |
| j=πι₁ | `π.comp (inl R Q' Q)` |
| h_L=h⊗id_L | Mathlib's `h.rTensor L`, in all occurrences. |
| Mutually inverse linear maps F and G | `∃! F : (Q' × Q) ⊗[R] L ≃ₗ[R] (Q' ⊗[R] L) × (Q ⊗[R] L), ...`; G is `F.symm`. The linear-equivalence structure includes linearity of both maps and both inverse identities. |
| F((y,z)⊗l)=(y⊗l,z⊗l) | The first conjunct, quantified over `y`, `z`, and `l`. |
| G(s,t)=(ι₁)_L(s)+(ι₂)_L(t) | The second conjunct, quantified over arbitrary tensors `s` and `t`, including tensors which are not pure. |
| Characterization of the maps | The pure-tensor formula fixes F on generators; the inverse is then fixed. `∃!` records the uniqueness explicitly mentioned in the node's proof. |
| Fδ_L(w)=(b_L(w),−a_L(w)) | The third conjunct, quantified over all `w : P ⊗[R] L`. |
| π_LG(s,0)=j_L(s) | The fourth conjunct. |
| π_L is surjective | `Function.Surjective (π.rTensor L)` |
| ker π_L=im δ_L | `(π.rTensor L).ker = ((b.prod (-a)).rTensor L).range` |
| ker j_L=b_L(ker a_L) | `((π.comp (inl R Q' Q)).rTensor L).ker = ((a.rTensor L).ker).map (b.rTensor L)`; `Submodule.map` is the image of that kernel under b_L. |
| The displayed set {b_L(w): a_L(w)=0} | The final conjunct: for each `s`, `j_L s = 0 ↔ ∃ w, a_L w = 0 ∧ b_L w = s`. This is its elementwise membership description. |
| Arbitrary L, without flatness or injectivity hypotheses | No flatness, nontriviality, or injectivity parameter occurs. All six universes are independent. |

### Dependency declarations and imports

Both statement dependencies are Mathlib leaves; neither needs a `lean` record.
Their full recorded declarations and source docstrings/signatures were read.

- `def-weil-pbc-direct-sum-modules`: `DirectSum` and its additive structure in
  `Mathlib.Algebra.DirectSum.Basic`, and `DirectSum.instModule`, `DirectSum.lof`,
  `DirectSum.component`, and `DirectSum.induction_on` in the Basic/Module files.
  The finite two-summand presentation uses its ordinary product realization,
  as explicitly specified in proof step 1, through `LinearMap.prod`, `inl`, and
  `inr` from `Mathlib.LinearAlgebra.Prod`. It supports differently sized Q and Q'.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and `TensorProduct.mk`
  from `Mathlib.LinearAlgebra.TensorProduct.Defs`; `TensorProduct.lift`,
  `lift.tmul`, and `ext'` from Basic; `LinearMap.rTensor`, `rTensor_tmul`,
  `rTensor_comp`, and `rTensorHom` from Map. These are supplied publicly through
  `Mathlib.LinearAlgebra.TensorProduct.Prod`; the statement directly uses
  `TensorProduct` and `LinearMap.rTensor`.
- Proof dependency `lem-weil-pbc-tensor-finite-product` records
  `TensorProduct.piLeft` in `Mathlib.LinearAlgebra.TensorProduct.Pi`, imported
  without `public`. The binary version `TensorProduct.prodLeft` from Prod
  gives the concrete witness and its pure-tensor normalization.
- Proof dependency `lem-weil-pbc-tensor-right-exact` records `rTensor_exact`
  and `lTensor_exact` in `Mathlib.LinearAlgebra.TensorProduct.RightExactness`;
  that file is imported without `public`. Together with
  `LinearMap.rTensor_surjective` these give the two right-exactness clauses.

### Edge cases

Read against the statement before writing, then checked again against the file:

- L=0: every tensor product is zero, so all formulas, surjectivity, and both
  kernel descriptions remain valid.
- P=0: δ=0 and the given quotient map is bijective. Tensoring the isomorphism
  preserves that property, and the first tensor leg is injective, as predicted.
- Q=0: ker a_L is all of P⊗L; the identity reduces to the usual cokernel
  presentation for b_L. Q'=0 gives the corresponding zero first-leg identity.
- E=0: the hypothesis says δ is onto; after tensoring, lifts of `(s,0)` give
  the asserted restricted image, so the theorem still covers this case.
- a=b=0 and noninjective δ are permitted: the kernel equality forces π to be
  an isomorphism, while the final restricted image is zero.
- A zero ring is allowed: `CommRing` has no nontriviality assumption.
- Nonflat L, for example a torsion module over the integers, is allowed.
  Crucially the kernel in the image formula is `ker (a.rTensor L)`, not
  `(ker a) ⊗ L`; confusing these would incorrectly require flatness.
- Independent universes are bound for R and each of the five modules;
  the product model does not force the two summands into a common universe.

No mathematical fault or disputed statement was found.

### Searches for an existing statement

All service searches used the prescribed
`/home/ubuntu/weil-launcher-all/batch2/msearch.py Q67 lem-trf-quotient-pair-tensor-kernel`.
The wrapper recorded the returned search data in sandbox `searches.jsonl`.

- LeanFinder query: “For a presentation P to Qprime direct sum Q to E with
  relation map (b,-a), tensoring by any L gives kernel of the first leg equal
  to b tensor id applied to kernel of a tensor id”. Eight hits, notably
  `TensorProduct.map_ker` and `LinearMap.tensorKerEquiv`; these give tensor
  kernels or presentations, but not this two-summand restricted-image identity.
- Loogle query: `LinearMap.ker, LinearMap.prod`. Three hits:
  `LinearMap.ker_prod`, `LinearMap.range_prod_eq`, and
  `LinearMap.coe_equivProdOfSurjectiveOfIsCompl`. None states the result.
- Mathlib grep query: `rTensor_exact|prodLeft|map_ker`, restricted to
  `LinearAlgebra/TensorProduct`. Twelve hits including `prodLeft`,
  `prodLeft_tmul`, `rTensor_exact`, and related ingredients, not the full result.
- LeanSearch query: “kernel of first leg of a two-summand module presentation
  after tensoring equals image of tensor kernel of the other leg”. Eight hits
  concerning flat tensor kernels and general tensor-map kernels; no exact match.
- Source and `lean/Sheaf` rg searches for
  `quotient_pair_tensor_kernel|quotientPairTensorKernel|lem-trf-quotient-pair-tensor-kernel`
  returned no match. The names index `dag/lean_names_upstream.json` was included.
- Concept rg searches in `lean/WeilConjectures`, `lean/Sheaf`, and Mathlib's
  LinearAlgebra directory for quotient/tensor/kernel combinations and kernels
  of `rTensor` of `prod`/`inl` returned unrelated quotient/kernel statements.
  A narrower pair/tensor search in their LinearAlgebra and RingTheory directories
  likewise found only unrelated Tor/cotangent declarations.
- The prescribed `grep -rn 'lem-trf-quotient-pair-tensor-kernel'
  lean/WeilConjectures` found no declaration attached to this item.

### Validation

`scompile.py Q67 lem-trf-quotient-pair-tensor-kernel` compiled the delivered
module against the server library in both sandbox and final module names,
with exit code 0 and no errors or warnings (4.1 s and 1.1 s). The file starts
with `module`, uses public statement imports and private proof imports, has
explicit universes and variables, and is at most 100 characters per line.
No proofs or helper declarations were added.

## Second reading by Q67

A separate second pass by this dispatcher worker reread the node and the final
module side by side; the maintainer supplies the independent review as requested
by the assignment. No additional agent was started.

I checked the summand order Q' then Q, the minus sign on a, the orientation of
composition in j, and that tensoring is on the right throughout. The canonical
product realization is explicitly the first identification in the node's proof,
so it changes neither the direct-sum objects nor the inclusions. I checked that
`F.symm` supplies both inverse identities, and that the inverse formula and
coordinate identities quantify over all tensors. The exactness equality has
kernel on the left and range on the right. The last submodule is the image of
the kernel of the tensor map a_L, and the final existential is its precise set
membership description. No flatness or injectivity assumption has slipped in.
All hypotheses and clauses match; no change was needed on this pass.
