## Worker report

The module `Sheaf.RingTheory.ConnectedFilteredCoalgebraKernelPrimitive` states
`Coalgebra.exists_primitive_mem_ker_of_not_injective`, with `sorry` as its whole
proof. There are no additional declarations or definitions. The node is unchanged
except for its `lean` record. No statement correction or disputed statement was needed.

The statement matches the node as follows:

- The field is `{k : Type u} [Field k]`. The two vector spaces are `{C : Type v}`
  and `{D : Type w}`, each with `AddCommGroup` and `Module k` instances. The three
  universes are independent and explicitly bound.
- `[Coalgebra k C]` and `[Coalgebra k D]` bundle exactly the linear maps Delta and
  epsilon and their three identities. Mathlib's `CoalgebraStruct.comul` has type
  `E →ₗ[k] E ⊗[k] E` and its `counit` has type `E →ₗ[k] k`. The `coassoc` field
  uses `TensorProduct.assoc` to identify the two triple tensor products. The
  `rTensor_counit_comp_comul` and `lTensor_counit_comp_comul` fields equate the
  respective composites to `y ↦ 1 ⊗ y` and `y ↦ y ⊗ 1`. Applying the unit
  identifications gives the node's two counit identities. Conversely, those
  identities give the fields. Thus bundling adds no restriction to the given maps.
- `(g : C)`, `hg_comul`, and `hg_counit` say respectively that g is fixed,
  `Delta(g)=g tensor g`, and `epsilon(g)=1`.
- `(F : ℕ → Submodule k C)` and `hF_mono : Monotone F` give the increasing
  subspaces. `hF_zero : F 0 = Submodule.span k {g}` is exactly `C_0=kg`.
  `hF_exhaustive : ∀ x : C, ∃ n : ℕ, x ∈ F n` is the exhaustive union condition.
- `hF_comul` bounds the image `(F n).map comul` by the supremum over
  `i ∈ Finset.range (n+1)` of
  `LinearMap.range (TensorProduct.map (F i).subtype (F (n-i)).subtype)`.
  The range is exactly the image of `F i tensor F(n-i)` in `C tensor C`, not an
  abstract tensor subspace or an assumed injective inclusion. The finite supremum
  of submodules is their sum, and the range contains exactly i=0,...,n, so natural
  subtraction is used only for i at most n.
- `(f : C →ₗ[k] D)` is the given linear map. `hf_comul` is
  `Delta_D ∘ f = (f tensor f) ∘ Delta_C`, and `hf_counit` is
  `epsilon_D ∘ f = epsilon_C`. Both are equalities of linear maps.
- `hf : ¬ Function.Injective f` is precisely noninjectivity.
- The existential conclusion is `∃ x : C`, with all four clauses in order:
  `x ≠ 0`, `f x = 0`, `counit x = 0`, and
  `comul x = x ⊗ₜ[k] g + g ⊗ₜ[k] x`.
- No finite-dimensionality, algebra, cocommutativity or characteristic instance
  occurs in the statement. The codomain has no filtration assumption.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`,
  `Mathlib.Algebra.Field.Defs`; the node is a Mathlib leaf, so no project module
  or replacement record is needed. Its definition and docstring were read.
- `def-weil-pbc-module-tensor-product`: `TensorProduct`, `TensorProduct.mk`,
  `TensorProduct.lift`, `TensorProduct.ext'`, `TensorProduct.map`, and
  `LinearMap.rTensor`, in Mathlib's `LinearAlgebra.TensorProduct` Defs, Basic,
  and Map modules. The recorded universal property and tensor-map interfaces were
  read; these are the standard tensor products and maps in the statement.
- Mathlib `Coalgebra` and `CoalgebraStruct`, in
  `Mathlib.RingTheory.Coalgebra.Basic` (public import), supply the exact identities
  stated explicitly in the node. Their full definitions and docstrings were read.
- Proof dependency `lem-sfb-vector-space-tensor-family-zero-detection` is already
  closed upstream as `TensorProduct.eq_zero_of_forall_rTensor_eq_zero` in
  `WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basis` (plain import).
  Its full statement and proof docstring were read. It assumes the right factor
  is free; over a field every vector space is free, as needed for the node's
  singleton-family applications. No additional hypothesis is added to this item.

Source verification: opened the local Milne PDF with `pdftotext -layout`.
Definition 14.4 and equation (91), printed p.281, give the increasing exhaustive
filtration with degree zero k and the tensor sum condition. Lemma 14.43, printed
p.294, gives the stated primitive-element coproduct calculation. As the node
explicitly records, the general kernel lemma is agent-written from these
structures, not a quotation of Lemma 14.44. The theorem docstring reproduces
all four proof steps, including the two tensor zero-detection applications.

Edge cases checked before writing:

- Degree zero has one tensor summand, i=0; no empty range is substituted.
  A kernel element there has form a*g, and counit preservation forces a=0.
- The first nonzero kernel degree is therefore positive. For n=1 the two endpoint
  terms are killed by p tensor p and there are no interior terms, so the same
  proof yields the primitive equation.
- g is automatically nonzero because epsilon(g)=1 over a field; the zero domain
  cannot satisfy the hypotheses. The zero codomain cannot admit the prescribed
  counit-preserving map since evaluation at g would give 0=1. No such cases are
  removed by an artificial nontriviality hypothesis.
- An injective f makes the conditional hypothesis impossible. Arbitrary
  infinite-dimensional spaces, repeated filtration steps, and every field
  characteristic are retained.

Searches for existing statements:

- `msearch.py leanfinder`, query: "A noninjective coalgebra map from an exhaustive
  connected filtered coalgebra over a field has a nonzero primitive element in
  its kernel". Eight results: `IsGroupLikeElem.ne_zero`,
  `Coalgebra.Repr.arbitrary`, `linearIndep_groupLikeVal`,
  `Coalgebra.subsingleton_to_ring`, `Coalgebra.Repr.mk.inj`, `Coalgebra.Repr.ι`,
  `linearIndepOn_isGroupLikeElem`, and `groupCohomology.Hilbert90.aux_ne_zero`.
  None asserts the kernel lemma.
- `msearch.py loogle`, query `"Coalgebra", "injective"`: zero results.
- `msearch.py grep`, query `primitive|coradical|connected|filtered`, subdirectory
  `RingTheory/Coalgebra`: one comment hit in `CoassocSimps.lean`, no theorem.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `connected.filtered|kernel.primitive|coradical`
  and tensor zero detection found only the existing tensor zero-detection helper
  and its consumers. Coalgebra searches found the existing general coalgebra
  and comodule interfaces, not the connected-filtration kernel lemma.
- Searching the exact node id in `lean/WeilConjectures` found no match. Searching
  the proposed full last declaration component in Mathlib, both project roots,
  and the upstream name index found no collision.

Validation: the prescribed `scompile.py` compiled the file as both sandbox and
library module, cleanly, with no errors or unexpected warnings. Every theorem
proof is `sorry`; nothing is proved in this delivery.

## Second reading by NQ

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
