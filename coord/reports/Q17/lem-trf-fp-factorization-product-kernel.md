## Worker report

The module `Sheaf.RingTheory.FpFactorizationProductKernel` states
`LinearMap.rTensor_eq_zero_of_fp_factorization_product_kernel`. Its only proof is
`sorry`; it introduces no definition or auxiliary theorem. The existing node statement
is unchanged. Source read: `literature/stacks-project/algebra.tex`, Tag 059M
(`proposition-ML-tensor`), proof (1) implies (2), especially the three-row comparison
diagram, and Tag 059K (`proposition-fp-tensor`), proof (1) implies (2). The current
blueprint ancestor `lem-trf-local-term-locality` and its proof were also read; this is
an algebraic supporting lemma, not that blueprint lemma's own statement.

Hypotheses and clauses, in order:

- The commutative ring is `(R : Type u) [CommRing R]`.
- The three modules are `P : Type v`, `Q : Type w`, and `T : Type x`, each with
  explicit `AddCommGroup` and `Module R` instances. Their universes are independent.
- The maps are `a : P →ₗ[R] Q`, `b : P →ₗ[R] T`, and `c : Q →ₗ[R] T`.
  The equation `b = c ∘ a` is exactly `hfactor : b = c.comp a`.
- Finite presentation of Q is `[Module.FinitePresentation R Q]`. No finite-generation,
  finite-presentation, or flatness hypothesis is placed on P or T.
- Universal tensor-kernel inclusion is `hker : ∀ (L : Type (max u v w x t))
  [AddCommGroup L] [Module R L], LinearMap.ker (b.rTensor L) ≤
  LinearMap.ker (a.rTensor L)`. Submodule order is inclusion, in the stated direction.
- The arbitrary index set is `(A : Type y)`; its universe is independent and it has
  no `Finite`, `Fintype`, `Nonempty`, or decidable-equality requirement.
- The family is `(L : A → Type (max u v w x t))` with componentwise additive-group
  and R-module instances. The product V is written explicitly as `∀ i : A, L i`.
  The arbitrary common upper universe includes R, P, Q, T and the freely varying t;
  it avoids a potentially too-small test universe. Smaller presentations of modules
  are represented by their canonical universe lifts, with tensor and product maps
  transported by the associated linear equivalences. No equality between object
  universes or bound on the index universe is imposed.
- The node's canonical theta is exactly Mathlib's `TensorProduct.piRightHom R R T L`.
  Its source definition and `piRightHom_tmul` were read: a pure tensor is sent to
  the family of its coordinate pure tensors. No replacement map or extra assumption
  about theta is used.
- The element is `z : P ⊗[R] (∀ i : A, L i)` and its zero-comparison condition is
  `hz : TensorProduct.piRightHom R R T L (b.rTensor (∀ i : A, L i) z) = 0`.
- Both conclusions are present, joined by `∧`: first
  `a.rTensor (∀ i : A, L i) z = 0`, then `b.rTensor (∀ i : A, L i) z = 0`.
  Here `LinearMap.rTensor` is exactly tensoring the named map with the identity
  of the product, as the tensor-product dependency specifies.

Dependency declarations read and used:

- `def-sc-finitely-presented-module`: `Mathlib.Algebra.Module.FinitePresentation`,
  `Module.FinitePresentation`. The class's finite generators and finite relations
  agree with the node's finite free presentation (`exists_fin'` was read too).
- `def-weil-pbc-module-tensor-product`: its `mathlib_match` is usable directly,
  even without a `lean` field. The modules
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, and `.Map` provide
  `TensorProduct`, `TensorProduct.mk`, `TensorProduct.lift`, `TensorProduct.ext'`,
  and `LinearMap.rTensor` (with its pure-tensor and composition rules).
  They are exposed through the public import of `.Pi`; no duplicate is supplied.
- The canonical comparison is `TensorProduct.piRightHom` from
  `Mathlib.LinearAlgebra.TensorProduct.Pi`, publicly imported.
- Proof-only dependency `lem-trf-finite-presentation-tensor-products` is imported
  privately as `Sheaf.RingTheory.FinitePresentationTensorProducts`; its declaration
  is `TensorProduct.piRightHom_bijective_of_finitePresentation`. Its entire
  signature and proof docstring were read. It applies to Q and the same arbitrary
  family, including an empty index type. The statement dependencies are public;
  the sole additional proof dependency is a plain import.

Edge cases checked before writing: an empty A gives the zero product module and
zero tensors, so both conclusions hold without selecting an index. Infinite A
uses the arbitrary-product comparison, not Mathlib's finite-index equivalence.
For Q = 0, a and hence b are zero. For b = 0, the kernel inclusion forces all
of a's tensor maps to vanish, consistent with the conclusion. The zero ring is
allowed and all its unital modules are zero. Non-flat factors (for example Z/2
as a Z-module) are allowed. No injectivity of b or c is assumed or inferred.

Searches for reuse (all run using the prescribed msearch wrapper where named):

- LeanFinder: `A tensor product to product comparison has kernel disjoint from
  the image of a map factoring through a finitely presented module with
  universally contained tensor kernels`. Eight hits, including
  `TensorProduct.map_ker`, `LinearMap.tensorKerEquiv`, `rTensor_mkQ`, and
  `LinearMap.kerLTensorEquivOfSurjective`. These concern exact sequences or
  flat-module tensor kernels and do not state this factorization/product assertion.
- Loogle: `TensorProduct.piRightHom, LinearMap.ker`: zero hits.
- LeanSearch: `Tensor to product comparison vanishes on the image of a linear
  map factoring through a finitely presented module only if the image is zero,
  assuming universal tensor kernel inclusion`. Eight hits, including tensor
  trivial-vanishing criteria, `TensorProduct.map_ker`, and flatness-dependent
  kernel equivalences. No exact statement.
- Mathlib grep: `piRightHom|factorization.*kernel|kernel.*factorization`, restricted
  to LinearAlgebra: five hits, all the canonical comparison's source/documentation
  in `TensorProduct/Pi.lean`. `piRightHom` constructs the needed map; it does not
  assert this lemma. `piRight` additionally requires a finite index and is not used.
- Project rg: `piRightHom|factorization_product_kernel|factorization.*[Kk]ernel|
  [Kk]ernel.*factorization` in `lean/WeilConjectures` and the RingTheory modules;
  full `lean/Sheaf` search for `piRightHom|fp_factorization_product_kernel`;
  source search for the item's exact DAG id; name-index search in
  `dag/lean_names_upstream.json`. No copy of this theorem. The relevant matches
  are the finite-presentation comparison theorem, the definition of Mittag-Leffler
  modules, and its completion application. Unrelated kernel factorizations and
  finite-complex Kunneth comparisons have different objects and hypotheses.

No statement correction, disputed statement, new node, or dependency repair is needed.

## Second reading by Q17

Reopened the node statement and the completed module for a separate clause-by-clause
self-check; independent review is performed by the maintainer under this assignment.
The ring/module instances, the three maps, factorization equation, Q's finite
presentation, and the universal kernel inclusion all match. In particular the kernel
inclusion points from b to a, and `rTensor` puts the identity on the right.
The family is a product of modules, not a direct sum. The comparison hypothesis
uses T, while the proof uses finite presentation only for Q. The conclusion records
both zero assertions in the node's order. The index type permits empty and infinite
families, with no flatness on any module. Explicit universes and binders were checked;
the common upper test universe avoids vacuity and the index universe remains free.
The proof docstring gives all four DAG steps with their dependencies. No mismatch
was found and no node correction was made.

Validation: compiled the delivered file using the prescribed `scompile.py`; only
the expected declaration-uses-sorry warning is permitted. The dry-run and final
delivery use `deliver2.py`, whose preflight and compilation results are recorded
by the delivery tool.
