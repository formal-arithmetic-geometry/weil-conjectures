## Worker report

Item: `lem-trf-reducedness-tensor-alg-equiv`, stage 2, Q02.

The new module `Sheaf.RingTheory.ReducednessTensorAlgEquiv` states
`Algebra.isReduced_tensorProduct_iff_of_bijective`. Its only theorem has proof `sorry`;
there are no definitions or helper theorems. The node is unchanged except for `lean`.
No statement correction, disputed statement, new node, or dependency repair is needed.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base field is `(k : Type u) [Field k]`.
- The commutative k-algebra is `(A : Type v) [CommRing A] [Algebra k A]`.
  Mathlib's `Algebra` includes the structure ring homomorphism; centrality adds no
  condition here because A is commutative.
- The two scalar fields are `(L : Type w) [Field L] [Algebra k L]` and
  `(M : Type z) [Field M] [Algebra k M]`.
- The k-algebra homomorphism is `(e : L →ₐ[k] M)`; preservation of the structure
  map is the `AlgHom.commutes'` field, as required by the dependency definition.
- Bijectivity is the explicit hypothesis `(he : Function.Bijective e)`.
  It is not replaced by an arbitrary equivalence or by an unbundled function.
- The left reducedness clause is `IsReduced (A ⊗[k] L)`; the right clause is
  `IsReduced (A ⊗[k] M)`; `↔` gives exactly both requested implications.
  These are Mathlib's algebra tensor ring structures on the recorded module
  tensor products, not a substitute tensor construction.

Dependencies read and used:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`, read at lines
  170–181 (field docstring and class declaration).
- `def-weil-pbc-algebra-hom-quotient`: the clauses used here are `Algebra`,
  `Mathlib.Algebra.Algebra.Defs:95`, and `AlgHom`,
  `Mathlib.Algebra.Algebra.Hom:30`; their signatures and docstrings were read.
  Quotient algebras and ideal powers are not used by this item.
- `def-weil-pbc-module-tensor-product`: `TensorProduct` and `TensorProduct.tmul`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs:81,107`, and the universal property
  `TensorProduct.lift`, `lift.tmul`, `ext'` in
  `Mathlib.LinearAlgebra.TensorProduct.Basic:123–140` were read. The recorded
  `LinearMap.rTensor` interface in `Mathlib.LinearAlgebra.TensorProduct.Map`
  was also read. The actual statement uses the recorded `TensorProduct`.
- Proof dependency `lem-weil-pbc-algebra-tensor-pushout-universal-property`
  is a Mathlib leaf, with no project module to import. Its recorded
  `Algebra.TensorProduct.instCommRing`, `includeLeft`, `includeRight`, `ext`
  in `Mathlib.RingTheory.TensorProduct.Basic` and `productMap` with its
  equations in `Mathlib.RingTheory.TensorProduct.Maps:810–829` were read.
  The latter module is imported non-publicly for this proof dependency.
- `IsReduced` is the existing class in `Mathlib.Algebra.GroupWithZero.Basic:191`:
  every nilpotent element is zero. Its docstring and full field were read.

Source check: read the local `literature/stacks-project/algebra.tex`, the basic
notions list (Tags 00AT and 00B3), the tensor universal property and quotient
construction (Tag 00CX), and the definition of scalar base change (Tag 05G3).
The tag-to-label mapping was checked in `literature/stacks-project/tags/tags`.
The theorem docstring follows every node proof step: inverse algebra map,
two maps by the tensor universal property, identity composites by pure tensors,
then each nilpotent-transport implication. No proof is supplied at stage 2.

Edge cases checked mathematically before writing:

- The zero algebra A is allowed: no `Nontrivial A` is assumed; both tensor
  products are zero rings and reduced. Mathlib explicitly has reducedness
  for subsingleton structures, so its convention includes this case.
- A may be nonreduced; reducedness is not a hypothesis on A or either tensor.
  The assertion is only that the two tensor rings agree in reducedness.
- Identity automorphisms and nonidentity scalar-field isomorphisms are allowed;
  there is no equality assumption on L and M or on their algebra structures.
- Every characteristic, finite or infinite field, and algebraic or transcendental
  scalar extension is allowed. No perfectness, algebraicity, finite-type,
  flatness, or finite-dimensionality hypothesis has been inserted.
- All four type universes are explicitly and independently bound. No test-object
  quantification or universe equality restricts the fields or algebra.
- Nilpotence with exponent zero causes no discrepancy: in a nonzero ring it
  cannot occur; in the zero ring its element is already zero.

Existing-declaration searches (2026-10-18, prescribed `msearch.py` wrapper):

1. `leanfinder`: "Reducedness of tensor products is invariant under a bijective
   algebra homomorphism between scalar fields" — 8 hits; geometric reducedness
   results, `Algebra.TensorProduct.map_bijective`, and related ingredients;
   none states the item. Read `Algebra.TensorProduct.congr` in
   `Mathlib/RingTheory/TensorProduct/Maps.lean:619`; it constructs an algebra
   equivalence but does not state this reducedness iff.
2. `loogle`: `Algebra.TensorProduct.congr, isReduced_of_injective` — 0 hits.
3. `leansearch`: "An algebra equivalence between scalar fields preserves
   reducedness of tensor products" — 8 hits; `congr_apply`, `congr_trans`,
   `algEquivOfLinearEquivTensorProduct`, geometrically reduced tensor results,
   and other constructions; no exact theorem.
4. `grep` in Mathlib RingTheory:
   `isReduced.*(iff|tensor)|tensor.*isReduced|def congr` — 20 hits; `congr`,
   geometric reducedness criteria, reducedness of tensor products of flat
   algebras, and nilpotent lemmas, but no exact theorem.
5. `rg` on both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
   `/home/ubuntu/weil-newtargets-shared/lean/Sheaf`:
   `isReduced.*tensor|tensor.*isReduced|reducedness_tensor_alg` — results
   concern perfect fields, separability, localization, geometric reducedness,
   or pushouts with extra data; none states invariance under a bijective map.
   `rg` for this item's id in upstream WeilConjectures returned no hit.
6. Searched `dag/lean_names_upstream.json` for tensor/reducedness combinations:
   only the separably-generated and separability-from-tensors declarations;
   neither is this item. Exact candidate name
   `isReduced_tensorProduct_iff_of_bijective` was absent from Mathlib,
   upstream WeilConjectures, local Sheaf, and the upstream declaration index.

Validation: `scompile.py Q02 lem-trf-reducedness-tensor-alg-equiv` compiled the
single delivered file, both sandbox and library forms, cleanly (1.0 and 1.1 s).
No errors or warnings were printed. All theorem proof content is `sorry`.

## Second reading by Q02

Author self-check under the dispatcher's direct-delivery instructions; independent
review is performed by the maintainer, and no sub-agent was started.

Reopened the node and compared the actual file signature against it. `Field k`
matches the base field. `CommRing A` with `Algebra k A` matches the commutative
algebra with its structure homomorphism. Each of L and M retains both its field
and k-algebra structures. `e : L →ₐ[k] M` with `Function.Bijective e` exactly
matches the specified bijective k-algebra homomorphism. The two tensor factors
remain in the node's order, with A on the left, and the iff relates the two
`IsReduced` predicates with no extra conclusion. Four independent universes
cover differently sized fields and algebras. The signature contains no hidden
`let`, file-local notation, private definition, or additional hypothesis.
The theorem docstring records all five proof steps and all named proof
dependencies. Found no mismatch and made no statement change.
