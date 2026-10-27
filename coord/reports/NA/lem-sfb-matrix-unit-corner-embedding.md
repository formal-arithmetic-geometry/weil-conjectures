## Worker report

The module `Sheaf.LinearAlgebra.MatrixUnitCornerEmbedding` states
`Module.Basis.matrixUnit_corner_embedding`, with its entire proof postponed by `sorry`.
There are no new definitions, helper axioms, dependency modules, or statement corrections.
The existential subspace and image are pinned down by exact carrier equalities, and the
linear map is pinned down by its pure-tensor formula, so they are the objects specified
in the node, rather than extra data assumed of the caller.

Hypotheses and clauses, in node order:

- The field K is `{K : Type u} [Field K]`; the vector space V is `{V : Type v}`,
  `[AddCommGroup V] [Module K V]`.
- The arbitrary algebraic basis and its chosen index are `{J : Type w}`,
  `(b : Module.Basis J K V) (j₀ : J)`. `Basis.repr` has finitely supported coordinates,
  so this is precisely an algebraic basis, without a finite or countable index condition.
- The coordinate function λ_j is `b.coord j`. The matrix unit E_ij is
  `(b.coord j).smulRight (b i)`, which evaluates at v as `(b.coord j v) • b i`.
- The unital K-subalgebra D of endomorphisms is
  `(D : Subalgebra K (Module.End K V))`; multiplication in `Module.End` is composition.
  The hypothesis `(hE : ∀ i j : J, (b.coord j).smulRight (b i) ∈ D)` gives all matrix units.
- H is an arbitrary unital left D-module, `(H : Type x) [AddCommGroup H] [Module D H]`.
  `[Module K H] [IsScalarTower K D H]` expresses the induced K-action. Indeed
  `IsScalarTower.algebraMap_smul` says that action by the scalar operator equals K-scaling;
  conversely the induced module action always has this tower. This is compatibility of
  the specified scalar action, not an additional restriction on H.
- The corner e is the element of D represented by `(b.coord j₀).smulRight (b j₀)`.
  The conclusion `∃ C : Submodule K H, (C : Set H) = Set.range (fun h ↦ e • h) ∧ ...`
  states exactly that eH is a K-subspace with its specified underlying set.
- `∃ hθ : ∀ v : V, (b.coord j₀).smulRight v ∈ D, ...` states membership of every θ_v
  in D. Its witness supplies the subtype membership proof needed in the tensor formula.
- `∃ Φ : V ⊗[K] C →ₗ[K] H, ...` asserts a well-defined K-linear tensor map, and the
  first conjunct is `∀ (v : V) (h : C), Φ (v ⊗ₜ[K] h) = θ_v • (h : H)`.
  Pure tensors generate Mathlib's algebraic tensor product, so this specifies the unique
  intended map; it does not permit an arbitrary injection.
- `Function.Injective Φ` is injectivity. The next conjunct, universally quantified in
  T and z, is `Φ (LinearMap.rTensor C (T : Module.End K V) z) = T • Φ z`.
  `LinearMap.rTensor` is precisely T on the first factor and identity on C.
- `∃ N : Submodule D H, (N : Set H) = Set.range Φ ∧ ...` asserts D-stability of the
  exact image. Its being a D-submodule gives the standard induced D-action on `H ⧸ N`.
- The last two conjuncts state that e kills every `q : H ⧸ N` and that for every j,
  the diagonal matrix unit `(b.coord j).smulRight (b j)` kills every such q.
- The tensor is Mathlib's ordinary `TensorProduct`, and the four independent universes
  cover arbitrary sizes of K, V, J and H. There is no topology or dimension assumption.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs` (available through
  the public imports); its signature and docstring were read.
- `def-weil-pbc-module-tensor-product`: Mathlib `TensorProduct`,
  `Mathlib.LinearAlgebra.TensorProduct.Defs`, and `LinearMap.rTensor`,
  `Mathlib.LinearAlgebra.TensorProduct.Map`. Their actual source definitions were read.
  Tensor universal property and generation are used in the documented proof plan.
- `lem-weil-pbc-module-tensor-hom-currying` (proof dependency):
  `TensorProduct.lift.equiv` and `TensorProduct.ext'`,
  `Mathlib.LinearAlgebra.TensorProduct.Basic`, imported as a proof dependency; full
  signatures and docstrings were read. All three nodes are Mathlib leaves, so there is
  no recorded project dependency to restate or repair.

Also read `Module.Basis.coord`, `LinearMap.smulRight`, and the standard quotient module
instances. No private substitute of these notions is introduced.

Edge cases checked before drafting: zero H and zero eH give the unique zero-domain
injection; singleton J gives the expected full image since e is identity; arbitrary
infinite J still uses only finite expansions; a zero V or empty J cannot coexist with
an algebraic basis and the chosen j₀ over a field. Every field characteristic is allowed.
For D equal to the full endomorphism algebra or to any intermediate unital subalgebra,
the coefficient isolation argument is unchanged. Surjectivity is deliberately not a
conclusion: infinite-rank examples can have nonzero quotients killed by all matrix units.

Searches made using the prescribed msearch wrapper:

- LeanFinder: "For an endomorphism subalgebra containing matrix units the corner tensor
  evaluation map is injective and its quotient is annihilated by the corner". Eight
  hits included `MatrixEquivTensor.left_inv`, `IsAzumaya.bij`, and
  `Algebra.injective_lift_lsmul`; none states this arbitrary-basis corner theorem.
- Loogle: `LinearMap.smulRight, TensorProduct`. No hits.
- Mathlib grep: `matrixUnit|matrix_unit|corner.*tensor|idempotent.*tensor`, in
  `LinearAlgebra`. Only the two unrelated `toMatrix_unitsSMul` occurrences.
- LeanSearch: "Injectivity of a tensor map defined using a rank one idempotent and a
  basis of a vector space". Eight hits about tensoring injective maps, invertible
  modules, and tensor algebras; no exact match.
- Ripgrep of both `lean/WeilConjectures` and `lean/Sheaf` for
  `matrixUnit|matrix_unit|corner.*tensor|corner.*[Ee]mbed` found no matching statement.
  The upstream search for the exact blueprint id found no declaration. DAG searches
  found the item and its reconstruction consumer, with no duplicate theorem node.

Source check: the node explicitly identifies this as an agent-formulated coefficient
auxiliary with the external reference WANTED. I read the current blueprint unit's
paragraph (3); it now uses the geometric direct-image references rather than presenting
this extracted algebra argument. The node's complete seven-step algebraic proof remains
coherent independently and is reproduced in the theorem docstring, including its two
existing tensor-product dependencies. No claim of an external reference was added.
No STATEMENT-DISPUTED flag is needed.

Validation: scompile.py compiled the sandbox and library module individually, in 2.2 s
and 2.6 s respectively, with no compiler errors or warnings.

## Second reading by NA

A separate clause-by-clause reading of the node and finished file checked the corner
carrier, θ membership, pure-tensor formula, injectivity, first-factor equivariance,
D-stable exact image, and both quotient annihilation clauses against the list above.
The existential C and N do not weaken the statement because their carriers are fixed;
the existential Φ is fixed by the formula and algebraic tensor universal property.
The tower specifies exactly the induced scalar action. No additional finiteness,
nontriviality of H, or topology hypothesis was introduced. No mismatch was found and no
correction was necessary. This is a rereading by the same dispatched worker; the prompt
prohibits starting other agents, and the maintainer supplies the independent review.
