## Worker report

The module `Sheaf.LinearAlgebra.AutomorphismFlagFiniteCoefficients` states
`LinearEquiv.exists_flag_finite_coefficients`, with the single expected `sorry`.
It constructs no new notions and leaves the DAG statement unchanged.

Hypotheses and clauses, matched against the node:

- `K : Type u`, `Ω : Type v`, their `Field` instances, `Algebra K Ω`, and
  `IsAlgClosure K Ω` give the field and its specified algebraic closure. This
  allows any algebraic closure, not just Mathlib's chosen `AlgebraicClosure K`.
- `E₀ : IntermediateField K Ω` and `[FiniteDimensional K E₀]` give the finite
  starting coefficient field. `V₀ : Type w`, its additive group and module
  instances, and `[FiniteDimensional E₀ V₀]` give precisely the original vector
  space. `c : Module.Basis (Fin d) E₀ V₀` is the specified ordered basis and
  `F₀ : V₀ ≃ₗ[E₀] V₀` is the automorphism. Universes u, v, w are independent.
- `E : IntermediateField E₀ Ω` and `FiniteDimensional E₀ E` give the common
  finite extension containing E₀ inside Ω; its finiteness over K follows by
  transitivity from the two displayed finite-extension hypotheses. The nested
  intermediate-field encoding is the usual subfield of Ω containing E₀.
- The scalar-extension convention recorded by the dependency uses
  `E ⊗[E₀] V₀`, reversing the informal factors by tensor commutation.
  `F₀.baseChange E₀ E V₀ V₀` is exactly F_E; `.symm` is its inverse, not an
  arbitrary independent operator. The Ω occurrences similarly give F.
- `b` is an E-basis of that tensor product; `α : Fin d → Eˣ` supplies every
  nonzero quotient scalar. `b.flag j` is Mathlib's initial-span flag, with
  indices `Fin (d+1)`. Its definition is the span of b_i for i < j; its zero
  and last members are bottom and top (`flag_zero`, `flag_last`), including
  d=0. The explicit `Module.finrank E (b.flag j) = j.val` gives each dimension.
- The basis `a` of each flag member is indexed by its initial segment and its
  coerced vectors are exactly the corresponding b_i. Thus every adapted
  subspace basis is specified over E, not merely an abstract isomorphic space.
- The matrices B and B⁻¹ are `(c.baseChange E).toMatrix b` and
  `b.toMatrix (c.baseChange E)`; both product identities are explicit. Their
  entries, and the entries of `LinearMap.toMatrix b b F_E.toLinearMap` and
  its inverse analogue, belong to E by type. Both operator matrices are
  explicitly `IsUpperTriangular`.
- The equivalences `r j` on every flag member have forward and inverse
  equations with the ambient F_E and F_E⁻¹ after subtype inclusion. These
  equations express both invariances and identify their mutually inverse
  restrictions, including both endpoints.
- The successive quotient is
  `(b.flag j.succ) ⧸ ((b.flag j.castSucc).comap (b.flag j.succ).subtype)`.
  This is W[j+1]/W[j], with the smaller subspace viewed inside the larger.
  `q j` is an E-linear equivalence from this quotient to E, normalized by
  `q j (mkQ x) = b.repr x j`. Its inverse image of 1 is the quotient adapted
  basis vector, the class of b_j. This expresses the actual quotient basis.
- `g j` is a quotient automorphism. Its forward and inverse equations with
  `mkQ (r j.succ x)` and `mkQ ((r j.succ).symm x)` identify the two induced
  mutually inverse quotient operators. `q j (g j x) = (α j : E) * q j x`
  gives precisely scalar multiplication by α_j on the quotient.
- The maps of each displayed sequence are the canonical E-linear
  `Submodule.inclusion (b.flag_mono ...)` and `Submodule.mkQ`. Their
  injectivity, `Function.Exact`, and surjectivity are all explicit. These
  maps, subspace bases, and quotient bases are therefore defined over E.
- The canonical maps themselves are also extended by `LinearMap.baseChange Ω`;
  injectivity, exactness, and surjectivity of those extended maps are explicit,
  so preservation of each displayed short exact sequence is stated directly.
- `bΩ = (b.baseChange Ω).map (cancelBaseChange E₀ E Ω Ω V₀)` transports the
  actual extended basis through the canonical tensor tower equivalence to V.
  The equality for `bΩ.flag j` identifies it with the image of the extended
  E-flag under that same equivalence. The full specification over Ω repeats
  the dimensions, adapted subspace and quotient bases, both triangular operator
  matrices, inverse restrictions and inverse quotient operators, canonical
  exact sequences, and scalar action by `algebraMap E Ω (α j : E)`.
  These scalars are nonzero because α_j is a unit and the inclusion is a field
  homomorphism. Thus the Ω flag is explicitly the extension of the E data.

Dependency declarations read and used:

- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`;
  `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, `IsAlgClosure`.
  The theorem uses the latter predicate to allow every algebraic closure.
- `Sheaf.FieldTheory.FieldTower`: `FieldExtension.degree`; its module docstring
  explicitly assigns the finite-extension clause to `Module.Finite`, which
  is Mathlib's `FiniteDimensional` abbreviation over fields. No duplicate
  finite-extension predicate is introduced.
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`: `FiniteDimensional`;
  `Mathlib.LinearAlgebra.Dimension.Finrank`: `Module.finrank`.
- `Mathlib.LinearAlgebra.TensorProduct.Basic`: `TensorProduct`;
  `...TensorProduct.Tower`: `LinearMap.baseChange`, `LinearEquiv.baseChange`,
  `Submodule.baseChange`, `TensorProduct.AlgebraTensorModule.cancelBaseChange`;
  `...TensorProduct.Basis`: `Module.Basis.baseChange`.
- Additional standard interfaces are `Module.Basis.flag` in
  `Mathlib.LinearAlgebra.Basis.Flag`, `Submodule.inclusion`, `Submodule.mkQ`,
  `Module.Basis.toMatrix`, and `LinearMap.toMatrix`.
- Proof dependencies are imported without `public`: the recorded
  `Module.End.exists_le_map_le_finrank_eq_succ` and its full-flag corollary in
  `WeilConjectures.Mathlib.LinearAlgebra.Eigenspace.Triangularizable`;
  `LinearMap.finrank_range_add_finrank_ker` in
  `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`;
  `IntermediateField.finiteDimensional_adjoin` in
  `Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`; and
  `ModuleCat.preservesFiniteLimits_extendScalars_of_flat` in
  `Mathlib.Algebra.Category.ModuleCat.Descent`. Their full signatures and
  surrounding docstrings were inspected.

Edge cases checked: d=0 gives the empty basis, the singleton zero flag, and
empty quotient/scalar/exact-sequence families. d=1 permits E=E₀. Repeated
nonzero eigenvalues and nonzero entries above the diagonal are unrestricted;
no diagonalizability, separability, characteristic, or nontrivial-space
assumption is added. A nontrivial Jordan block is therefore allowed. The field
K may have any characteristic, including inseparable algebraic extensions.

Searches performed with the prescribed `msearch.py`:

- LeanFinder: “An invertible linear operator over an algebraic closure has a
  full invariant flag and adapted basis defined over a single finite
  intermediate field.” Eight hits, including Galois bases and generalized
  eigenspaces, none giving the common finite coefficient model.
- Loogle: `Module.Basis.baseChange, LinearEquiv.baseChange,
  Submodule.quotientMap, Matrix.BlockTriangular`. No hits (the guessed
  `Submodule.quotientMap` identifier does not exist). Source search found the
  actual `Submodule.mkQ`/`mapQ` interfaces instead.
- Mathlib grep: `flag|triangular` in `LinearAlgebra/Eigenspace`. Eleven
  triangularizability/decomposition hits, no descent theorem.
- LeanSearch: “A full invariant flag of a linear automorphism with adapted
  subspace and quotient bases and invertible restricted and quotient
  operators.” Eight hits, including `Module.Basis.toFlag` and invariant
  submodules; none is the item's simultaneous finite-model statement.
- `rg` in Mathlib, `lean/WeilConjectures`, and `lean/Sheaf` found
  `Module.Basis.flag`, tensor base-change APIs and upstream triangularization.
  `rg` for the item ID in `lean/WeilConjectures` found no attachment.
  The new declaration name was searched in all three libraries and
  `dag/lean_names_upstream.json`: no clash. DAG conceptual searches found the
  assigned node and its consumers, not a separate existing finite-coefficient
  flag definition. `tools/blueprint_refs.py search 'automorphism flag'`
  returned zero matching blueprint nodes.

The current source read was
`literature/blueprint/latest/blueprint/sec-deligne-laumon-general/`
`sk-i-dl-general-real/thm-zl-real-mixed-by-curves.proof.md`, paragraph 7.
The algebraic coefficient refinement is the assigned DAG node's expanded
proof of that dimension-zero Jordan-filtration step. No statement correction,
new node, dependency repair, or disputed claim is needed.

Validation: server `scompile.py` typechecked both the sandbox module and its
library path; the initial four line-width warnings were repaired. The final
clean compile and delivery preflight are recorded by the delivery tools.

## Second reading by Q34

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
