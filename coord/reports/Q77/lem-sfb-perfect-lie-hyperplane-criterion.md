## Worker report

This stage-2 delivery states `LieModule.exists_isCompl_of_perfect_of_simple_hyperplane`
in `Sheaf.Algebra.Lie.PerfectLieHyperplaneCriterion`. Its only proof is `sorry`.
There are no definitions, new nodes, dependency repairs, or statement corrections.

The inherited BLOCKED ending concerned an unchanged stage-1 delivery after N7's split
review. The live node has no `lean` field and `coord/queue.tsv` lists this item at
stage 2. The stage-handoff rule in `coord/brief-stage2.md` §0 explicitly permits
recording the Lean statement after an accepted split. No repair note exists for it.

### Hypothesis and conclusion correspondence

- An arbitrary field k is `(k : Type u) [Field k]`.
- An arbitrary k-Lie algebra L is `(L : Type v) [LieRing L] [LieAlgebra k L]`.
  No finite-dimensionality, nontriviality, characteristic, or algebraic closure is
  imposed on L or k.
- Perfectness is `_hperfect : LieAlgebra.derivedSeries k L 1 = ⊤`.
  `LieAlgebra.coe_derivedSeries_one_eq` identifies this first derived ideal with
  the k-linear span of all brackets, exactly the node's definition of perfect.
- A finite-dimensional representation M is quantified in `hsplit`, with
  `[AddCommGroup M] [Module k M] [LieRingModule L M] [LieModule k L M]
  [FiniteDimensional k M]`. The two Lie-module classes are precisely a bilinear
  action satisfying the commutator identity. They equivalently give the linear
  bracket-preserving map `LieModule.toEnd k L M`.
- Every invariant subspace W is `(W : LieSubmodule k L M)`.
- Simplicity of W is `LieModule.IsIrreducible k L W`. Its definition is
  `IsSimpleOrder (LieSubmodule k L W)`; nontriviality of this order excludes the
  zero module, and its only elements are bottom and top. Thus both parts of the
  node's simple/nonzero condition are present.
- The hyperplane condition is `Module.finrank k (M ⧸ W.toSubmodule) = 1`.
  The quotient is the actual vector-space quotient. As M is finite-dimensional,
  its quotient is finite-dimensional, so finrank is its dimension.
- The splitting hypothesis concludes `∃ D : LieSubmodule k L M, IsCompl W D`.
- The conclusion quantifies arbitrary `(V : Type w)` with all four module/action
  classes and `[FiniteDimensional k V]`, then arbitrary `U : LieSubmodule k L V`,
  and asserts `∃ C : LieSubmodule k L V, IsCompl U C`.
- `IsCompl` means zero intersection and sum equal to the whole space.
  `LieSubmodule.isCompl_toSubmodule` identifies it with the underlying
  vector-space complement condition: existence and uniqueness of the requested
  sum expression. Both complement witnesses are invariant because they are
  Lie submodules, rather than arbitrary vector subspaces.

The universes u, v, w are explicitly declared and remain independent. The test
representations in `hsplit` inhabit `Type (max u w)`, which contains the Hom space
`V →ₗ[k] U` used by the node's proof and its subspaces. This does not restrict
mathematical finite-dimensional representations: every such representation has
coordinates on a finite power of k, and can be transported to that universe.
The conclusion allows V in the independent universe w; no universe equality or
small-universe test hypothesis is imposed. `set_option autoImplicit false`
ensures that no binder or universe was auto-introduced.

### Dependency declarations read and used

- `def-wf-lie-algebra` is a Mathlib node; its `mathlib_match` records
  `LieRing`, `LieAlgebra`, `LieRingModule`, and `LieModule` in
  `Mathlib.Algebra.Lie.Basic`, `LieSubmodule` in
  `Mathlib.Algebra.Lie.Submodule`, `LieModule.IsIrreducible` in
  `Mathlib.Algebra.Lie.Semisimple.Defs`, and `LieAlgebra.derivedSeries`
  in `Mathlib.Algebra.Lie.Solvable`. Its explicit perfectness specialization
  is `derivedSeries k L 1 = ⊤`. These definitions are exposed through the
  public import `Mathlib.Algebra.Lie.Semisimple.Defs`. I read their definitions,
  signatures and docstrings, and the `LieModule.toEnd` signature/docstring in
  `Mathlib.Algebra.Lie.OfAssociative` to check the action formulation.
- `def-weil-finite-dimensional-subspace`: the Mathlib match is
  `FiniteDimensional`, defined in `Mathlib.LinearAlgebra.FiniteDimensional.Defs`
  as `Module.Finite`; imported publicly.
- `def-weil-vector-space-dimension`: its recorded declaration is
  `Module.finrank` in `Mathlib.LinearAlgebra.Dimension.Finrank`; imported publicly.
- Proof dependency `lem-sfb-lie-linear-hom-action`: its exact Mathlib matches
  `LinearMap.instLieRingModule`, `LinearMap.instLieModule`, and
  `LieHom.lie_apply` are in `Mathlib.Algebra.Lie.Basic`, already publicly
  available through the Lie definitions import. I read lines 249-282, including
  the actual commutator formula.
- Proof dependency `lem-trf-finite-dimensional-short-exact-dimension`:
  `ModuleCat.free_shortExact_finrank_add` in
  `Mathlib.Algebra.Category.ModuleCat.Free`; its module is a plain proof import.
- Proof dependency `lem-trf-vector-subspace-complement`:
  `Submodule.exists_isCompl` in `Mathlib.LinearAlgebra.Basis.VectorSpace`;
  its module is a plain proof import. No separate downstream modules are changed.

### Source and edge cases

I read Milne's PDF pp. 488-489 (printed pp. 476-477), Lemma 22.40 and its
(c) to (b) to (a) proof. The node explicitly identifies its statement as an agent
adaptation to Lie modules, not Milne's algebraic-group formulation. The docstring
carries all six DAG proof steps: triviality of lines by perfectness, two strong
induction applications, the Hom action, the scalar-restriction hyperplane, and
an equivariant retraction with complementary kernel.

Checked V = 0, U = 0 and U = V: zero or whole complementary submodules are
allowed, with no Nontrivial assumption on V. A simple W is necessarily nonzero,
so W = 0 is correctly excluded from the hypothesis and handled separately in
its induction. An ambient M of dimension zero has no codimension-one subspace;
when dim M = 1 the only hyperplane is zero and the splitting is immediate.
L = 0 is perfect and has only trivial representations, so ordinary vector-space
complements agree with the statement. Nonzero abelian L is not perfect, so the
perfectness premise is not hollow. In positive characteristic the scalar
commutator still vanishes; no division by dimensions or characteristic-zero
step occurs in this criterion. Infinite-dimensional L is allowed throughout.
The reviewed observation that perfectness can be avoided by using x.E ⊆ K
does not require dropping it from the specified statement.

No STATEMENT-DISPUTED flag or node fault was found.

### Searches

Executed `/home/ubuntu/weil-launcher-all/batch2/msearch.py` with this group/item:

- LeanFinder: "Every invariant subspace of a finite dimensional representation
  of a perfect Lie algebra has a complement if every simple invariant hyperplane
  has a complement". Eight hits: invariant-form orthogonal complements,
  nilpotent Fitting decompositions, triangularizability, Killing-form results;
  none is this simple-hyperplane criterion.
- Loogle: `LieSubmodule, "IsCompl"`. Three hits:
  `LieSubmodule.isCompl_toSubmodule` and two Fitting decompositions for nilpotent
  Lie algebras. The first verifies the complement interpretation, and neither
  of the latter is the criterion being stated.
- Mathlib grep: `hyperplane|IsIrreducible|IsCompl` under
  `Algebra/Lie/Semisimple`. Twelve hits on definitions of irreducibility and
  results about radicals; no matching criterion.
- LeanSearch: "Simple invariant hyperplanes split implies every finite
  dimensional Lie algebra module has invariant complements". Eight hits on
  semisimple individual endomorphisms, vector-space complements, invariant
  forms and triangularizability; none matches.
- `rg -n 'hyperplane|simpleHyperplane|simple_hyperplane|perfectLie|perfect_lie'`
  in both `lean/WeilConjectures` and `lean/Sheaf`: unrelated geometric hyperplanes
  and a Serre-presentation comment; no Lie-module simple-hyperplane criterion.
- `grep -rn 'lem-sfb-perfect-lie-hyperplane-criterion' lean/WeilConjectures`:
  no hits. The final theorem name was also searched in Mathlib, both source
  roots, and `dag/lean_names_upstream.json`, with no hits.

Validation: the prescribed `scompile.py` compiled both its sandbox and library
module modes successfully, with no errors or unexpected warnings.

## Second reading by Q77

I reread the node and the completed file in a separate pass; no second agent was
started, as the dispatch brief prohibits that. This is a self-check, not a claim
of independent review; the maintainer's independent review remains required.

The field, unrestricted Lie algebra, first-derived-ideal perfectness premise,
all finite-dimensional test representations, nonzero simplicity, quotient
of dimension one, invariant complement hypothesis, arbitrary finite-dimensional
V and invariant U, and invariant direct-sum conclusion all match. In particular
I checked that simplicity concerns W itself, not M, and dimension concerns M/W,
not W; both use the correct objects. The complement is `IsCompl` in the Lie
submodule lattice, whose coercion theorem gives exactly unique vector-space
decomposition. The universe of test modules contains the proof's Hom space.
No statement mismatch was found and no clause was changed. There are no new or
dependency modules to review.
