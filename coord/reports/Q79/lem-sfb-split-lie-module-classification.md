## Worker report

The module `Sheaf.Algebra.Lie.SplitLieModuleClassification` states
`LieAlgebra.split_lie_module_classification`, with a single `sorry` and no
new definitions. The node is copied unchanged except for its `lean` field.
Its signature is copied verbatim into `lean.statement`.

Source read: Milne, Algebraic Groups (2017), Theorem 23.70 and its proof
(a), (b), (d), printed pp. 507–508 (PDF pp. 519–520). This explicitly uses
Weyl complete reducibility, the standard description of semisimple Lie
representations, and the integral Cartan weight grading. The DAG expands
that independent Lie-theoretic input in thirteen proof steps; all thirteen
are carried into the theorem docstring, including the rational Casimir
argument and arbitrary-field-extension kernel argument. The locally
unavailable Serre Chapter VII remains the additional source named by the node.

Hypotheses, in node order:

- Finite-dimensional rational Lie algebra: `(g : Type u) [LieRing g]
  [LieAlgebra ℚ g] [FiniteDimensional ℚ g]`. Mathlib's alternating bracket,
  Jacobi identity and scalar compatibility are the node's Lie algebra notion.
- Semisimple means no nonzero solvable ideal: `[HasTrivialRadical ℚ g]`, using
  the recorded `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`.
  It is deliberately not the separately defined Mathlib `IsSemisimple`.
- Maximal abelian Cartan subalgebra: `(H : LieSubalgebra ℚ g)
  [IsLieAbelian H]` and `hmax`. The latter quantifies over all abelian
  subalgebras containing H. Rational diagonalizability of every adjoint
  operator is `hsplit`, the supremum of its ordinary rational eigenspaces.
- Root spaces and nonzero roots: `LieModule.weightSpace g (α : H → ℚ)`
  and `hR : α ∈ R ↔ α ≠ 0 ∧ weightSpace ... ≠ ⊥`.
- Normalized coroots: `c : R → H` and `hc`. Each coroot belongs to the
  span of brackets of the opposite root spaces and evaluates to 2.
  This is exactly the normalized bracket-line characterization in the
  root-decomposition dependency and the highest-weight existence dependency.
- Simple-root base: `Δ : Finset R`, `b : Module.Basis Δ ℚ (Module.Dual ℚ H)`
  and `hb` identify the actual simple roots with a rational dual-space basis.
  `hcoords` says each root or its negative is a sum of these roots with
  natural coefficients, equivalently integer coordinates of one sign.
- Integral lattice P: `P : Submodule ℤ (Module.Dual ℚ H)` and `hP` specify
  membership by integer evaluation on every coroot. This is the same
  interface as `exists_rational_highestWeight_module`.
- Dominant weights P+: `D : Set P` and `hD` specify precisely nonnegative
  evaluation on each simple coroot. `D` is a set parameter with its defining
  equivalence, not a new notion or an arbitrary restricted collection.
- Chosen modules: `L : D → Type v`, with dependent `AddCommGroup`, rational
  `Module`, `LieRingModule`, `LieModule`, `FiniteDimensional` and
  `LieModule.IsIrreducible` instances. The Lie action axioms give exactly
  `[x,y]v = x(yv) - y(xv)`; irreducibility means nonzero and no nontrivial
  invariant subspace. These are the modules supplied by the recorded
  highest-weight existence theorem, universally quantified over their choice.
- Cyclic highest vectors: `vtop` and `hvtop`. The four conditions are
  nonzero, Cartan eigenvalue equal to the indexing weight, annihilation by
  every positive root space, and `LieSubmodule.lieSpan ℚ g {vtop lam} = ⊤`.
  The Lie span is exactly the rational span of all finite iterated actions,
  including the empty product. No action or choice is hidden in a definition.

Conclusions, in node order:

1. Every finite-dimensional rational module is quantified as `V : Type w`
   with its module/action instances. `n : ℕ`, `lam : Fin n → D`, and invariant
   `N : Fin n → LieSubmodule ℚ g V` give the finite summands.
   `DirectSum.IsInternal (fun i ↦ (N i).toSubmodule)` gives a genuine direct
   sum spanning V; `Nonempty (N i ≃ₗ⁅ℚ,g⁆ L (lam i))` identifies each summand
   with the specified chosen module. Because these are invariant subspaces
   and equivariant equivalences, this is a direct sum of Lie modules, not
   just a vector-space decomposition. Repeated highest weights are allowed.
2. Pairwise nonisomorphism is `Nonempty (L lam ≃ₗ⁅ℚ,g⁆ L mu) ↔ lam = mu`.
3. Every equivariant endomorphism `f` has a rational scalar `a` with
   `∀ m, f m = a • m`. This includes zero and all scalar endomorphisms.
4. For each dominant weight, every irreducible module `S : Type w` with a
   nonzero highest vector of that weight is Lie-linearly isomorphic to
   `L lam`. There is intentionally no finite-dimensionality assumption on S.
5. Absolute simplicity is `∀ (K : Type t) [Field K] [Algebra ℚ K],
   LieModule.IsIrreducible K (K ⊗[ℚ] g) (K ⊗[ℚ] L lam)`.
   These are Mathlib's canonical scalar-extended algebra and action,
   not arbitrary actions on a tensor product or only algebraic extensions.
6. The ordinary top weight space has rational finrank 1 and equals
   `Submodule.span ℚ {vtop lam}`. Every vector annihilated by all positive
   root spaces belongs to this same line, including the zero vector.
7. For any finite-dimensional module, the finite set `Ω` consists of
   integral weights with nonzero ordinary simultaneous eigenspaces; the
   `DirectSum.IsInternal` clause decomposes the entire module into those
   actual spaces. No generalized eigenspace substitutes for an eigenspace.
8. The zero module is included: `n = 0` is permitted, with no `Nonempty`
   index hypothesis. In a zero module no nonempty family of summands
   isomorphic to the nonzero L(lam) can occur, so its decomposition is
   necessarily empty. Likewise the nonzero-space condition forces Ω empty.
9. `Subsingleton g` states the zero Lie algebra case without excluding it
   at the outset. Each chosen module is rationally linearly equivalent to Q,
   with its chosen highest vector carried to 1 and action identically zero.
   Every simple module, with no dimension assumption, is linearly equivalent
   to Q. Together with `hR`, the basis, `hP` and `hD`, this is precisely the
   unique weight 0 and unique simple module L(0) = Q, up to isomorphism.

Dependency declarations used, read with their signatures and docstrings:

- `Mathlib.Algebra.Lie.Basic`: `LieRing`, `LieAlgebra`, `LieRingModule`,
  `LieModule`, `LieModuleHom`, `LieModuleEquiv` (the corresponding entries in
  the `def-wf-lie-algebra` Mathlib match).
- `Mathlib.Algebra.Lie.Semisimple.Defs`: `LieModule.IsIrreducible` and
  `LieAlgebra.HasTrivialRadical`; `Mathlib.Algebra.Lie.Semisimple.Basic`:
  `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`, as recorded by
  `def-wf-semisimple-lie-algebra`.
- `Sheaf.Algebra.Lie.SplitSemisimpleRootDecomposition`:
  `LieAlgebra.exists_splitSemisimple_rootDecomposition`. Its ordinary roots,
  adjoint splitting, root basis and normalized bracket-line coroot interface
  are reused. The theorem is imported publicly.
- `Sheaf.Algebra.Lie.RationalHighestWeightModules`:
  `LieAlgebra.exists_rational_highestWeight_module`. Its integral lattice,
  dominant evaluation, module structures, ordinary weight-space convention,
  nonzero cyclic highest vector, and rank-zero normalization are reused.
  The theorem is imported publicly.
- `Mathlib.Algebra.Lie.Weights.Basic`: `LieModule.weightSpace`, the actual
  intersection of ordinary eigenspaces; `Mathlib.Algebra.DirectSum.Module`:
  `DirectSum.IsInternal`, for the inclusion map from the direct sum.
- `Mathlib.Algebra.Lie.BaseChange`: the canonical
  `LieAlgebra.ExtendScalars` Lie algebra and Lie module instances, whose
  tensor bracket is `[a ⊗ x,b ⊗ m] = ab ⊗ [x,m]`.

Proof-only imports are plain imports: the recorded
`Sheaf.Algebra.Lie.PerfectLieHyperplaneCriterion`, `Mathlib.Algebra.Lie.Sl2`
(the recorded primitive-string declarations),
`Mathlib.LinearAlgebra.RootSystem.BaseExists` (root-base spans), and
`Mathlib.LinearAlgebra.Trace` (trace and trace cyclicity). Four proof-only
nodes currently have no recorded Lean module or Mathlib match:
`lem-sfb-semisimple-lie-surjective-image`,
`lem-sfb-faithful-semisimple-trace-form`,
`lem-sfb-sl2-invariant-complement`, and
`lem-sfb-verma-monomial-weight-basis`. They are not needed to type this
statement; their proof uses are retained in the docstring. No proof
prerequisite has been removed from the node.

Edge cases checked: zero algebra (empty roots/base and unique zero dominant
weight), zero module (empty summands and empty weight support), trivial
one-dimensional representations, multiplicities of a chosen simple,
zero endomorphism, zero vector in the positive-root kernel, arbitrary
possibly infinite-dimensional simple S in uniqueness, and transcendental
field extensions in absolute simplicity. Algebra, chosen modules, test
modules and extension fields have independent explicit universes u,v,w,t.
There is no characteristic restriction beyond the given rational base.

Searches made through the prescribed `msearch.py`:

- LeanFinder: “finite dimensional split semisimple Lie algebra rational
  highest weight classification absolutely irreducible modules”; eight
  hits about Geck constructions, root systems, and generalized weights.
  None states this classification.
- Loogle: `LieModule.IsIrreducible, LieModuleEquiv, LieModule.weightSpace`;
  zero hits.
- Mathlib grep: `highestWeight|highest.weight|absolutely.*(simple|irreducible)`
  in `Algebra/Lie`; one unrelated comment in `Basis/Prod.lean`.
- LeanSearch: “A finite dimensional module of a split semisimple rational
  Lie algebra is a direct sum of simple highest weight modules, which are
  absolutely simple”; eight hits on semisimple ring modules and semisimple
  Lie algebras. These assume semisimplicity of a module, or concern the
  adjoint Lie algebra, and do not state this theorem.
- Direct `rg` of `lean/WeilConjectures` and `lean/Sheaf/Algebra/Lie` for
  highest weights, absolute simplicity and the proposed declaration name;
  only the two supplied dependencies and unrelated polynomial absolute
  irreducibility appeared. `grep -rn` for the item ID in
  `lean/WeilConjectures` found nothing, and the proposed declaration name
  has no hit in `dag/lean_names_upstream.json`, Mathlib or the project.

No statement correction, dependency repair, new node, or disputed assertion
was needed. Compilation and preflight results are recorded below.

## Second reading by Q79

This is a separate pass by the dispatcher worker; no other agent was started,
as the assignment expressly prohibits it. The independent delivery review
belongs to the maintainer.

I reopened the node and module and compared every clause against the binders
and eight conjuncts. The simple-root base is a full basis, not merely an
independent subset. Root normalization includes bracket-line membership, not
just evaluation 2. The uniqueness conjunct quantifies over arbitrary simple
modules, whereas finite dimension is required only for the decomposition
clauses. Absolute simplicity extends both the algebra and module and ranges
over every field extension. The positive-root-kernel clause quantifies over
all vectors, not just weight vectors. The decomposition indexes allow
multiplicities and the empty case. During this reading I separated the
universes of g, the chosen family L, tested modules and extension fields;
there is no forced equality between their universes. No mathematical mismatch
with the unchanged node was found.

Validation: the prescribed server `scompile.py` compiled both the sandbox
statement and its library module successfully, with no errors or unexpected
warnings. No local compiler or global build was run. A structural comparison
confirms that the node differs from the read-only source only in `lean`, and
the module has exactly one named theorem and one postponed proof. All Lean
lines are at most 100 characters; auto-bound implicits are disabled.
