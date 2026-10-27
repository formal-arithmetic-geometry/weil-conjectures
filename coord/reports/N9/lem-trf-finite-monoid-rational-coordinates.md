## Worker report

The module `Sheaf.GroupTheory.FiniteMonoidRationalCoordinates` states
`TensorProduct.finite_monoid_rational_coordinates`, with one `sorry` and no new definitions.
Only the item's `lean` field changes. No statement correction or dependency repair is needed.

Source read: the item's complete statement and six proof steps; its parent
`lem-trf-sharp-cone-lattice-intersection` and the parent's landed Lean module;
the current blueprint's `lem-trf-local-term-locality.proof.md`; ILO Exposé VIII,
Remark 3.1.29, printed p. 103 (PDF page 109), via pdftotext. The ILO remark concerns
combinatorial fans and is motivation, as the node explicitly says; the exact finite
coordinate calculation is the agent-extracted statement in this node. Stacks algebra.tex,
Section 00CV and Lemma 00CX, lines 1703--1780, were read for the tensor construction,
universal property, and pure-tensor generation used in its proof plan.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- `G : Type u` with `[AddCommGroup G]` is an arbitrary abelian group, with its canonical
  integer module structure. The universe `u` is explicit and unrestricted.
- `r m : ℕ` and `e : Module.Basis (Fin r) ℤ G` give the finite integral basis.
  `e.repr g k` is exactly its unique integer coordinate λ_k(g). Mathlib's basis is a
  linear equivalence to finitely supported coordinates, so it imposes precisely unique
  integral expansion. No separate freeness or finite-generation assumption is added.
- `p : Fin m → G` and `hp : ∀ g, ∃ a : Fin m → ℤ, g = ∑ j, a j • p j` render group
  generation exactly. No requirement that the p_j be independent, nonzero, or distinct.
- `P : Set G` with `hP` fixes P to the set of natural combinations in the node.
  It introduces a name for the exact set, without requiring any additional structure.
- `TensorProduct ℤ ℚ G` is the dependency-recorded extension-of-scalars convention.
  The dependency `def-weil-module-base-change` explicitly records tensor symmetry to
  account for its order. `TensorProduct.comm ℤ G ℚ` takes `g ⊗ q` to `q ⊗ g`.
  Thus the node's `i(g)` is `(1 : ℚ) ⊗ₜ[ℤ] g`, and `q • i(g)` equals `q ⊗ₜ[ℤ] g`.
  The canonical left-factor ℚ-module action is exactly `a(q ⊗ g) = (a*q) ⊗ g`.
  This is also the order used by the already landed parent module.
- `C : Set (TensorProduct ℤ ℚ G)` with `hC` defines C by finite sums indexed by `Fin n`,
  with every `v l ∈ P` and rational coefficient `q l ≥ 0`. All finite sums admit this
  indexing; `n = 0` is allowed. Scalar multiples are rendered as the equal pure tensors.
- The existential `L : Fin r → (TensorProduct ℤ ℚ G →ₗ[ℚ] ℚ)` supplies all rational
  linear coordinate maps together. Its first conjunct is their prescribed value on
  every pure tensor, for every k, g, and q. The next conjunct quantifies over each
  competing rational-linear `L'` with those same values and states `L' = L k`.
- The third conjunct gives reconstruction for every tensor x. The fourth states that
  every other rational coefficient vector d giving that expansion satisfies
  `∀ k, d k = L k x`. These two conjuncts give existence and uniqueness of expansion.
- The fifth conjunct is precisely the set equality for C, with one nonnegative
  rational coefficient for each p_j.
- The sixth conjunct quantifies over EVERY integer matrix `b : Fin r → Fin m → ℤ`,
  assumes exactly its row identities, and quantifies over EVERY x. Each c_j is written
  explicitly as `∑ k, L k x * (b k j : ℚ)`. The two finite sums use respectively
  `max c_j 0` and `max (-c_j) 0`, with subtraction in the rational tensor group.
  No `let` binder hides coefficients or makes stage-3 unfolding unavailable.
- The final conjunct explicitly states that `m = 0` forces every g and every x to zero.
  Both empty signed sums and the empty generator expression for C are the actual Lean
  empty sums; the preceding cone equality therefore makes C the singleton zero set.
  Empty bases also remain allowed through `Fin r` without a `Nonempty` assumption.

Dependency declarations read and used:

- `def-weil-pbc-module-tensor-product` is a Mathlib-status leaf. Its recorded
  `TensorProduct` (Defs.lean:81), `TensorProduct.tmul` (107), `TensorProduct.mk` (378),
  and `TensorProduct.lift` with `lift.tmul` and `ext'` (Basic.lean:123--138) were read,
  including their full signatures and available docstrings. The statement uses the
  actual TensorProduct and tmul. `LinearMap.rTensor` and its pure-tensor signature
  (Map.lean:331--346) were also read, although that extra clause is not needed here.
- `def-weil-module-base-change` records `Mathlib.LinearAlgebra.TensorProduct.Tower`,
  `LinearMap.baseChange`, `TensorProduct`, `TensorProduct.mk`, and
  `TensorProduct.AlgebraTensorModule.distribBaseChange`. Their signatures and docstrings
  were read at Tower.lean:431--465 and 650--667. The statement uses the tensor and
  its canonical scalar extension from that module; no private base-change construction.
- Mathlib `Module.Basis` and its `repr` were read at Basis/Defs.lean:79--120.
  `Mathlib.LinearAlgebra.Basis.Defs` is imported for these actual notions.
  TensorProduct.Tower is publicly imported for the recorded statement dependencies.
  Both proof dependencies are the same two nodes, so no additional proof import is needed.

Edge cases checked mathematically before writing: r = 0 forces G = 0 by the basis
expansion; m = 0 forces G = 0 by hp and then every pure tensor is zero. If r = 0
and m > 0, all p_j and c_j are zero. A positive-rank basis with m = 0 cannot satisfy hp,
so this inconsistent input case is handled by the existing hypothesis, not excluded.
Redundant or zero generators are allowed. For G = ℤ, p = (-1), and e = (1), the row
b = (-1) yields c = -x and the asserted signed formula recovers x. For p = (2,3),
the row (-1,1) reconstructs e = 1; this checks that group generation is sufficient,
without silently assuming that each basis vector is in the natural monoid P.

Searches run with the prescribed msearch.py, group N9 and this item:

- leansearch: `Finite integral basis rational tensor coordinates nonnegative cone monoid generators signed coefficients`.
  Eight hits including NumberField.integralBasis, AddGroupCone.nonneg,
  ConvexCone.positive, and Module.Basis.tensorAlgebra. None states this combined lemma.
- leanfinder: `Finite integral basis induces unique rational coordinate linear maps on G tensor Q and nonnegative rational cone generated by finite monoid generators`.
  Eight number-field integral-basis/lattice results. They require special number-field
  objects and do not give this general abelian-group cone equality or signed formula.
- loogle: `TensorProduct, Module.Basis`.
  Twelve hits including Module.Basis.baseChange, TensorProduct.equivFinsuppOfBasisLeft,
  eq_repr_basis_left, and tensor-basis coordinate lemmas. Read TensorProduct/Basis.lean
  through the returned basis/coordinate definitions. These cover coordinate components,
  not the full cone comparison and explicit formula for every integer matrix.
- grep: `rightModule|rightActions|RightActions|baseChange`, subdirectory
  `LinearAlgebra/TensorProduct`: 24 hits, including Tower.baseChange,
  distribBaseChange, and Basis.baseChange. No full-statement match.
- Direct rg in both `lean/WeilConjectures` and `lean/Sheaf`, and in
  `dag/lean_names_upstream.json`, for the item name, `finiteMonoidRationalCoordinates`,
  `finite_monoid_rational_coordinates`, finite-monoid/rational-coordinate/cone phrases.
  Direct grep for the node id in WeilConjectures found no declaration. Existing
  SharpConeLatticeIntersection, CompleteToricModel and GordanRationalCone were read;
  none states this item. The parent describes the calculation in its proof plan only.
  An attempted inspection of TensorProduct/RightActions.lean and Comm.lean found no such
  files; this was a path search, not evidence for a mathematical absence.

Validation: scompile.py compiled the sandbox and library module separately against
server published sources, both clean (4.7 s and 4.8 s), without errors or warnings.
The sole theorem proof is `by sorry`. All variables/universes are explicitly bound;
no definitions, instances, local notation, or extra axioms are introduced.

## Second reading by N9

A separate clause-by-clause rereading of the final node copy and Lean file was performed
by this worker. The dispatcher explicitly forbids starting another agent; the maintainer's
independent delivery review remains the independent reading. This section does not claim
that a second person or agent has reviewed the statement.

The rereading checked the binder list against every hypothesis, and each of the seven
conjuncts against the conclusion: pure-tensor values, per-coordinate uniqueness,
reconstruction, uniqueness of coefficients, cone equality, arbitrary matrix signed
formula, and the empty-generator zero case. In particular `hP` uses ℕ, hp and matrix b
use ℤ, L and coefficients use ℚ, and nonnegativity occurs only in C and its generator
presentation. All quantifiers over k, g, q, d, b, and x have the same scope as in the node.
The tensor-order difference is the canonical symmetry explicitly allowed in the recorded
base-change dependency and used by the parent. The scalar action is on the rational
factor, so no unjustified ℚ-module structure on G is assumed. No hypothesis, clause,
or edge case was found missing; no mathematical change was made during this rereading.
The full six-step proof appears in the theorem docstring, including the named dependency
nodes and the rank-zero/generator-zero cases. The node record copies the exact multiline
signature from the theorem keyword up to `:=`. Only its `lean` field was changed.
