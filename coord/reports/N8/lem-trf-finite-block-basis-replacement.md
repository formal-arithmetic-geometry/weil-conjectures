## Worker report

The module `Sheaf.LinearAlgebra.FiniteBlockBasisReplacement` states
`Module.Basis.finite_block_replacement`, with its entire proof postponed by `sorry`.
It states the existing node without changing its accepted statement or split.
Source read: Stacks Project, `literature/stacks-project/algebra.tex`, Tag 0592,
`lemma-projective-freeness-criteria`, second paragraph of the proof, especially
lines 20658–20674. The theorem docstring includes all five steps of the node proof.

Hypotheses, individually:

- The commutative ring is `{R : Type u} [CommRing R]`.
- The module is `{F : Type v} [AddCommGroup F] [Module R F]`.
- Its specified basis is `(b : Module.Basis ι R F)` with `{ι : Type w}`.
  A separate `Module.Free R F` assumption would be redundant: the given basis
  already witnesses precisely the freeness in the dependency definition.
  No finiteness, nonemptiness, or cardinality restriction is imposed on `ι`.
- The nonnegative integer is `(n : ℕ)`; the distinct selected indices are
  `(e : Fin n ↪ ι)`. We use zero-based `Fin n` for the paper's 1 through n.
- `T` is rendered everywhere by `Submodule.span R (b '' (Set.range e)ᶜ)`:
  the image under the original basis of the complement of the selected indices.
- The vectors and complementary tails are `(y t : Fin n → F)`.
  `ht` requires every `t i` to belong to exactly that complementary span.
- `(B V : Matrix (Fin n) (Fin n) R)` are the given finite square matrices.
  `hy` is exactly the row-oriented equation
  `y i = (∑ j : Fin n, B i j • b (e j)) + t i`.
- The two-sided inverse is expressed by `hBV : B * V = 1` and
  `hVB : V * B = 1`, preserving both equations from the node.

Conclusions, individually:

- The first existential supplies `U : F ≃ₗ[R] F`, with
  `U (b (e i)) = y i` for every selected index and `U (b j) = b j`
  for every other original index. This is precisely that the endomorphism
  prescribed on the basis is an automorphism: a linear map is determined by
  its values on the original basis, so this existential cannot choose a
  different endomorphism. No unspecified arbitrary map is assumed.
- The second existential supplies `b' : Module.Basis ι R F`, with those same
  replacement values on `e i` and original values on the complementary indices.
  Thus it is the prescribed family with the original index type.
- The third existential supplies a basis indexed by `Fin n` of
  `Submodule.span R (Set.range y)`, exactly the node's `G`. Its displayed
  subtype values coerce to `y i` in `F`, so this is the stated basis of `G`.
- The last clause says for every `x : F` there exists a unique pair `p` in
  `G × T` with `x = (p.1 : F) + (p.2 : F)`. Using a unique pair expresses
  precisely uniqueness of both summands, not uniqueness of their sum alone.

Dependencies used:

- `def-weil-pbc-free-module`: recorded declaration `Module.Free` from
  `Mathlib.LinearAlgebra.FreeModule.Basic`, imported publicly. Its definition
  is existence of a `Module.Basis`; the specified-basis portion of this node
  uses `Module.Basis` itself (read its full docstring and structure in
  `Mathlib.LinearAlgebra.Basis.Defs`: `repr : F ≃ₗ[R] (ι →₀ R)`). This is the
  unique finite-coordinate notion in the dependency, without a private copy.
- `def-weil-matrix`: recorded declaration `Matrix` from
  `Mathlib.LinearAlgebra.Matrix.Defs`, imported publicly. Its full signature
  is `Matrix (m : Type u) (n : Type u') (α : Type v) : Type max u u' v`;
  its data is `m → n → α`, exactly the node's row-column family.
- `Mathlib.Data.Matrix.Mul` supplies matrix multiplication and identity used
  in the two inverse hypotheses. There are no other proof dependencies than
  the already public free-module dependency.

Edge cases checked before accepting the kept draft:

- `n = 0`: the hypotheses on vectors and inverse matrices are empty; the
  automorphism and replacement basis are the original ones, `G = 0`, `T = F`,
  and the unique pair is `(0, x)`.
- Empty ambient basis: the embedding forces `n = 0`; the module is zero.
- Empty complementary index set: `T = 0`, and the statement reduces to the
  usual finite invertible basis change, with unique decomposition `(x, 0)`.
- Infinite ambient basis: `ι` is arbitrary and coordinate vectors remain
  finitely supported by `Module.Basis`; no finite-rank premise slipped in.
- Singleton block: the inverse calculation gives the usual rescaling with
  a complementary tail, over a commutative ring rather than only a field.
- The zero ring is allowed. Its modules are subsingleton, and coordinate
  equivalences and unique decomposition remain valid with their given indices.
- Matrix orientation: `U W(e_i)` has coefficient matrix `V B`; `W U(e_i)`
  has `B V`, after subtracting tails. Both required inverse equations occur.

Searches for an existing statement (kept searches plus fresh checks):

- `msearch.py leanfinder`, query "Replace finitely many vectors of an arbitrary
  module basis by vectors with invertible finite coordinate matrix and arbitrary
  complementary tails": eight hits, including `Module.Basis.reindexRange`,
  `Module.Basis.mkFinCons`, `Module.Basis.sumExtend`, and `Module.Basis.unitsSMul`.
  Reindexing does not change the vectors, scaling handles only diagonal changes,
  and extension results do not prescribe this complement and these tails.
- `msearch.py loogle`, query "Module.Basis, Matrix, IsUnit": twelve hits,
  including `Matrix.toLinearEquiv`, `LinearMap.isUnit_toMatrix_iff`, and
  `LinearEquiv.ofIsUnitDet`. These use a finite basis of the entire module;
  they do not state replacement in an arbitrary ambient basis with tails.
- `msearch.py grep`, query "replace|block|update", subdirectory
  `LinearAlgebra/Basis`: four tactic-text hits in `Basic` and `Exact`, no match.
- The kept `msearch.py leansearch` query "Replacing a finite subset of a possibly
  infinite module basis with an invertible coordinate block gives a basis and a
  free direct summand" returned eight hits, including `invertibleToMatrix`,
  `baseChange`, `reindex`, and `unitsSMul`; none states all the present clauses.
- `rg -n 'finite_block_replacement|finite.block|basis.replacement'` over both
  project roots found no declaration stating this result; the parent
  `Sheaf.SecTraceFormula.ProjectiveElementFreeSummand` mentions its proof idea.
- Search for the exact node id in `lean/WeilConjectures` found no match.
  Name search of the new theorem in the two project roots found no collision.

Validation: `scompile.py N8 lem-trf-finite-block-basis-replacement` compiled the
module in both its sandbox and library locations successfully (0.9 seconds each).
No errors or unexpected warnings. All variables and universes are explicitly bound.
There are no new definitions, extra nodes, dependency repairs, or statement faults.

The inherited BLOCKED text referred to the passing Q56 stage-1 split, not a
stage-2 Lean delivery. The current `coord/brief-stage2.md` section 0 explicitly
permits this handoff; `coord/queue.tsv` lists the node at stage 2 and it has no
Lean record on the read base. This delivery preserves the accepted split.

## Second reading by N8

I re-read the node and the kept module against the source and checked each
hypothesis and all four conjuncts as matched above. In particular the complement
uses indices of the original basis, the finite sums have row orientation,
both inverse equations are present, the new full basis keeps `ι`, the basis of
`G` keeps `Fin n`, and uniqueness quantifies a pair of actual submodule elements.
No mismatch or statement correction was found, and the kept Lean file required
no edit. This is a worker self-check; the independent maintainer review remains
the independent reading required by this dispatched workflow. No other agent
was started, as the dispatch brief forbids doing so.
