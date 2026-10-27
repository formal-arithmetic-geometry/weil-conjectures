## Worker report

The module `Sheaf.Analysis.CompactRemainderCoercivity` states
`ContinuousLinearMap.exists_pos_norm_le_on_orthogonal_ker_of_compact_remainder`.
Its only theorem has proof `sorry`; no definition or additional theorem is introduced.
The node is preserved verbatim outside its new `lean` field. No statement correction,
missing dependency, new node, or STATEMENT-DISPUTED issue was found.

Clause-by-clause correspondence:

- Over the real field: every scalar parameter of the space and map structures is `ℝ`.
  The sole statement dependency `def-weil-field` has Mathlib match `Field` in
  `Mathlib.Algebra.Field.Defs`; its full definition/docstring was read. The canonical
  real field instance supplies it, through the public imports.
- Hilbert space `E`: `{E : Type u}`, `[NormedAddCommGroup E]`,
  `[InnerProductSpace ℝ E]`, `[CompleteSpace E]`. Definiteness comes from the normed
  additive group, compatibility of norm and inner product from `InnerProductSpace`,
  and completeness is for this same induced metric. No finite dimensionality or
  separability hypothesis is present.
- Real normed vector spaces `F,Z`: `{F : Type v}` and `{Z : Type w}`, each with
  `NormedAddCommGroup` and `NormedSpace ℝ`. These structures express the triangle
  inequality, definiteness, and real scalar norm homogeneity. Neither codomain has a
  completeness or inner-product assumption. The independent universes `u v w` are
  explicitly bound and do not restrict the node's spaces.
- Bounded linear maps: `(T : E →L[ℝ] F)` and `(J : E →L[ℝ] Z)`. Mathlib's
  continuous linear maps between normed spaces over the reals are precisely bounded
  linear maps; no choice of bound is added to the statement.
- Sequential compactness of `J`: `hJ` quantifies over every `x : ℕ → E` satisfying
  `∃ M : ℝ, ∀ n : ℕ, ‖x n‖ ≤ M`. This is exactly a bounded sequence in a normed
  space. Such a bound is automatically nonnegative by evaluating at zero.
  Its conclusion provides `φ : ℕ → ℕ`, `z : Z`, `StrictMono φ`, and
  `Filter.Tendsto (fun n : ℕ => J (x (φ n))) Filter.atTop (nhds z)`.
  The indices therefore give a genuine subsequence, and its image converges to an
  element of `Z` itself. We express the node's explicit condition directly with
  Mathlib's `StrictMono` and `Filter.Tendsto`; no second compactness definition is
  introduced and no completeness of `Z` is hidden in it.
- Positive remainder constant and global estimate: `hestimate` is
  `∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖x‖ ≤ C * (‖T x‖ + ‖J x‖)`.
  The sum, norms, universal domain, and strict positivity are exactly the node's.
- Kernel: `T.ker` is the standard linear kernel, with membership `T x = 0`.
- Kernel complement: `T.ker.orthogonal` uses `Submodule.orthogonal` from
  `Mathlib.Analysis.InnerProductSpace.Orthogonal`, whose full definition and
  `mem_orthogonal` were read. Membership is exactly
  `∀ w ∈ T.ker, inner ℝ w v = 0`, in the order specified in the node.
- Conclusion: `∃ D : ℝ, 0 < D ∧ ∀ v : E, v ∈ T.ker.orthogonal → ‖v‖ ≤ D * ‖T v‖`.
  This gives one strictly positive constant uniformly for every vector in the
  kernel complement, with no additional conclusion.

The module has two public imports: `Mathlib.Analysis.InnerProductSpace.Orthogonal`
for the inner-product space and orthogonal complement, and
`Mathlib.Analysis.Normed.Operator.Basic` for continuous linear maps and their
normed-space boundedness API. The only DAG dependency is the Mathlib leaf `Field`;
there are no proof dependencies to import. All standard notions are reused.

Edge cases checked before writing:

- `E = 0`: every vector is zero and any positive `D` works.
- `T = 0`: the kernel is all of `E`, its orthogonal complement is zero, and the
  conclusion is valid even if the kernel is nontrivial.
- `J = 0`: the hypothesis itself gives the conclusion with `D = C`.
- `T` injective: its kernel complement is all of `E`, giving the expected bound.
- `F = 0` is included by the zero-map case; `Z = 0` by the zero-remainder case.
- Noncomplete `F` or `Z`: the node's argument only takes a limit in `E` and uses
  the actual limit in `Z` supplied by `hJ`; neither space is silently completed.
- A diagonal operator with entries tending to zero on real square-summable
  sequences and `J = id` illustrates why the compactness condition is substantive:
  the remainder estimate holds but no kernel-complement bound holds.
- The subsequence starts at index zero, which merely reindexes the node's sequence;
  `StrictMono φ` excludes constant or repeated-index selections.

Searches made for existing declarations (all on 2026-10-24):

1. `msearch.py ... leanfinder` with query
   "A bounded linear map from a real Hilbert space satisfying a norm estimate with a
   compact remainder is bounded below on the orthogonal complement of its kernel".
   Eight hits included `IsCoercive.bounded_below`, `IsCoercive.antilipschitz`,
   `ContinuousLinearMap.bounds_bddBelow`, and positivity-based estimates. Reading
   the Lax-Milgram and operator-bound declarations confirmed no match: the first
   assumes an already coercive bilinear form, and the second concerns upper bounds.
2. `msearch.py ... loogle` with query `"IsCompactOperator", "ker"`: zero hits.
3. `msearch.py ... grep` with query
   `Peetre|compact.*remainder|remainder.*compact|orthogonal.*ker|ker.*orthogonal`
   in `Analysis/`: thirteen hits in adjoint/orthogonal/projection files. Reading
   `ContinuousLinearMap.orthogonal_ker` confirmed it identifies an adjoint range
   closure and does not assert this norm estimate.
4. `msearch.py ... leansearch` with query
   "A norm estimate with a compact remainder implies a norm bound on the orthogonal
   complement of the kernel of a bounded linear map": eight hits, including
   `ContinuousLinearMap.orthogonal_ker`, `opNNNorm_le_bound'`, and complemented-range
   results. None states the claimed compact-remainder estimate.
5. `rg -n` over both `lean/WeilConjectures` and `lean/Sheaf` for
   `compact.*[Rr]emainder|remainder.*[Cc]ompact|Peetre|lem-sfb-compact-remainder-coercivity`:
   no matches. The equivalent node-id search was included in this query.
6. `rg -n` over Mathlib, both project roots, and `dag/lean_names_upstream.json` for
   the proposed full theorem's final name: no matches. The upstream index was also
   searched for `CompactRemainder|compactRemainder|compact_remainder`, without hits.

Source check: read the latest blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`
and the item's complete source and five-step proof record. Demailly's PDF is absent
locally; opened the cited public PDF at
https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf,
including printed p.290. The node honestly records the abstract normalized-sequence
proof as the project's argument, motivated by the analytic compactness estimate.
The declaration docstring includes all five proof steps in full.

Validation: `scompile.py NW lem-sfb-compact-remainder-coercivity` compiled both
sandbox and final module identities cleanly (3.1 seconds each), with no errors or
unexpected warnings. The node signature is extracted verbatim from the declaration,
and JSON uses indent 1, Unicode, and a final newline.

## Second reading by NW

No independent worker reading: the dispatch brief requires the worker to deliver
directly without spawning agents; the maintainer supplies the independent review.
A final author comparison of the node and file checked each hypothesis and clause
listed above. In particular, the compactness condition provides convergence in `Z`
and strictly increasing indices; positivity is retained for both constants; only
`E` is complete; kernel membership and the order of the inner-product arguments
agree exactly with the node. No mismatch or statement correction was found.
