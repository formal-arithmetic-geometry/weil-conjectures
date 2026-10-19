## Worker report

The module `Sheaf.ZetaLinearAlgebra.LinearRecurrenceShiftSpan` states
`LinearRecurrence.shift_span_bound`. Its sole proof is `sorry`, as required in stage 2.
No definition, auxiliary theorem, dependency repair, new node, or statement correction is
needed. The copied node changes only in `lean`.

I read the complete item, all six statement dependencies and both additional proof
prerequisites, including their Mathlib declarations and docstrings. I also read the current
main-20261015 blueprint proof, third paragraph, final sentences: the coordinate recurrence
expresses R_(j+d) in the span of the preceding d rows, and all rows therefore lie in the span
of R_0,...,R_(m+d-1). This is the item's source. The theorem docstring carries all four steps
of the node's natural-language proof, including the independent-subfamily dimension argument.

Hypotheses and conclusions, clause by clause:

- A field K is `{K : Type u} [Field K]`, with explicitly declared `universe u`; there is no
  characteristic restriction and no restriction of K to the smallest universe.
- The nonnegative integer m is `m : ℕ`; the positive integer d is `d : ℕ` with `hd : 1 ≤ d`.
  Natural numbers encode precisely the nonnegative integer indices in the source.
- The d given coefficients are `a : Fin d → K`, indexed 0 through d-1; the given sequence
  is `c : ℕ → K`.
- The eventual recurrence is exactly the dependency's recorded specialization:
  `(⟨d, fun i ↦ -a i⟩ : LinearRecurrence K).IsSolution (fun n ↦ c (n + m))`.
  Unfolding the recorded `LinearRecurrence.IsSolution` gives, for every n : ℕ,
  c((n+d)+m) = sum over i : Fin d of (-a i) * c((n+i)+m).
  Set N=n+m and commute/associate natural-number addition: this is
  c(N+d) = -sum_i a_i*c(N+i) for all N ≥ m. Conversely every N ≥ m is (N-m)+m,
  so this encoding neither strengthens nor weakens the recurrence. The sign agrees with
  the source's equation c(N+d)+sum_i a_i*c(N+i)=0.
- R_j is written directly as `fun s : ℕ ↦ c (j + s)`; this has the exact coordinate order
  in the node. These are elements of the existing pointwise K-module `ℕ → K`.
- The first conclusion is `∀ j : ℕ, ... ∈ Submodule.span K (Set.range ...)`. Its generator
  family is `fun i : Fin (m + d) ↦ fun s : ℕ ↦ c (i.val + s)`, exactly the first m+d rows,
  with indices 0,...,m+d-1. No independence, distinctness, or nonvanishing is assumed.
- V is written directly, without a second definition or an extra binder hypothesis, as
  `Submodule.span K (Set.range (fun j : ℕ ↦ fun s : ℕ ↦ c (j + s)))`.
  The next conjunct `FiniteDimensional K (...)` states finite-dimensionality of precisely
  this span of all shifted rows.
- The last conjunct is `Module.finrank K (...) ≤ m + d` for the very same submodule.
  It accompanies finite-dimensionality, so the convention finrank=0 in infinite dimension
  cannot weaken the assertion.

Dependency declarations used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs` (available through the public
  statement imports).
- `def-weil-eventual-linear-recurrence`: `LinearRecurrence.IsSolution`,
  `Mathlib.Algebra.LinearRecurrence`; used exactly as its `mathlib_match.how` prescribes,
  with order d, coefficients -a_i, and the tail n ↦ c(n+m).
- `def-weil-sequence-subspace`: `Submodule`, `Mathlib.Algebra.Module.Submodule.Defs`, on
  the existing pointwise sequence module; used through the two `Submodule.span` terms.
- `def-weil-submodule-span`: `Submodule.span`, `Mathlib.LinearAlgebra.Span.Defs`; its
  smallest-submodule definition supplies both spans.
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional`,
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`, the second conjunct.
- `def-weil-vector-space-dimension`: `Module.finrank`,
  `Mathlib.LinearAlgebra.Dimension.Finrank`, the third conjunct.
- Proof-only dependency `lem-weil-span-independent-subfamily`:
  `exists_linearIndependent'`, `Mathlib.LinearAlgebra.LinearIndependent.Lemmas`.
- Proof-only dependency `lem-weil-dimension-span-independent-family`:
  `finrank_span_eq_card`, `Mathlib.LinearAlgebra.Dimension.Constructions`.
  Both proof modules are explicitly imported without `public`; the complete proof plan
  names their role. The public LinearRecurrence import also exposes its own dimension
  dependencies, so the existing span and finrank definitions are available to consumers.

Edge cases checked before writing:

- m=0: the tail is c itself, the initial family has exactly d rows, and the bound is d.
- d=1: a is a one-element family and the span bound is m+1. d=0 is excluded exactly as
  in the source; no additional positivity condition is placed on m.
- c=0: every row and both spans are zero; finite-dimensionality and the dimension bound
  are valid, with no requirement that a generator be nonzero.
- m=0,d=1,a_0=0: the recurrence only forces c_(n+1)=0; c_0 remains arbitrary. The
  single initial row correctly spans every shift, including the nonzero initial impulse.
- Over ℚ, m=1,d=1,a_0=-1 and c=(5,1,1,...) satisfy the recurrence only from index 1.
  R_0 and R_1 are independent (compare coordinates 0 and 1), giving dimension 2=m+d.
  In particular the statement keeps the exceptional initial row rather than claiming
  a d-dimensional bound or imposing the recurrence from 0.
- Repeated or zero initial rows and a nonminimal recurrence order are allowed. The theorem
  gives an upper bound, not equality. Its coefficients need not have a_0 nonzero.
- All characteristic-p fields are allowed: the coordinate recurrence and span argument
  require no division by a prescribed coefficient or integer.

Searches for an existing declaration (all prescribed service calls ran for Q18 and this item):

- `msearch.py ... leanfinder "Every shift of an eventually recurrent sequence lies in the
  span of the first m+d shifts and that span has dimension at most m+d"` returned eight
  hits: seven unrelated Profinite/Nobeling span statements and
  `LinearRecurrence.solSpace_rank`. None gives the eventual shift-span containment.
- `msearch.py ... loogle "LinearRecurrence.IsSolution, Submodule.span"` returned zero hits.
- `msearch.py ... grep "shift|IsSolution|solSpace_rank" Algebra/LinearRecurrence.lean`
  returned five displayed hits for IsSolution and its solution-construction lemmas.
  The wrapper displays line numbers in the file column for this single-file search;
  I opened the actual source. There is no theorem for the required shift span.
- `msearch.py ... leansearch "All shifts of a sequence satisfying an eventual linear
  recurrence lie in the span of its first finitely many shifts, with dimension bounded
  by their number"` returned eight hits: solSpace, is_sol_iff_mem_solSpace, tupleSucc,
  solSpace_rank, IsSolution, order, mkSol and instInhabitedLinearRecurrence. Their types
  concern the recurrence or its full solution space, rather than the item's conclusion.
- `rg` searches in Mathlib for the proposed name `shift_span_bound` returned no match.
  Read Algebra/LinearRecurrence.lean, Span/Defs.lean, FiniteDimensional/Defs.lean,
  Dimension/Finrank.lean, LinearIndependent/Lemmas.lean (exists_linearIndependent'),
  and Dimension/Constructions.lean (the span bounds and finrank_span_eq_card).
- `rg` in the read-only upstream `WeilConjectures/` tree for recurrence/shiftSpan and
  the exact item id, and `rg` in `lean/Sheaf/` for recurrence/shiftSpan and the proposed
  declaration name, found related upstream modules but no existing complete statement.
  The exact item id is absent upstream. A name search in `dag/lean_names_upstream.json`
  also found no collision with the proposed declaration.
- I opened the full signatures, docstrings and implementations in upstream
  `WeilConjectures.ZetaLinearAlgebra.ShiftSpan` and
  `WeilConjectures.ZetaLinearAlgebra.RationalityCriterion`. The closest theorem,
  `finiteDimensional_shiftSpan_of_forall_add_eq_zero`, concludes only
  `FiniteDimensional K (shiftSpan K c)`. Although its proof establishes containment
  locally, neither that containment nor the numerical dimension bound is in the
  declaration's type. It cannot be an exact existing attachment for this node.
  The new theorem introduces no parallel definition of shiftSpan: V is expressed with
  the recorded existing `Submodule.span` directly, as in the node's own statement.

No statement dispute or node fault was found. The recurrence dependency's recorded
specialization is usable as written, so no dependency interface is replaced.

Validation for this completion attempt (2026-10-17): I reread the node, its six statement
dependencies and both proof-only prerequisites, their recorded Mathlib signatures and
docstrings, and the current main-20261015 blueprint proof. I reran the prescribed LeanFinder,
Loogle and Mathlib grep searches; none supplies the complete statement. Recursive searches
in the upstream WeilConjectures tree and shared lean/Sheaf tree found no exact theorem or
collision with LinearRecurrence.shift_span_bound. The shared lean/Sheaf tree has no
ZetaLinearAlgebra directory, so the search was also run over the entire shared tree.

The existing sandbox Lean statement needs no change. I removed the old report's unattributed
second-reading section: this is a worker completion, and the independent second reader must
write that section. The copied node is refreshed from the shared base, changing only lean,
with its statement signature taken verbatim from the module and its date taken in UTC.
The compilation result is recorded below; dry-run.log records the required dry delivery.

The completion attempt's scompile.py run succeeded: the sandbox form and the library-module
form each compiled in 1.0 seconds, with no errors or warnings. The LeanSearch query above
was also rerun and returned the same eight recurrence/solution-space declarations.


## Second reading by Q18

I am the independent second reader, not the statement's author. I read the sandbox node
and Lean module together, all six statement-dependency nodes and the two additional
proof-dependency nodes, the recorded Mathlib declarations in the pinned checkout, and
both the master blueprint statement/proof and the current main-20261015 proof of
`prop-weil-rationality-criterion`. The source is this blueprint, not a Stacks tag.
Its ambient assumptions are an arbitrary field K and a coefficient sequence indexed by
nonnegative integers; its condition (3) explicitly has m >= 0 and d >= 1. No further
characteristic, finiteness, or nonvanishing hypothesis is assumed. There is no repair note
for this item and no `statement_change` in the copied node.

My independent object/hypothesis/conclusion inventory and the matching Lean are:

1. Arbitrary field K: `{K : Type u} [Field K]`, with `universe u` explicitly declared.
   Verdict: exact. Mathlib's `Field` extends `CommRing` and `DivisionRing`; no extra
   instance is requested.
2. Nonnegative integer m and positive integer d: `(m d : ℕ) (hd : 1 ≤ d)`.
   Verdict: exact; natural-number binders encode precisely these nonnegative indices.
3. Given d coefficients a_0,...,a_(d-1) in K: `(a : Fin d → K)`.
   Verdict: exact, with the increasing index convention of the dependency node.
4. Given sequence (c_n) in K: `(c : ℕ → K)`. Verdict: exact, with no restrictions on
   its exceptional initial values.
5. Recurrence from index m: `hrec` is
   `(⟨d, fun i ↦ -a i⟩ : LinearRecurrence K).IsSolution (fun n ↦ c (n + m))`.
   I opened `LinearRecurrence` and `IsSolution` in Mathlib.Algebra.LinearRecurrence.
   The latter is `∀ n, u (n + E.order) = ∑ i, E.coeffs i * u (n + i)`.
   Thus hrec says c((n+d)+m) = sum_i (-a_i)*c((n+i)+m), equivalently
   c(N+d)+sum_i a_i*c(N+i)=0 for every N >= m. Take N=n+m in one direction,
   n=N-m in the other. Associativity and commutativity of natural-number addition
   account for the index order. Verdict: exact, including the sign; this is precisely
   the dependency's recorded `mathlib_match.how`, not a private recurrence predicate.
6. R_j=(c_(j+s))_(s>=0) in the coordinatewise sequence module: each row is written
   `fun s : ℕ ↦ c (j + s)` in the existing module `ℕ → K`.
   Verdict: exact; the recorded `Submodule` notion applies to this pointwise module.
7. Every R_j lies in the span of R_0,...,R_(m+d-1): the first conjunct is `∀ j : ℕ`,
   membership of that row in `Submodule.span K (Set.range (fun i : Fin (m + d) ↦
   fun s : ℕ ↦ c (i.val + s)))`. Verdict: exact, including the last index and all j.
8. V is the subspace generated by all shifts: both remaining conjuncts use exactly
   `Submodule.span K (Set.range (fun j : ℕ ↦ fun s : ℕ ↦ c (j + s))))`.
   Verdict: exact; this direct expression uses the recorded span, without a new
   definition or an arbitrary subspace hypothesis.
9. V is finite-dimensional: the second conjunct is `FiniteDimensional K` of that V.
   I opened its abbreviation to `Module.Finite`, and `Submodule.FG`, which means
   generation by a finite family. Verdict: exact.
10. dim_K V <= m+d: the third conjunct is `Module.finrank K` of that same V, bounded
    by `m + d`. I opened the recorded finrank definition and its dimension convention.
    Verdict: exact. The finite-dimensionality conjunct prevents the convention for
    infinite rank from making this conclusion weaker. The assumptions all precede the
    conclusions and the universal row index stays inside the first conjunct.

I also checked `Submodule.span` is the intersection of all submodules containing its
set of generators. The two proof imports expose the recorded signatures
`exists_linearIndependent'` (injective reindexing, equal spans, linear independence)
and `finrank_span_eq_card` (finrank of an independent finite family equals its index
cardinality). The field and finite index family meet their assumptions. The theorem's
proof docstring gives the node's four steps in order: coordinate recurrence; strong
induction into the initial span; equality of the initial and full spans and finite
spanning; independent subfamily and cardinality bound. The sole proof is `by sorry`.
There are no definitions, hidden data, auxiliary theorems, private copies, file-local
instances or notations, or extra unbound variables. Module and theorem docstrings name
the source place and the exact blueprint id. No new node or dependency module needs
review under H12/H13 because none is delivered or needed.

Edge cases checked independently:

- m=0 gives the first d shifts and recurrence at every nonnegative index; d=1 gives
  exactly m+1 initial shifts. d=0 is excluded by the source, not silently excluded by
  an API limitation. Since m+d >= 1, there is no admissible empty initial index family.
- The zero sequence gives the zero submodule and finrank zero. Zero and repeated
  generators, nonminimal recurrence order, and a_0=0 are all permitted.
- For m=0, d=1, a_0=0, c_0 is arbitrary and later coefficients vanish. The initial
  impulse R_0 is retained, so the statement does not accidentally force c_0=0.
- For m=1, d=1, a_0=-1 over the rationals and c=(5,1,1,...), R_0 and R_1 are
  independent, giving dimension 2=m+d. This checks the exceptional prefix and the
  necessity of the m contribution.
- Positive characteristic (including characteristic two), arbitrary field universe u,
  and the zero vector space are covered. There is no scheme or empty-scheme parameter.

Independent searches used different wording from the worker:

- `msearch.py Q18 lem-weil-linear-recurrence-shift-span leanfinder` with query
  "The vector space generated by all translates of an eventually linearly recurrent
  sequence is generated by the initial translates with dimension at most the threshold
  plus the order" returned eight recurrence declarations: solSpace, solSpace_rank,
  toInit, is_sol_iff_mem_solSpace, order, mkSol, IsSolution, and is_sol_mkSol.
  Their signatures do not supply the eventual initial-span containment and bound.
- The Loogle query `LinearRecurrence, Submodule.span` returned zero hits.
- LeanSearch for "All translates of an eventually linearly recurrent sequence lie in
  a finite initial translate span with a numerical dimension bound" returned eight
  hits, including IsSolution, tupleSucc, span_finset and an affine finite-span lemma,
  with the other hits about semilinear sets. None states this node.
- `rg` searches for `shiftSpan|shift_span|linear.recurrence|LinearRecurrence` across
  upstream WeilConjectures and the shared lean/Sheaf identified the upstream
  ZetaLinearAlgebra files ShiftSpan, RationalityCriterion, Hankel and IntegralRecurrence,
  and the project's RingTheory/RationalSeriesLinearRecurrence. I opened the relevant
  declarations: the project's theorem goes from a rational series to a recurrence,
  rather than from a recurrence to its shift-span containment and dimension bound.
- I read the definitions seqShift and shiftSpan and the complete relevant theorem
  signatures in upstream ShiftSpan and RationalityCriterion. The two closest theorems,
  `finiteDimensional_shiftSpan_of_recurrence` and
  `finiteDimensional_shiftSpan_of_forall_add_eq_zero`, conclude only finite-dimensionality.
  In particular the latter's docstring and proof mention the containment, but its type
  does not export it or the numerical bound. It is not an exact existing attachment.
  Writing the spans with `Submodule.span` introduces no duplicate shiftSpan definition.
- Direct searches in Mathlib's LinearRecurrence module found IsSolution and solSpace_rank
  but no shift-span theorem. Exact searches for `shift_span_bound` and the blueprint id
  in Mathlib, upstream WeilConjectures, shared lean/Sheaf and the upstream name index
  found no declaration collision or existing complete statement.

Mismatches and changes: none in the Lean statement or node. The worker's statement says
exactly what the node and source say. I preserved both files and appended this independent
reading to the report. I checked byte-for-byte that `lean.statement` equals the theorem
signature before `:=`, that only `lean` differs from the shared node, and that every Lean
line has at most 100 characters. The compilation and delivery checks follow below.

Second-reader validation: `scompile.py Q18 lem-weil-linear-recurrence-shift-span` on the
sole delivered module succeeded with exit code 0. The sandbox form compiled in 1.2 s
and the library-module form in 1.3 s; both emitted no errors or warnings.
