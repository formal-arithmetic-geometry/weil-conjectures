## Worker report

The module `Sheaf.Topology.OpenNormalQuotientFunctionsDense` states
`ContinuousMap.openNormalQuotientFunctions_dense`, with its whole proof `sorry`.
It introduces no definitions and changes only the item's `lean` record. The accepted
stage-1 statement, split and dependencies are preserved. The inherited rejection
concerned a stage-1 unchanged split; the present assignment is stage 2 and the current
node has no Lean record. There is no released repair note for this item.

The mathematical clauses are rendered as follows:

- The compact Hausdorff topological group is `K : Type u`, `[Group K]`,
  `[TopologicalSpace K]`, `[IsTopologicalGroup K]`, `[CompactSpace K]`, `[T2Space K]`.
- The open normal subgroup basis is the explicit hypothesis `h_basis`: for each
  `W : Set K`, `IsOpen W` and `(1 : K) ∈ W` imply the existence of
  `U : OpenNormalSubgroup K` with `(U : Set K) ⊆ W`. Thus it quantifies over exactly
  the open identity neighbourhoods in the statement.
- The coefficient field is `B : Type v` with `[NormedField B]`. This supplies its
  norm topology. No separate topology, completeness, nonarchimedean assumption,
  or nontrivial-norm assumption is imposed.
- `C(K, B)` is Mathlib's space of continuous maps. Its norm from
  `Mathlib.Topology.ContinuousMap.Compact` is the supremum norm: that file transfers
  the metric from bounded continuous functions and defines `norm f := dist f 0`.
- The first conjunct `TotallyDisconnectedSpace K` means every preconnected subset
  of the universal set is a subsingleton (see the class and
  `IsTotallyDisconnected` in `Mathlib.Topology.Connected.TotallyDisconnected`).
  This is equivalent to every connected subset having at most one point, including
  the empty-subset case.
- The second conjunct universally quantifies over `F : Type w` with
  `[TopologicalSpace F]`, `[DiscreteTopology F]`, `[Finite F]`, and `g : C(K, F)`.
  Its witnesses `U` and `b : K ⧸ U.toSubgroup → F` satisfy
  `∀ x : K, g x = b (QuotientGroup.mk x)`, precisely the asserted equality
  `g = b ∘ π_U`, by function extensionality. The function `b` has no algebraic
  restriction, as required.
- The third conjunct quantifies over every `f : C(K, B)` and `ε : ℝ` with `0 < ε`.
  It supplies an open normal `U`, a function `b : K ⧸ U.toSubgroup → B`, and
  `d : C(K, B)`, with `∀ x, d x = b (QuotientGroup.mk x)` and `‖f - d‖ < ε`.
  Bundling `d` as a continuous map supplies exactly the required continuity of
  the composite, without postulating continuity or a homomorphism property of `b`.
- The last conjunct is `Dense {d : C(K, B) | ∃ U b, ∀ x, d x = b (QuotientGroup.mk x)}`.
  This inline set is precisely `D`, using the actual canonical quotient projection.
  Density is for Mathlib's topology on compact-domain continuous maps, whose
  compatible metric and norm are the supremum metric and norm just described.
- The size convention is rendered by explicit universe levels `u v w` on the
  group, field and finite codomains. It imposes no equality of those universes.
  Every variable and universe is explicitly bound; there are no statement-local
  `let` terms, notation, private definitions or auxiliary instances.

Dependencies read and used:

- `def-weil-size-convention` is a convention record (`lean.module = null`,
  `lean.declaration = null`), so it supplies no module to import. Its statement
  is followed by the explicit universe polymorphism above.
- The proof dependency `lem-exc-coinduced-functions-open-stabilizer` is imported
  privately from `WeilConjectures.Topology.ContinuousOpenNormalStabilizer`.
  Its declaration `ProfiniteGrp.exists_openNormalSubgroup_right_invariant`
  takes `G : ProfiniteGrp.{u}`, any discrete `S : Type v`, and a continuous
  function `f : G → S`; it gives an open normal `U` with `f (x * a) = f x`
  for every `a ∈ U`. The full signature, docstring and proof were read. The
  docstring explains compactness, the subgroup basis, finite index and the
  intersection of conjugates. The item uses it after deriving total
  disconnectedness and packaging `K` as a profinite group, not as an extra
  profiniteness hypothesis.
- The Mathlib proof leaf `lem-sfb-profinite-finite-map-approximation` has
  `mathlib_match` (no `lean` record). Its recorded declaration
  `ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal` is imported
  privately from `Mathlib.Topology.Separation.DisjointCover`. The signature and
  docstring at lines 134–141, with the enclosing variables at lines 122–123,
  were read: for compact Hausdorff totally disconnected `X`, arbitrary topological
  `V`, `f : C(X,V)`, and `S ∈ nhdsSet (diagonal V)`, it produces `n`, `g : X → Fin n`,
  `h : Fin n → V`, continuity of `g`, and pointwise membership `(f x,h(g x)) ∈ S`.
  Thus it is exactly the node's finite-map approximation input.
- The public statement imports supply Mathlib's `OpenNormalSubgroup`,
  `OpenNormalSubgroup.toSubgroup`, `QuotientGroup.mk`,
  `TotallyDisconnectedSpace`, `ContinuousMap`, and its compact-domain norm.
  In particular `OpenNormalSubgroup` extends the open subgroup structure and
  supplies normality of `U.toSubgroup`; the quotient is the actual group quotient.

The proof docstring reproduces all four DAG proof steps: separating points by
clopen cosets; finiteness and discreteness of open quotients; right-invariance
and quotient factorization; then finite-map approximation with `ε / 2`, normal
quotient refinement and the supremum bound giving density. It names both proof
dependencies. I read the current blueprint `latest` direct-images proof,
paragraph (3), and Stacks `topology.tex`, `lemma-profinite-group` (Tag 0BR1).
As the node records, the blueprint provides the application context and the
DAG supplies the auxiliary topological argument; no new source claim is made.

Edge cases checked before writing:

- A group is inhabited by its identity; an empty group is not part of the
  informal assertion. The trivial group is allowed and the top subgroup works.
- Empty `F` is allowed: there is no continuous map from the inhabited group to
  it, so the universal map assertion is vacuous. No `[Nonempty F]` was added.
  Singleton `F`, all constant maps, and finite groups are included.
- Empty and singleton connected subsets are covered by Mathlib's subsingleton
  formulation. No connectedness or positive-dimension assumption occurs.
- The zero continuous map and arbitrary positive real `ε` are included; no
  approximation is asserted for nonpositive `ε`.
- A trivially normed field and an incomplete normed field are permitted by
  `[NormedField B]`. No scalar algebra or completeness instance is needed by
  the continuous-map supremum norm.
- Arbitrary cardinalities of `K` and the three independent universe levels are
  allowed. No countability, metrizability, second-countability or finite-generation
  assumption was introduced.

Searches performed (actual results):

- `msearch.py`, LeanFinder, query "Continuous functions on a compact group with a
  basis of open normal subgroups are dense in the supremum norm among functions
  factoring through open normal quotients": eight hits including
  `ProfiniteGrp.denseRange_toLimit`, quotient-image density, Fourier density and
  Stone–Weierstrass approximation. None states the combined assertion for an
  arbitrary normed field and the given subgroup-basis hypothesis.
- `msearch.py`, Loogle, query `ContinuousMap, OpenNormalSubgroup`: zero hits.
- `msearch.py`, grep of Mathlib `Topology`, query
  `dense.*[Ll]ocally[Cc]onstant|[Ll]ocally[Cc]onstant.*dense|[Oo]pen[Nn]ormal.*approxim`:
  zero hits.
- `msearch.py`, LeanSearch, query "Continuous functions on a compact group are
  uniformly approximated by functions factoring through finite open normal
  quotients when open normal subgroups form a neighbourhood basis": eight hits,
  including the real Stone–Weierstrass approximation theorems,
  `Subgroup.quotient_finite_of_isOpen`, quotient completeness and compact-uniform
  convergence facts. None gives this complete statement. The real approximation
  results cannot be specialized to an arbitrary normed field.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf`, for the node id,
  quotient-functions-density names, and the same density/locally-constant/open-normal
  patterns: no matching theorem; only unrelated constructible-sheaf generic-density
  hits occurred. `rg` for the chosen full declaration name in Mathlib and both
  project roots returned no declaration. Mathlib's finite-map approximation and
  the existing right-invariance theorem are retained as proof dependencies,
  rather than restated.

No statement correction, missing notion, unusable dependency, disputed statement,
new node or dependency module was required.

Validation: the prescribed `scompile.py` compiled the file on the server both
as a sandbox and as `Sheaf.Topology.OpenNormalQuotientFunctionsDense`, cleanly
(4.0 s and 3.3 s). All source lines are at most 100 characters. The node's
`lean.statement` is copied verbatim from the theorem signature.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
