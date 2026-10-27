## Worker report

The module `Sheaf.RingTheory.InvariantCoordinateTransfiniteFiltration` states
`DirectSum.exists_invariant_coordinate_transfinite_filtration`. Its only proof is
`sorry`; it introduces no definitions. The accepted stage-1 split is preserved, and
the node copy changes only `lean`. The inherited unchanged-node rejection concerned
stage 1; the current queue assigns this unstated node to stage 2, as clarified in
`coord/brief-stage2.md` section 0. There is no released repair note for this item.

Source read: Stacks Project `algebra.tex`, Tag 058X,
`theorem-kaplansky-direct-sum`, lines 20465–20575, especially the transfinite
recursion and exhaustion paragraphs. This node isolates that construction once
countable invariant blocks have already been specified. Countable generation is
used in the source to produce those blocks, and is not needed in this node.

Hypotheses and clauses, in statement order:

- `R : Type u` with `[CommRing R]` is the commutative ring. `J : Type v`,
  `N : J → Type w`, `[∀ j, AddCommGroup (N j)]` and `[∀ j, Module R (N j)]`
  give an arbitrary indexed family of modules. All three universes are explicit
  and independent. No finiteness, generation or nonzero assumption is imposed.
- `DirectSum J N` is exactly the finite-support module M. Every occurrence of
  `coordinateSubmodule R J N A` uses the recorded dependency's submodule M_A,
  whose carrier requires every coordinate outside A to vanish.
- `f : (DirectSum J N) →ₗ[R] DirectSum J N` is the given R-linear endomorphism.
- `D : J → Set J` supplies the specified blocks, `hD_countable` asserts every
  block is at most countable, and `hD_self` asserts `j ∈ D j`.
- `hD_invariant` says that every x in M_(D j) has f x in that same submodule,
  exactly the assumed inclusion f(M_(D j)) ⊆ M_(D j).
- The existential `κ : Ordinal.{v}` is a set ordinal. `η : Set.Iio κ ≃ J`
  supplies the bijective enumeration, including the empty enumeration.
- `A : Set.Iic κ → Set J` includes every stage α ≤ κ. `Monotone A` says
  the coordinate subsets increase.
- `A ⟨0, ...⟩ = ∅` and `A ⟨κ, ...⟩ = Set.univ` are the two subset endpoints.
  The proof terms only certify that 0 and κ lie in the index interval.
- For each `μ : Set.Iic κ`, `Order.IsSuccLimit μ.val` means a nonzero limit
  ordinal; the first union equality says A_μ = ⋃_(β < μ) A_β.
- For each ordinal α < κ, the first successor implication gives stationarity
  when A_α is all of J. The second implication applies otherwise and supplies
  `γ : Set.Iio κ` with `η γ ∉ A_α`; its universal clause puts `η δ` in A_α
  for every δ < γ. Thus γ is precisely the least missing index, and the
  displayed successor equality is A_(α+1) = A_α ∪ D_(η γ).
- The next quantified clause states that every successor difference is
  `Set.Countable`, including stationary successors.
- `∀ (α : Set.Iic κ) (β : Set.Iio κ), β.val < α.val → η β ∈ A α`
  states η({β : β < α}) ⊆ A_α at every stage, including α = κ.
- The next two equalities identify the initial coordinate submodule with `⊥`
  and the terminal coordinate submodule with `⊤`, namely 0 and M.
- The quantified membership implication for every α asserts f(M_(A_α)) ⊆ M_(A_α).
- The final equality coerces each coordinate submodule to its underlying set
  and takes the actual union over β < μ at every nonzero limit μ ≤ κ. This
  states the node's union equality, rather than replacing it by a lattice
  supremum. Finite support and monotonicity justify that union in the proof.
- The absence of any countable-generation binder renders the last sentence
  of the node. Nothing requires f to be idempotent or the N_j to be nonzero.

Dependency declarations read and used:

- `Sheaf.RingTheory.CoordinateSubmodule`, `DirectSum.coordinateSubmodule`:
  full definition and docstring read in `lean/Sheaf/RingTheory/CoordinateSubmodule.lean`.
  Its actual carrier is `{x | ∀ j, j ∉ A → x j = 0}`. It publicly imports
  `Mathlib.Algebra.DirectSum.Module`, supplying the other statement dependency.
- `Mathlib.Algebra.DirectSum.Basic`, `DirectSum`, is the dependent finite-support
  function type; the signature/docstring at lines 35–40 were read.
  `Mathlib.Algebra.DirectSum.Module`, the module instance at lines 35–43 and
  canonical inclusion `DirectSum.lof` at lines 75–84 were read.
- The proof-only imports are `Mathlib.SetTheory.Cardinal.Order` for
  `exists_wellFoundedLT` (lines 549–553, full signature/docstring read) and
  `Mathlib.Order.RelClasses` for `WellFoundedLT.fix`, `fix_eq`, and `induction`
  (lines 285–311, full signatures/docstrings read).
- `Mathlib.SetTheory.Ordinal.Basic`, `Ordinal.enum` (lines 466–490, signature
  and docstring read), is the recorded Mathlib match of the ordinal-enumeration
  proof dependency. That module also supplies the ordinal statement types.
- `Mathlib.Data.Set.Countable` supplies countability. `Order.IsSuccLimit` was
  read in `Mathlib.Order.SuccPred.Limit` lines 80–95: it excludes the minimal
  element and successors, exactly a nonzero limit for ordinals.

Edge cases checked mathematically before finalizing:

- For J empty take κ = 0 and the unique empty enumeration. The only A stage is
  empty = univ. Successor and nonzero-limit clauses are vacuous, and the empty
  direct sum has ⊥ = ⊤. No inhabitant of J is assumed.
- For all N_j = 0 and nonempty J the subsets must still exhaust J; the explicit
  enumeration-prefix clause ensures that zero coordinate modules cannot cause
  premature termination. No submodule equality is used as a substitute for A = J.
- Overlapping blocks and early exhaustion (for instance a countable J with
  D_j = J) are admitted; later stages are stationary and have empty increments.
- Singleton blocks with f = 0 or f = id give the usual well-ordered coordinate
  filtration. Finite J has successor endpoints; an infinite limit endpoint is
  covered by the nonzero-limit clauses.
- At a limit, finite support lies in one earlier stage by a finite maximum;
  for empty support choose stage 0, which exists since the limit is nonzero.
  This validates both the actual submodule union and its invariance.
- The zero ring and arbitrary module/ring universes impose no extra restriction.
  Ordinal.{v} suffices by well-ordering a type in universe v; the interval subtype
  may live in the successor universe without constraining the module universe w.

Searches made (saved wrapper search records are in the sandbox's searches.jsonl):

- Inherited from the interrupted stage-2 turn: LeanSearch query
  "Transfinite continuous increasing filtration of a direct sum by invariant
  coordinate submodules with countable increments" returned eight hits, including
  `IsModuleFiltration`, measurable-space filtrations and ideal filtrations.
  Reading `Mathlib/RingTheory/FilteredAlgebra/Basic.lean` lines 85–110 confirms
  that `IsModuleFiltration` is a predicate on an existing graded filtration,
  not this existence theorem.
- Inherited LeanFinder query "Transfinite continuous increasing exhaustive
  filtration of coordinate submodules of a direct sum invariant under a linear
  endomorphism with prescribed countable blocks" returned eight hits on module
  filtration predicates, generalized eigenspaces, field embeddings and Hahn
  embeddings. None states the required coordinate recursion.
- Resumed LeanFinder query "An endomorphism of a direct sum of modules with
  prescribed countable invariant coordinate blocks admits an exhaustive
  continuous transfinite coordinate filtration" returned eight hits:
  Nobeling good-products lemmas, `Field.Emb.Cardinal.directed_filtration` and
  `iSup_filtration`, `Module.End.genEigenspace_directed`, Hahn embeddings and
  `LinearMap.trace_eq_zero_of_mapsTo_ne`. Their returned signatures concern
  Boolean cubes, field extensions, generalized eigenspaces, ordered modules or
  traces, respectively, and do not assert this filtration.
- Loogle `Ordinal, Monotone, Set.Countable` returned zero hits, both in the
  inherited search and the resumed search.
- Whole-Mathlib grep
  `[Ii]nvariant.*[Ff]iltration|[Cc]oordinate.*[Ff]iltration|[Cc]ountable.*[Ii]ncrement`
  returned zero hits, both in the inherited search and the resumed search.
- Ripgrep of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`
  for the item id, the proposed declaration name and invariant/coordinate
  filtration patterns found no declaration of this statement. Hits were
  representation filtrations, finite-free kernel filtrations, and the parent
  `ProjectiveKaplanskyDirectSummand` theorem, which proves a module decomposition
  and discusses this construction only in its proof docstring. It does not
  already expose the present theorem.

No new nodes, dependency repairs, statement corrections or mathematical disputes
were needed. All binders and universes are explicit; `autoImplicit` is disabled.
The saved module's reserved lambda binder was renamed to μ and ordinal endpoint
proofs were made explicit during compiler repair. The final module compiled in
both sandbox and library modes through `scompile.py` with no errors or warnings.
The full six-step natural-language proof is in the theorem docstring for stage 3.

## Second reading by Q153

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
