## Worker report

The delivery states `Set.exists_disjoint_cubic_cocycle_integral` in
`Sheaf.Combinatorics.DisjointCubicCocycleIntegration`. Its only proof is `sorry`;
no definitions, helper lemmas, dependency repairs, or new nodes are introduced.
The accepted stage-1 split and every original node field are preserved; only
`lean` is added. The inherited BLOCKED ending concerned a stage-1 unchanged-split
rejection. The current `coord/queue.tsv` assigns the item to stage 2, its current
node has no Lean record, and there is no released repair note for this item.

Source read: the entire item (including all four proof steps), its sole statement
dependency `def-sfb-finite-infinite-set`, the two-cocycle proof dependency, and the
latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/` file
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3). The blueprint does
not assert this combinatorial auxiliary. The declaration's docstring explicitly
attributes it to the agent-written DAG argument and does not attribute it to an
unavailable Moret–Bailly original. The four proof steps are included in full
mathematical detail in the docstring.

Clause and hypothesis correspondence:

- A finite set E: `{ι : Type u} (E : Set ι) (hE : E.Finite)`. This uses precisely
  `Set.Finite`, the statement dependency's recorded Mathlib declaration. The
  ambient set need not be finite, inhabited, or decidably equal.
- An arbitrary commutative multiplicative group A: `{A : Type v} [CommGroup A]`.
  This supplies exactly the group operations, identity, inverses and their laws;
  there is no divisibility, torsion, field, or characteristic assumption.
- Subsets of E, including all its subsets: `Set E` (sets of elements of the
  subtype E). This is the canonical power set of E, equivalent to ambient subsets
  contained in E, without making callers carry separate containment proofs.
- A value for every ordered pairwise disjoint triple:
  `t : (U V W : Set E) → Disjoint U V → Disjoint U W → Disjoint V W → A`.
  No values at intersecting triples are required. Proof irrelevance ensures the
  value does not depend on the witnesses of disjointness.
- Invariance under all permutations: `hsym` states invariance under exchanging
  the first two arguments and under exchanging the last two. These adjacent
  transpositions generate all six permutations, so this is equivalent to full
  symmetry on the same domain. The disjointness arguments are reordered using
  `Disjoint.symm`; repeated sets, including repeated empty sets, remain allowed.
- Value 1 when any argument is empty: `hempty` has exactly the disjunction
  `U = ∅ ∨ V = ∅ ∨ W = ∅`, on each admissible triple.
- Four pairwise disjoint blocks: `hcocycle` quantifies over `U V W Z` and all six
  pairwise disjointness witnesses. Its displayed equation is literally
  `t U V Z * t (U ∪ V) W Z = t V W Z * t U (V ∪ W) Z`, with the required
  witnesses supplied by Mathlib's `Disjoint.sup_left` and `Disjoint.sup_right`.
- Existence of c on the power set: `∃ c : Set E → A`.
- Normalization on all subsets of size at most two:
  `∀ B : Set E, B.ncard ≤ 2 → c B = 1`. Every such B is finite since hE says the
  subtype E is finite; thus Mathlib's infinite-set junk value for ncard is never
  involved. No additional finiteness assumption on B is imposed.
- Cubic formula for every pairwise disjoint triple: the final quantified clause
  has the same three witnesses as t. The numerator is
  `c (U ∪ V ∪ W) * c U * c V * c W`; the denominator is
  `c (U ∪ V) * c (U ∪ W) * c (V ∪ W)`. Division is the group division operation,
  exactly multiplication by inverses as in the node.

Dependency declarations read and used:

- `def-sfb-finite-infinite-set`: its `mathlib_match` is `Set.Finite` in
  `Mathlib.Data.Finite.Defs`; the full definition and adjacent `Set.Infinite`
  documentation were read. It is publicly available through
  `Mathlib.Data.Set.Card`.
- Supporting Mathlib interfaces are `Set.ncard` (`Mathlib.Data.Set.Card`),
  `Disjoint`, `Disjoint.symm`, `Disjoint.sup_left`, `Disjoint.sup_right`
  (`Mathlib.Order.Disjoint`, through `Mathlib.Data.Set.Disjoint`), and `CommGroup`
  (`Mathlib.Algebra.Group.Defs`). Their definitions/signatures were inspected.
- Proof dependency `lem-sfb-disjoint-symmetric-two-cocycle-integration` has neither
  a Lean record nor a Mathlib match in the current DAG, so there is no stated
  module to import. Its statement was read and its intended use is recorded in
  proof step 2 of the theorem docstring. It is not needed to type this statement.

Edge cases checked before writing: E empty, singleton and two-element E, and all
triples containing empty blocks. In these cases c identically 1 works whenever
|E| ≤ 2, since an admissible triple cannot have three nonempty blocks. For a
three-element E, c on the full set can take the prescribed singleton-triple
value without extracting a root. For larger E the source's induction removes a
point and uses a two-cocycle, again without roots. Arbitrary torsion groups,
the trivial group, empty four-blocks, and independent universes u and v are
included. The finiteness assumption is substantive: it cannot be inferred for
an arbitrary ambient subset E. No disputed statement or node fault was found.

Searches for an existing declaration:

- `msearch.py ... leanfinder` with query: "A symmetric normalized cubic cocycle
  on pairwise disjoint subsets of a finite set is the third multiplicative
  difference of a function on its power set". Eight hits, mostly group
  cohomology: `groupCohomology.IsMulCoboundary₂`, `d₂₃`, `IsCocycle₂`,
  `IsMulCocycle₂`, `IsMulCocycle₁`, `IsCocycle₁`, `IsCoboundary₂`, and
  `d₂₃_hom_apply`. None states this finite partial-union integration theorem.
  In particular, the signatures and docstrings of `IsMulCocycle₂` and
  `IsMulCoboundary₂` were read in `GroupCohomology/LowDegree.lean`: these are
  predicates for a total multiplication and action, not integration results
  on disjoint triples of subsets.
- `msearch.py ... loogle '"Disjoint", "cocycle"'`: zero hits.
- `msearch.py ... grep
  '(cocycle.*[Dd]isjoint|[Dd]isjoint.*cocycle|[Cc]ubical)'`: zero Mathlib hits.
- `rg` with `(cocycle.*[Dd]isjoint|[Dd]isjoint.*cocycle|disjointCubic|disjoint_cubic)`
  over `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  two unrelated Picard gluing comments in Sheaf; no matching declaration.
- `grep -rn 'lem-sfb-disjoint-cubic-cocycle-integration'
  lean/WeilConjectures`: no hits.
- Exact-name `rg` for `exists_disjoint_cubic_cocycle_integral` across Mathlib,
  WeilConjectures, Sheaf and the upstream name index: no hits.

Validation: prescribed `scompile.py NZ lem-sfb-disjoint-cubic-cocycle-integration`
compiled the delivered file in sandbox and library module modes successfully
(4.5 s and 2.8 s), with no unexpected warnings or errors. The file explicitly
sets `autoImplicit false`; all variables and universes are bound. Every line is
at most 100 characters. Only the named theorem has a postponed proof.

## Second reading by NZ

The worker re-read the completed file against the node clause by clause after
compilation. This is a self-audit; the maintainer supplies the independent
reading, as specified in this dispatcher brief. No separate agents were started.
The domain requires exactly all three disjointness relations; the symmetry
conjunction uses the two adjacent swaps, not an extra cyclic or sign condition;
the four-block equation's four t calls have the original order and unions;
the normalization threshold is two; and the quotient has all four numerator
and three denominator factors. The finite-set and coefficient universes are
independent. No mismatch or statement correction was needed.
