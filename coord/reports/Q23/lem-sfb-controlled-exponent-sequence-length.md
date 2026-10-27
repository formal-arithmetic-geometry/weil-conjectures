## Worker report

The module `Sheaf.Order.ControlledExponentSequenceLength` states
`Order.exists_bound_length_of_controlled_bad_exponent_sequence`. Its sole theorem
has proof `sorry`; it defines no new notion. The accepted natural-language
statement, dependencies, proof and all stage-1 review fields are unchanged.

The former worker's BLOCKED ending concerned reopening the stage-1 split. The
current node is reviewed stage 1, has no Lean record, and occurs in
`coord/queue.tsv` as stage 2. The explicit stage handoff in
`coord/brief-stage2.md` section 0 therefore applies: this delivery records its
Lean statement without resplitting it. There is no released repair note.

Clause-by-clause correspondence:

- Every integer `r >= 0` is represented by `(r : ℕ)`; no dimension is excluded.
- Every function from natural numbers to natural numbers is `(h : ℕ → ℕ)`;
  there is no monotonicity, positivity or computability assumption.
- A bound depending only on `r,h` is `∃ L : ℕ` outside the quantifiers for
  `n` and `α`. The statement asserts existence, without an explicit formula.
- An arbitrary length is `∀ (n : ℕ)` and its sequence of exponent tuples is
  `α : Fin n → Fin r → ℕ`. `Fin n` is exactly the finite set of positions
  `0,...,n-1`, and `Fin r` relabels the coordinates `1,...,r` without changing
  the vectors or their coordinatewise order. These are canonical finite types,
  with Mathlib's finiteness in the sense of def-sfb-finite-infinite-set.
- The coordinate-sum control at every position is
  `∀ i : Fin n, (∑ a : Fin r, α i a) ≤ h i.val`.
- For each earlier and later position, a strictly decreasing coordinate is
  `∀ i j : Fin n, i < j → ∃ a : Fin r, α j a < α i a`.
  Reversing the operands expresses the node's `α i a > α j a` exactly.
  In natural-number coordinates this is equivalent to saying that the earlier
  vector is not coordinatewise at most the later vector; the explanatory
  sentence of the node is therefore already expressed by this condition.
- The conclusion is `n ≤ L`. No extraneous conjunct or bound is included.

Dependency declarations inspected and used:

- Statement dependency def-sfb-finite-infinite-set is a Mathlib leaf:
  `Set.Finite` and `Set.Infinite` in `Mathlib.Data.Finite.Defs`. Its full recorded
  definition says that the subtype is finite; `Set.Infinite` is its negation.
  The module publicly imports this file. No private finiteness predicate is
  introduced, and `Fin n`/`Fin r` use Mathlib's existing finite-index types.
- Proof dependency lem-trf-cofiltered-finite-sets-section is a Mathlib leaf:
  `nonempty_sections_of_finite_cofiltered_system` in
  `Mathlib.CategoryTheory.CofilteredSystem`. Its full signature permits separate
  index/object/hom universes, assumes `IsCofilteredOrEmpty`, and finite nonempty
  values, and concludes `F.sections.Nonempty`; it needs no surjectivity.
- Proof dependency lem-trf-dickson-exponent-sequences is a Mathlib leaf:
  `Pi.wellQuasiOrderedLE`, `wellQuasiOrdered_le`, and
  `WellQuasiOrderedLE.finite_of_isAntichain` in `Mathlib.Order.WellQuasiOrder`.
  Read their signatures and the definition `WellQuasiOrdered`. The Pi instance
  applies to `Fin r → ℕ`, including `r = 0`. The sequence clause, rather than
  the antichain clause, is used in the plan.
- `Mathlib.Algebra.BigOperators.Fin` publicly supplies the sum over coordinates.
  The two proof-dependency imports are plain imports, as required for the plan.

The docstring follows all four accepted proof steps: finite prefix sets,
unbounded lengths giving nonempty prefixes and the cofiltered restriction
diagram, compatible sections giving an infinite bad sequence, and Dickson's
contradiction. The Dube theorem is explicitly identified only as surrounding
context; this combinatorial argument is agent supplied, as the node records.

Edge cases checked before writing:

- `r = 0`: the coordinate sum is empty (zero) and the coordinate existential
  is false for any pair of positions. Hence admissible sequences have length
  at most one; `L = 1` works. No nonempty-coordinate assumption was added.
- `n = 0`: all hypotheses about positions are vacuous and `0 ≤ L` holds.
- `h 0 = 0`: any first tuple has every coordinate zero, so there is no later
  term satisfying the strict-coordinate condition; length is at most one.
- Zeros later in `h` are allowed. In dimension one, `h 0 = 1`, `h 1 = 0`
  permits the length-two sequence `(1),(0)`, so this case was not accidentally
  discarded or subjected to monotonicity.
- Repeated vectors are forbidden at distinct increasing positions, precisely
  as in the node. There is no restriction on unused values of `h`.
- All objects are built from natural numbers and finite types; the statement
  requires no universe parameters or auto-bound implicit variables.

Searches for an exact existing statement (all run using msearch.py for Q23 and
this item, plus read-only project searches):

1. LeanFinder: "For every function h from natural numbers to natural numbers
   and dimension r, there is a uniform length bound for finite bad sequences
   of natural number vectors whose coordinate sums at position i are bounded
   by h i". Eight hits: finite-dimensional relation-series bounds and minimal
   bad-sequence declarations; none is this controlled length theorem. The
   relation-series bounds assume finite dimensionality, the missing argument.
2. Loogle: `WellQuasiOrdered, List`. Successful search, zero hits.
3. Mathlib grep: `IsBadSeq|controlled|length.*bound` in `Order`.
   Six hits, in KrullDimension and WellFoundedSet, with no controlled finite
   sequence bound. The bad-sequence predicate itself concerns infinite
   sequences and does not state the desired uniform finite-length bound.
4. LeanSearch: "Uniform bound on lengths of finite bad sequences of natural
   number vectors whose coordinate sum at position i is bounded by a
   prescribed function h i". Eight hits, chiefly bad/minimal-bad-sequence
   definitions, sequence termination and relation-series finite dimensionality;
   no exact declaration.
5. `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
   `controlled.*[Ee]xponent|[Ee]xponent.*[Ss]equence|[Bb]ad.*[Ss]equence|controlled.*[Dd]ickson|controlled.*length`:
   only unrelated trace-energy and etale/Kummer exponent-sequence text.
   `grep -rn` for the exact blueprint id in `lean/WeilConjectures` found none.
6. `rg` for `exists_bound_length_of_controlled_bad_exponent_sequence` and
   `controlled_bad_exponent` in Mathlib, WeilConjectures, Sheaf and
   `dag/lean_names_upstream.json` found no declaration-name collision.

No statement correction, new node, dependency repair or statement dispute is
needed. Compilation and delivery validation use the prescribed server wrappers.

## Second reading by Q23

A separate rereading by this worker compared the saved module with the complete
node after writing it; no second agent was started, in accordance with the
explicit dispatcher instruction. The maintainer's independent review remains
the independent reading of the delivery.

The rereading checked that `∃ L` precedes both sequence quantifiers, the sum is
indexed over all `Fin r`, the bound uses the original index `i.val`, and the
strict inequality has the earlier value on the right. `i < j` on `Fin n` is
exactly the order of the positions. The two stated conditions are implications
to `n ≤ L`, with no implicit positivity, monotonicity or nonemptiness assumption.
Dimension zero, the empty sequence, and bounds taking zero are all included.
All statement and proof dependencies have the imports described above, and the
single theorem's docstring supplies the full accepted proof plan. There are no
helper definitions, hidden hypotheses, private notation or auxiliary theorems.
No mismatch was found and no mathematical change was made during this rereading.
