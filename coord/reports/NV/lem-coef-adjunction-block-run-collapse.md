## Worker report

The delivery states `CategoryTheory.AdjunctionWord.block_run_collapse` in
`Sheaf.CategoryTheory.AdjunctionBlockRunCollapse`, with one `sorry` and no proved
theorems. Its thirteen helper definitions give real data or explicit predicates
for the notions introduced inline in this node. They introduce no independent
notion requiring a new DAG node. All fourteen declarations are in `lean.declarations`.
Only the item's `lean` record changes; its statement, dependencies and proof are unchanged.

Hypothesis and clause correspondence (names below are in `CategoryTheory.AdjunctionWord`):

| Node text | Lean rendering |
| --- | --- |
| Zero-based finite simplex/coordinate convention | Natural coordinates with `∀ j ∈ x, j ≤ r + 1` inside `IsWord`, using the convention of the imported `Sheaf.CategoryTheory.EnhancedDiagramsCones` |
| `r ≥ 0` | `r : ℕ` |
| `p,q ∈ {-,+}` | `p q : Bool`, with `false = -`, `true = +` |
| Nonempty finite strings | `x : List ℕ`; `head? = some ...` and `getLast? = some ...` in `IsWord` force nonemptiness |
| Both prescribed endpoints | `head?` equals `some (if p then r + 1 else 0)`; `getLast?` equals `some (if q then r + 1 else 0)` |
| Strict successive inequalities, alternating from the stated sign | `IsAlternating p x`, comparing consecutive `getD` values for every `i + 1 < x.length`; upwards at even `i` for minus and odd `i` for plus |
| `0 ≤ h ≤ r` | `h : ℕ` and `hh : h ≤ r` |
| Labels `χ_h(j) = 0` below/equal to `h`, and `1` above | The decidable predicate `j ≤ h`; `thresholdRuns` merges adjacent letters exactly when these truth values agree |
| Every maximal constant-label run has odd length | First conjunct: `∀ b ∈ thresholdRuns h x, Odd b.length` |
| `C_h(j) = min(j,h+1)` | `lowerRestriction h j := min j (h + 1)` |
| `D_h(j) = max(j-h,0)` | `upperRestriction h j := j - h`, using natural truncated subtraction |
| Both maps applied entrywise | `x.map (lowerRestriction h)` and `x.map (upperRestriction h)` |
| Deterministic leftmost-pair reduction `R` | `eraseFirstPair` scans from the left, stops at the first adjacent equal-value pair, and removes exactly those two letters; `reduceWithTraceAux` repeats this with initial-length fuel; `reduce` returns the survivors |
| First reduction collapses each one-run to `h+1`, and keeps every zero-run verbatim | Second conjunct, the equality with `(thresholdRuns h x).flatMap (lowerRun h)` |
| Second reduction collapses each zero-run to `0`, and shifts every entry of each one-run by `-h` | Third conjunct, the equality with `(thresholdRuns h x).flatMap (upperRun h)` |
| No reduction crosses a run | Fourth and fifth conjuncts: `NoCrossRunDeletion` for both maps; every actual deleted pair has the same original run number |
| Surviving run order is unchanged | Both `flatMap` formulas keep the ordered original run list and replace each run by precisely its prescribed nonempty output |
| Alternating directions unchanged | Sixth and seventh conjuncts: `IsAlternating p` for both reduced words, retaining the original starting sign |

The reduction uses initial word length as fuel: a successful step removes two entries,
so this cannot truncate a genuine reduction. When there is no equal pair the procedure
stops immediately. `reduceWithTrace` uses the same function both for plain letters
and for run-tagged letters, comparing only their numerical values. `taggedRestriction`
tags by the original run's ordinal number, rather than by its binary label, so the
no-crossing assertions also exclude cancellation between distinct runs of the same label.
The guarded `getD` calls in `IsAlternating` always access in-range positions. Runs
are computed by structural recursion from the actual input word; no arbitrary run
partition, chosen reduction, or assumed comparison is used.

Dependency read and used: `def-cbc-enhanced-diagrams-cones`, module
`Sheaf.CategoryTheory.EnhancedDiagramsCones`, main recorded declaration
`SSet.Enhanced.coneCategory` and its full recorded interface. I read the whole module,
including the full cone signature/docstring, the Mathlib simplex convention and the
finite-ordinal helper `SSet.Enhanced.appendLast`. The present node needs its zero-based
coordinate convention only; it has no cone, functor or simplicial-map argument to which
`coneCategory` would apply. Its existing interface is usable and is imported unchanged.
`Odd` is Mathlib's existing predicate, defined in `Mathlib.Algebra.Ring.Parity` by
`∃ k, a = 2 * k + 1`; lists, `getD`, `head?`, `getLast?`, `zipIdx`, `flatMap`, natural
ordering, minimum and truncated subtraction use the existing Lean/Mathlib notions.

Source checked: [Riehl--Verity, Proposition 3.2.2 proof](https://emilyriehl.github.io/files/adjunctions.pdf),
printed pp. 824--825, PDF pages 22--23 (zero-based).
The paper explains splicing and recovering both restrictions by deleting lines and
reducing, and delegates the string calculation. The node expands that calculation;
the docstring retains all four elementary proof steps, including the last-run endpoint
direction supplied by `q`. No source or node fault was found.

Edge cases checked: the empty list fails `IsWord`; a singleton is admitted exactly
at the appropriate extreme with equal endpoint signs and has one odd run; both
starting signs and both final signs are admitted. For `r = 0` there is still the
two-vertex alphabet `{0,1}`, and `h = 0`. For general `r`, both `h = 0` and `h = r`
are included. First, last, interior, singleton and whole-word runs are covered.
An exhaustive Python evaluation over all valid words of length at most eight for
`0 ≤ r ≤ 3`, all signs and thresholds checked 10,602 `(r,p,q,x,h)` cases: odd run
lengths, both exact formulas, both actual deletion traces, both direction conditions,
and equality of tagged versus untagged reductions all passed. This is an edge-case
check, not a Lean proof.

Searches for an existing declaration:

- `msearch.py leanfinder`: `Odd maximal threshold runs of a strictly alternating
  finite word, deleting adjacent equal pairs after interval restriction`. Eight
  hits: six Coxeter declarations (including `CoxeterSystem.alternatingWord` and
  five facts about it), plus `DyckWord.outsidePart` and `DyckWord.drop`.
  These concern two-letter words or Dyck paths, not threshold runs of ordered coordinates.
- `msearch.py leansearch`: `Deleting adjacent equal pairs from a list deterministically
  at the leftmost equal pair`. Eight hits concerning `List.dedup`, `List.destutter`,
  dedup lemmas, `kerase_cons_eq`, and `Perm.eraseIdx_of_getElem?_eq`; no exact match.
  Read `Mathlib.Data.List.Defs` at `dedup` and `destutter`: dedup removes duplicates,
  and destutter keeps one entry when a relation fails; neither deletes both letters
  of an equal pair and restarts at the leftmost position.
- `msearch.py loogle`: `List, List.Chain, List.groupBy`, zero hits and unknown
  identifier `List.Chain`. A follow-up `"groupBy"` returned `Array.groupByKey` and
  `List.groupByKey`, which combine all entries with a key, including nonadjacent
  entries; they are not consecutive maximal runs.
- `msearch.py grep`: `leftmost|adjacent.*equal|groupBy`, subdirectory `Data/List`,
  zero hits. Direct `rg` of Mathlib located `FreeGroup.reduce`; I read its definition
  in `Mathlib/GroupTheory/FreeGroup/Reduce.lean`: it cancels equal generators with
  opposite Boolean signs and recurses from the right, so it is not this operation.
- `rg` of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `lean/Sheaf`
  for `leftmost`, `squiggle`, `Squiggle`, `blockRun`, alternating words, and the helper
  names found only unrelated Cech, hammock, signed-word, and coproduct constructions.
  The exact node-id search in upstream source had no match. The upstream declaration
  inventory also had none of the new declaration names.
- DAG search found the related `lem-coef-adjunction-squiggle-normal-form` and
  `lem-coef-adjunction-two-block-splicing` nodes, whose prose uses this calculation
  but provides no recorded Lean word/reduction definition to reuse. No duplicate
  threshold-run or deterministic equal-pair reduction declaration was found.

Compilation uses only the prescribed `scompile.py` wrapper. Both the sandbox and
library-path checks passed cleanly (6.8 seconds and 16.2 seconds respectively).
All variables and the helper universe are explicitly bound with `autoImplicit false`.
The final delivery additionally runs the wrapper's compile and server preflight
through `deliver2.py`.

## Second reading by NV

This is the author's second pass under the dispatcher's direct-delivery instructions;
no second agent was started. The maintainer performs the independent review.
I reread the node against the complete file and checked every table row above.
In particular: both endpoint conditions remain in `IsWord`; the final-run proof uses
`q`; reduction erases pairs rather than deduplicating; run tags distinguish separate
runs with the same label; both run formulas retain every entry of uncollapsed runs;
and both outputs retain the starting inequality parity. The helper data contain no
`sorry`, and the only postponed theorem is exactly the item's named theorem.
The compile pass corrected an import path (`Mathlib.Data.Nat.Parity` is not a module)
and qualified `_root_.Prod.snd` to avoid the categorical product-functor name.
These changes do not alter the mathematical statement. No extra hypotheses,
strengthening, omitted clause, new dependency or statement correction was needed.
