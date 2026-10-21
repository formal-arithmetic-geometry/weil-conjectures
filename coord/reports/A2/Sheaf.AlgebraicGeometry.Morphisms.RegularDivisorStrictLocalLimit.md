## What changed

Completed the zero-hole retirement listed in `coord/retire-items.tsv`, row 2043.
Withdraw `Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit`
through `deleted.txt`, including its unused private small-colimit quotient helper.
The proved upstream `AlgebraicGeometry.Scheme.regular_divisor_strict_local_limit`
remains the sole owner. Its statement is identical modulo the unused existential
instance binder name `hH` versus `_`. A Lean example applies it at the complete
original signature, retaining every hypothesis and conclusion.

Reattach `lem-sbc-regular-divisor-strict-local-limit` to the upstream theorem with
its verbatim signature. Update only `lean`, `proof`, `proof_deps`, and `proof_origin`
to describe the actual full-colimit proof. No source-library file, public import,
statement, definition, attribute or proof is edited. The mathematical parent and
unit route remain intact.

The retirement inventory's former Sheaf consumer is already absent; the current
upstream `RootSplitCoverIndEtaleCharts` already imports and calls this upstream
theorem directly. Exact import and declaration-name scans of both roots and
quarantine find no additional consumer, and there is no related rework row.
No consumer adaptation is necessary. Change record:
`coord/changes/A2-retire-regular-divisor-strict-local-limit.md`.

Validation: the entire original signature is accepted by Lean, and
`#print axioms regular_divisor_strict_local_limit` lists only `propext`,
`Classical.choice`, and `Quot.sound`. The unused binder warning in that scratch
example is silenced locally without altering its signature. After server congestion,
`lcompile.py --all` compiled the unchanged upstream theorem and its sole consumer
individually in import order, exit 0, without warnings (0.1 seconds each).

## Proved and sorry left

Item baseline: 0 holes. Closed: 0. Added: 0. Split off: 0. Remaining: 0.
This is retirement of a proved duplicate, not a new mathematical proof.

The removed duplicate `AlgebraicGeometry.Scheme.regular_divisor_strict_local_limit`
is retained with the same signature in the upstream module. The removed private
`small_regular_divisor_quotient` is fully proved and no longer needed. The retained
upstream theorem and its consumer `root_split_cover_indEtale_charts` have no
textual `sorry`. No new declaration or node is introduced.

## No longer needed

Withdrawn module:
`Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictLocalLimit`.
There are zero current import edges to remove. Its five public statement imports
remain provided by the retained upstream owner. Its quotient, functoriality and
flatness proof imports likewise remain used by the retained upstream proof.
The duplicate's private helper and its small/full comparison are unnecessary.

The proof of this node no longer needs these dependencies:

- `lem-weil-pbc-strict-henselization-small-closed-fiber-comparison`, from
  `Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison`.
- `lem-weil-pbc-strict-henselization-local-structure`, from
  `Sheaf.AlgebraicGeometry.StrictHenselizationCompatibility`.
- `lem-weil-pbc-small-strict-henselization-ind-etale`, from
  `Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale`.

The full-colimit proof uses the upstream affine-chart ind-etale theorem,
`lem-weil-pbc-strict-henselization-affine-chart-ind-etale`, directly. These three
small-model modules have other users and are not withdrawn or claimed globally
pruned. No mathematical node is deleted. In particular, the sole DAG parent
`lem-sbc-root-split-cover-ind-etale-charts` still cites this node; its Lean
attachment already names the current upstream consumer. Quotient regularity,
functoriality and flatness remain needed. The unit `sk-prop-input-spreading`
keeps its statement and steps unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an open proof, but the queue assigns the
human-approved retirement of an already proved duplicate with zero holes. The
historical retirement inventory lists a Sheaf consumer already migrated upstream.
Its absence is not used to discard the mathematics: the upstream consumer and
the DAG parent both still need the exact retained theorem.

The later A3 quotient retirement had adapted the duplicate's internal proof to
the small-colimit model. That work is correct but redundant here: the existential
statement never prescribed the small representative. The retained upstream proof
constructs the full affine-neighbourhood colimit directly, so its public theorem
suffices without a new wrapper or transport. Both statements exclude the same
zero-ring and unit-divisor edge cases through y and hy. No statement is disputed.
Current msearch.py LeanFinder, Loogle and grep searches and local source searches
confirm that the direct upstream theorem is the shortest route.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
