## What changed

Added the explicit-transition intermediate `overlap_conjugate_restriction_explicit`.
The target theorem now substitutes the hypothesis identifying `θ` with the canonical
conjugated transition and applies that intermediate. The existing single-chart
restriction theorem remains the lower decomposition used by the intermediate.

## Proved and sorry left

The target `overlap_conjugate_restriction` is proved by a real substitution and
application. Two named intermediate holes remain: `overlap_conjugate_restriction_explicit`
(the full restriction-square calculation at the canonical transition) and
`overlap_single_chart_restriction` (the one-chart comparison equation).

## No longer needed

The single-chart restriction module is imported privately for the split proof dependency. The
unused private categorical helper lemmas from the worker draft were removed.

## Where the brief, the DAG or earlier work was wrong

The direct full expansion exceeds the kernel elaboration timeout. Fixing the
canonical transition as an explicit intermediate reduces elaboration to a fast
substitution while preserving the exact target statement.

## New nodes

`lem-pc-overlap-conjugate-restriction-explicit` records the strict intermediate
with the transition supplied explicitly; its source is the restriction-square
calculation in the target node's proof steps.

`lem-pc-overlap-single-chart-restriction` records the single-chart restriction
equation used by that intermediate; its change record is
`coord/changes/overlap-canonical-comparison-representation.md`.

## Second reading by Q2

1. Compared the delivered module with the repository version. Existing declaration signatures
are unchanged; the target proof substitutes the transition and applies the explicit intermediate.
The original bodies of existing comparison and transition definitions were restored because no
definition change was declared.
2. Compiled both sandbox modules with `lcompile.py --all`. The only remaining `sorry`s are the
named split theorems `overlap_conjugate_restriction_explicit` and
`overlap_single_chart_restriction`; no unsafe declarations or extra axioms were introduced.
3. Checked the split statements against their docstrings and DAG nodes. The explicit intermediate
is strictly stronger than the target's arbitrary-transition form, while the single-chart statement
is the needed lower restriction equation. No duplicate library declaration was found.
4. Pruned unused private helper lemmas and changed the added single-chart dependency to a plain
import. The target node's proof and dependencies now match the actual substitution proof.
5. The unit route is preserved: the target reduces to the explicit restriction-square node,
which reduces to the single-chart restriction node and canonical comparison definitions.

Changed in this second reading: restored unrecorded definition-body edits, removed unused helper
lemmas, made the added import proof-only, corrected the target DAG proof route, and fixed compiler
warnings.
