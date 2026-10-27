## What changed

Copied `Sheaf.Paper.ReindexingSystemHomReductionSquare` into the E4 sandbox and
reduced its final conjunction to two named component theorems:
`podReindexingSystemHomReductionSquare_laws` for the actual system identities and
`podReindexingSystemHomReductionSquare_realization` for their functorial total-limit
realization.  The original theorem is now a genuine structural assembly of those two
components.  The item node proof and proof dependencies were updated to record this
route.

## Proved and sorry left

The original theorem
`podReindexingSystemHomReductionSquare` is proved by assembling the two strictly
smaller component statements.  Two sorries remain, one in each named component:

- `podReindexingSystemHomReductionSquare_laws`, node
  `new-e4-pod-system-reindexing-laws`;
- `podReindexingSystemHomReductionSquare_realization`, node
  `new-e4-pod-system-reindexed-realization`.

No definitions contain `sorry`.  The delivery closes one original sorry and splits
two strictly smaller proof obligations.

## No longer needed

No Lean imports were removed.  The final theorem's direct proof no longer needs the
item node's former 24 proof dependencies individually: it uses only the two new
component declarations.  Those dependencies remain imported because the same module's
public definitions and structures use them, so they are not removable from the module.

## Where the brief, the DAG or earlier work was wrong

The existing nine-step proof plan bundles the entire system construction and its
functorial realization into one theorem.  The available declarations do not provide
all of those identities as a single proved theorem, so the final conjunction can only
be assembled cleanly after naming the two independent component obligations.  No
statement was weakened or changed.

## New nodes

`new-e4-pod-system-reindexing-laws` records the system-level component theorem
`podReindexingSystemHomReductionSquare_laws`.

`new-e4-pod-system-reindexed-realization` records the functorial realization component
theorem `podReindexingSystemHomReductionSquare_realization`.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
