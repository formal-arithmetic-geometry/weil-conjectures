## What changed
Added a compiling decomposition of `tower_comparison` into first and second projection lemmas.

## Proved and sorry left
`tower_comparison` is proved by combining `tower_comparison_first` and `tower_comparison_second`.
The two decomposition lemmas remain `sorry`, with nodes `new-tower-comparison-first` and `new-tower-comparison-second`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The planned pointwise universal-property proof is substantial; it was split into its two projection components.

## New nodes
`new-tower-comparison-first` and `new-tower-comparison-second`.

## Second reading by R2
1. Compared the delivered module with the repository version. The existing
   `tower_comparison` signature is byte-for-byte unchanged; only its proof and
   the two explicitly recorded split-off lemmas were added.
2. Compiled both modules with `lcompile.py --all`. There are no errors, unsafe
   declarations, or hollow definitions; the only remaining holes are the two
   named split-off theorems and their nodes.
3. Checked the split statements against the target and small logical cases.
   They are the first projection and the conditional second projection,
   respectively, and together are exactly sufficient for the target. Neither
   weakens the target or adds an assumption to it.
4. Checked the proof route and imports. The target is reduced directly to the
   two projection lemmas, while both lemmas retain the explicit tower node as
   their dependency. The unit's comparison route is therefore retained; no
   import can be pruned.
5. Checked the DAG records and search records. The two new nodes match their
   Lean declarations, source, proof dependencies, and blueprint unit.

Changed only the review report and synchronized the existing target node's
proof metadata with the decomposition used by the Lean proof.
