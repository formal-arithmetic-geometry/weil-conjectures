## What changed

Repaired the duplicate theorem rejection by removing the separate public torsion helper module and using the existing assertion theorem's torsion argument locally. The coefficient-control statement remains proved with its original signature.

## Proved and sorry left

`AlgebraicGeometry.IsCurve.finite_pushforward_coefficient_control` is proved. No `sorry` was added or left in the item module.

## No longer needed

Removed the added `FinitePushforwardTorsion` and adapted `FinitePushforwardAssertions` sandbox copies. The item now keeps only imports needed by its proof; no new public declaration is introduced.

## Where the brief, the DAG or earlier work was wrong

The earlier repair added a public theorem/module duplicating the torsion result already stated in `FinitePushforwardAssertions`, which violated import-pruning checks. The torsion proof is now inlined in the coefficient-control proof, avoiding that duplicate declaration and preserving the existing route.

## New nodes

None. The previously added `lem-g1-finite-pushforward-torsion-helper` node and its change record `coord/changes/finite-pushforward-torsion-extraction.md` were removed because the helper duplicated an existing theorem route and is no longer needed.

## Earlier second reading (a previous round; superseded)

The repaired sandbox module compiles with `lcompile.py`. The duplicate public helper and adapted dependent module were removed; the target theorem signature is unchanged and no new declarations or holes remain.

## Second reading by R1

1. The delivered theorem signature is byte-for-byte unchanged from the repository version; the proof only fills the existing `sorry`, and the stale dependent-node adaptation is excluded.
2. The module compiles with `lcompile.py`; it contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The target's remaining `sorryAx` dependency comes only from the imported open constructibility-descent theorem.
3. No new public statement or split-off theorem was added. The private helpers are local proof reductions, and the coefficient-control statement is unchanged and true for the stated edge cases, including `p = 0` and `p = 1`.
4. The proof uses the finite stalk formula, counit epi argument, and existing integral constructibility descent. The added `ConstructibleIntegralCoefficients` import is proof-only and plain; no unused public import was introduced.
5. The target DAG node's proof steps and dependencies match the proof, and the unit route remains through finite stalks, coefficient comparison, and constructibility descent. No unit record was changed.

Changed in this reading: removed the stale `FinitePushforwardAssertions` node copy from the delivery and added this review record. No Lean declarations or target statements were changed.
