## What changed
Added `AffineBaseFlatQuasiFiniteChartCore.lean`, whose named theorem isolates the affine-base polynomial chart construction and remains a documented `sorry`. Replaced the target theorem proof by a real packaging argument: obtain the core chart, define the relative affine space and its projection to `T`, and apply the smooth composition theorem. Added the corresponding DAG node and updated the item's proof route.

## Proved and sorry left
The target declaration `exists_flat_quasiFinite_chart_of_fibre_depth_eq_ringKrullDim` is proved. The new declaration `exists_affine_base_flat_quasiFinite_chart_core` remains `sorry`, with node `lem-sbc-affine-base-flat-quasi-finite-chart-core`.

## No longer needed
The target proof no longer directly needs the five former proof-dependency nodes; they are subsumed by the isolated core theorem. The target module retains only its statement imports, the Smooth import, and the core import.

## Where the brief, the DAG or earlier work was wrong
The original DAG plan placed the entire affine localization and polynomial-factorization argument directly in the target proof. That argument is too large for this item; it was split into the strictly smaller affine-base core statement, while the target's remaining packaging is fully proved.

## New nodes
`lem-sbc-affine-base-flat-quasi-finite-chart-core` is added at `dag/nodes/sec-smooth-base-change/lem-sbc-affine-base-flat-quasi-finite-chart-core.json`; its Lean declaration is in `lean/Sheaf/AlgebraicGeometry/AffineBaseFlatQuasiFiniteChartCore.lean`.

## Earlier second reading (a previous round; superseded)
The target proof uses the unchanged target signature and obtains every target conjunct from the affine-base core and the standard affine-space smoothness composition theorem. The new core statement is a strict affine-base subproblem and is exactly the remaining construction from Tag 00RH; its proof is intentionally left for a subsequent worker.

## Second reading by S1

1. I compared the delivered target module with the repository version. The theorem signature and all existing declarations are unchanged byte for byte; only the proof and a proof-only import were added. Verdict: pass.
2. I compiled both delivered modules with `lcompile.py --all`. They compile cleanly. The target proof has no `sorry`; the only remaining `sorry` is the named core theorem, documented in its docstring and represented by node `lem-sbc-affine-base-flat-quasi-finite-chart-core`. No forbidden declarations or hollow definitions were introduced. Verdict: pass.
3. The core statement is a strict affine-base subproblem: it fixes the base open and affine-space target and leaves the smooth packaging to the target theorem. Its hypotheses and conclusion match the construction needed by the target, with no weakened target conclusion. Verdict: pass.
4. The target proof follows the shortest available route from the core theorem and the existing affine-space smoothness and composition declarations. The proof no longer uses the five former construction dependencies directly; the unit route is retained through the core node. Verdict: pass.
5. The target DAG proof now records the core node as its sole proof dependency, and the new core node records its construction dependencies and Lean declaration. Verdict: pass.

I changed the report only by adding this second-reading record. No Lean proof or statement changes were needed during review.
