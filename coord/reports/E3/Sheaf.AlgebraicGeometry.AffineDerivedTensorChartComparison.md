## What changed

Proved `AlgebraicGeometry.affine_derivedTensor_chart_comparison` in
`lean/Sheaf/AlgebraicGeometry/AffineDerivedTensorChartComparison.lean`. The proof converts the
module K-flat hypothesis to the acyclic-tensor criterion, applies affine tilde K-flatness and
open restriction K-flatness, maps the specified quasi-isomorphism through the chart, and
composes the natural derived-tensor comparison with `affineChart_totalTensor_iso`.

Removed proof-only imports of `Mathlib.CategoryTheory.Preadditive.LeftExact`,
`Sheaf.Algebra.Homology.KFlatPullback`, `Sheaf.AlgebraicGeometry.AffineTildeTotalTensor`, and
`Sheaf.AlgebraicGeometry.Modules.RestrictionTensorComparison`; the file still compiles without
them.

## Proved and sorry left

Closed the only hole, `AlgebraicGeometry.affine_derivedTensor_chart_comparison`. No `sorry` remains
in the delivered module, and no new holes were added.

## No longer needed

The four proof-only imports listed above are no longer needed. No proof-dependency node is pruned:
the proof uses the K-flat criterion, affine tilde K-flatness, open restriction K-flatness, the
K-flat derived tensor comparison, affine total-tensor comparison, and the imported private tilde
kernel-preservation theorem.

## Where the brief, the DAG or earlier work was wrong

Nothing found.

## Second reading by E3

1. Compared the delivered module with the repository version. The theorem statement and all existing declaration signatures are byte-for-byte unchanged; only the theorem proof and proof-only imports differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings. A scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` declarations. Verdict: pass.
3. Checked the existing DAG node and proof dependencies. The proof uses the stated K-flat criterion, affine tilde K-flatness, open restriction K-flatness, derived tensor comparison, affine chart total-tensor comparison, and imported kernel-preservation result; no new statement or node is introduced. Verdict: pass.
4. Checked the proof route and pruning. It preserves the unit route through K-flatness, restriction, derived tensor comparison, and the affine chart isomorphism. The four removed imports are proof-only and unused after the new proof. Verdict: pass.
5. Checked the Lean/DAG agreement and source route. The declaration, proof dependencies, and proof origin match the implementation and the Stacks source cited by the node. Verdict: pass.

No changes were needed during second reading; the delivered proof and import pruning are accepted as written.
