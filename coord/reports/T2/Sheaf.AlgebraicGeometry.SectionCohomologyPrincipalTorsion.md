## What changed

Closed the original proof body of `AlgebraicGeometry.Scheme.Modules.sectionCohomologyPresheaf_pow_annihilates` using `resolution_unitTwist_comparison`, `invertS_cohomology`, and `cohomologyFraction_eventually_zero`. The new module `Sheaf.AlgebraicGeometry.ResolutionUnitTwistComparison` states the section-complex comparison, restriction naturality, and compatibility of unit-tensor transitions with scalar powers. The existing theorem signature and docstring are unchanged. Its new comparison import is private to the proof; the tensor unit and right unitor are fully qualified inside the proof.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.sectionCohomologyPresheaf_pow_annihilates` (node `lem-pc-section-cohomology-principal-torsion`).

Hole added and left: `AlgebraicGeometry.Scheme.Modules.resolution_unitTwist_comparison` (node `lem-pc-resolution-unit-twist-comparison`). Its proof is exactly `by sorry`, with source and a complete mathematical proof in its docstring. No other holes are added. This is a decomposition: one upper hole closed and one strictly lower comparison hole added, for net zero direct holes. The torsion theorem still depends on open proofs; it is not claimed axiom-free.

## No longer needed

Every old proof dependency of the item is retained: `def-pc-morphism-conventions`, `def-weil-pbc-flat-base-change-open-choices`, `lem-sc-invert-s-cohomology`, and `lem-sc-cohomology-fraction-eventually-zero`. No old node or module is pruned.

The new comparison module's unnecessary public import of `Sheaf.AlgebraicGeometry.CohomologyFractionPresentation` was replaced by `WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators`, which supplies the tensor transition in its signature. Its plan no longer assumes `lem-pc-resolution-sections-homology-scalar`: the scalar argument is explicitly included in the comparison's own mathematical proof. `Sheaf.Topology.RestrictInjectiveResolution` is imported privately for the retained restriction step. This is not a claim that either removed dependency module leaves the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The old plan elided the comparison between raw section cohomology of the pushed-forward resolution and open module cohomology of the restricted resolution. The split makes that work explicit. The original report described this as a proof without distinguishing the one-for-one decomposition. A change record for a proof-only import and namespace opening was unnecessary; it has been removed because no existing interface changed.

## New nodes

`lem-pc-resolution-unit-twist-comparison` at `dag/nodes/sec-picard-framework/lem-pc-resolution-unit-twist-comparison.json`, stated in `lean/Sheaf/AlgebraicGeometry/ResolutionUnitTwistComparison.lean`. It has no localization or torsion conclusion, no compactness, affineness, quasi-separatedness or quasi-coherence hypotheses, and supplies only the comparison required before applying the existing localization theorem. There are no statement or definition change records.

## Second reading by T2

1. Compared the entire existing module with the repository using `diff`. The theorem signature is byte for byte unchanged; no definition, hypothesis, conclusion, visibility, or existing docstring changed. Only its proof and a plain proof import changed. The other Lean module is new. Verdict: pass.

2. Compiled both modules in import order through `lcompile.py`; no errors or unexpected warnings. Scanned both files for forbidden declarations and hollow definitions. The only delivered sorry is the named new comparison theorem. Scratch-copy `#print axioms` checks and the delivery probe check the trust basis; `sorryAx` is expected from the named comparison and existing open dependencies. No arbitrary witness is used to define data: both delivered declarations are theorems. Verdict: pass, conditional on the documented lower holes.

3. Read the comparison top to bottom and checked Stacks 01E1, 01E4 and 09MR. Choose the actual pulled-back function times the unit generator; restrict the resolution, compare evaluation of presheaf complexes (not exact evaluation of sheaves), and use the canonical unitors. These give exactly the two displayed compatibilities. Checked a=0, unit a, q=0, zero F and empty W; all are covered uniformly. Independent LeanFinder, Loogle and grep searches located generic `isoRightDerivedObj` and homology comparison machinery, but no complete duplicate. Read the existing scalar-comparison statement: it is only one component of this bridge and does not discharge the combined theorem. The split is a strictly smaller comparison assertion, not a renamed torsion result. Closing it is substantial work, not a few-minute repair. Verdict: pass as a decomposition.

4. Read the target proof from the comparison through the canonical exponent-zero localization equation, injectivity, the fraction-zero criterion, and scalar transport. It uses the shortest available existing localization route; the direct-image section module cannot be imported because it depends on this item. Checked every old dependency and narrowed the new comparison import. Read `dag/units/sk-thm-picard-coherence.json`: its realized lists are currently empty, and this below-unit comparison does not change or bypass a unit step. Verdict: pass.

5. Compared both nodes with their Lean declarations and proof routes. Restored the first item's step uses so their union equals its proof_deps. The new node's plan now gives scalar linearity explicitly rather than citing a dependency its proof does not assume. Checked source, creation, blueprint, chapter/unit, searches, and Lean records. Verdict: pass.

Second-reading changes: narrowed the new module's signature import; added the private planned restriction import; corrected DAG step/dependency agreement and expanded its scalar argument; recorded independent searches; removed the unnecessary change record; corrected hole accounting; rewrote this report with the five review verdicts. No theorem statement changed. Qualified the tensor unit and right unitor in the proof and restored the original namespace opening after preflight classified the global opening as an interface change.
