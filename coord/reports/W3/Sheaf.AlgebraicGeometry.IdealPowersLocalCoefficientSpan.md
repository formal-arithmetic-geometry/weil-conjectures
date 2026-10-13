## What changed
Replaced the proof of `AlgebraicGeometry.idealPowersLocalCoefficientSpan_affine` with a direct proof. Affine section base change transports the given spanning family to W. The affine image and tensor comparisons compute multiplication membership, the existing ideal-power formulas compute its coefficient ideal, and `Ideal.map_pow` plus `Submodule.span_smul_span` give the desired coefficient span. The local affine-basis proof is unchanged.

Removed the first worker's undelivered `idealPowersLocalCoefficientSpan_affine_expansion` theorem and its node: its finite-sum conclusion is equivalent to the affine span conclusion, so it was a restatement rather than a strictly smaller subproblem. Restored the affine theorem's original docstring.

Removed the proof-only import `Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient`. Added proof-only imports `Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`, `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Affine`, and `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`. All existing public imports, declaration signatures, definitions, and visibility are unchanged. Updated the existing affine-core node's proof, proof dependencies, and proof origin to match the Lean proof. No change record is needed.

## Proved and sorry left
Hole closed relative to the repository: `AlgebraicGeometry.idealPowersLocalCoefficientSpan_affine` (node `lem-weil-pbc-ideal-powers-local-coefficient-span-affine-core`). Holes added: none. Holes remaining in delivered modules: none. The already proved `AlgebraicGeometry.idealPowersLocalCoefficientSpan` now also has no sorry in its axiom closure.

Both declarations compile and `#print axioms` lists exactly `propext`, `Classical.choice`, and `Quot.sound`. This closes one of one original holes, with no split-off statements; it is a proof, not a decomposition.

## No longer needed
Removed direct import `Sheaf.AlgebraicGeometry.ModulePullbackIdealQuotient` and old affine-core proof dependency `lem-weil-pbc-module-pullback-ideal-quotient`: only the existing affine ideal-extension formula is needed, so the full quotient/pullback theorem is bypassed. The other two old proof dependencies remain used. This prunes that direct dependency of this item; no assertion is made that the module is globally unreachable, since other targets may import it.

The undelivered expansion theorem and node are discarded, not additions to the library. `dag/units/sk-thm-p1.json` has been checked: neither this affine subargument nor the removed quotient dependency realizes a unit statement or step. The local theorem and its dependency on the affine core remain unchanged, preserving the unit route.

## Where the brief, the DAG or earlier work was wrong
The first worker moved the affine span problem into an equivalent finite-sum expansion theorem with the same hypotheses. Its docstring lacked a complete proof, its node's Lean statement was an ellipsis, and it did not update the affine-core node's dependencies. No new expansion lemma is necessary: the already proved affine image/tensor, base-change, ideal-extension and power formulas suffice. The removed quotient theorem is stronger than the ideal-extension calculation actually needed.

## Second reading by W3
1. Compared the complete module with the repository using diff and the declaration parser. Both existing theorem statement strings are byte for byte identical. No definition, public import, visibility, or target meaning changes. The only added theorem in the first worker's work was removed before delivery; no new public declarations remain.
2. Compiled the delivered file locally through lcompile.py with no errors or warnings, and compiled a scratch copy with both axiom prints. Both declarations use only propext, Classical.choice and Quot.sound, with no sorryAx. Scanned for sorry, axioms, unsafe, opaque, implemented_by and extern: none in the delivered source. No data definition or arbitrary witness from an unproved existence theorem was introduced.
3. Refused and removed the expansion restatement. No split-off statements remain. Read the existing affine base-change, tensor, image, ideal-power and ideal-extension declarations. Independent leanfinder search for restriction of spanning generators found local generator predicates, not a shorter exact result; loogle and grep found Submodule.span_smul_span, which is used. Edge cases: m=0 is proved with the identity inclusion and I^0=top; r=0 forces F(U)=0 and the same base-change proof forces F(W)=0; I=0 at positive powers gives the bottom coefficient ideal; empty affine opens and the zero ring need no nonemptiness assumptions.
4. The proof follows the local theorem downward and closes the affine core directly from existing proved results. All proof-only imports are plain imports; each is used for the comparison, range, ideal extension or quasi-coherence calculation. The unused full quotient dependency is removed and reported. The unit realized map is retained, with no bypass of a realized unit node.
5. Updated the existing affine-core node's proof, proof_deps and proof_origin to the actual route. Its declaration and statement record are unchanged. The local node still applies the affine core and needs no edit. No new nodes or change records remain.

The first dry run flagged module-level namespace opens as an interface change. These were scoped inside the affine proof instead, with the monoidal operations written by their names; the static interface check now reports no change.

Second reading changed: replaced the equivalent sorry expansion with a complete direct affine proof; restored the original docstring; removed its new node; pruned the quotient import and dependency; added the necessary proof-only comparison imports; corrected the DAG and report.
