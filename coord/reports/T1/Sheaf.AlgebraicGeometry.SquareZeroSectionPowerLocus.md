## What changed

Replaced the first worker's equivalent `SquareZeroSectionPowerLocusCore` restatement with
`Sheaf.AlgebraicGeometry.SquareZeroSectionPowerLift`, which states an actual equality of
section morphisms after lifting a positive tensor power. The original theorem now proves
its nonvanishing conclusion from that lift, `Hom.zeroLocus_eq_of_arrowIso`, the upstream
proved `compl_support_zeroLocus_tensorPowSection`, the section/nonvanishing dictionary,
and the proved `nonvanishing_tensorPullback`.

The original signature and all its public imports are byte-identical to the repository.
No existing definitions or statements changed; no change record is needed. Removed the
unchanged dependency copies from the delivery. Both delivered modules compile locally,
in import order, without errors or warnings through lcompile.py.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.exists_section_power_locus_of_square_zero`
(node `lem-sc-square-zero-section-power-locus`). The locus comparison is now proved.

Hole added and left: `AlgebraicGeometry.Scheme.Modules.exists_section_power_lift_of_square_zero`
(node `lem-sc-square-zero-section-power-lift`), in `SquareZeroSectionPowerLift`. Its entire
proof is a named `by sorry`, with a sourced natural-language proof in its docstring.
There are no other direct holes in the delivered modules. The rejected, unlanded core
module/node were deleted, so they add no hole.

This is a decomposition: one original hole closed, one earlier section-lifting step
added, net zero holes. It is not a sorryAx-free proof of the original theorem. Scratch
`#print axioms` for both declarations prints only `propext`, `Classical.choice`,
`Quot.sound`, and the expected `sorryAx`. No data definition is introduced or chosen from
mere existence. The section and comparison witnesses are used only in a theorem proof.

## No longer needed

Removed from the item's direct imports: `Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge`,
`Sheaf.AlgebraicGeometry.ClosedImmersionPushforwardAnnihilated`,
`Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`,
`Sheaf.AlgebraicGeometry.SectionAffineOpenKillsCohomology`, and
`Sheaf.Paper.BoundaryDerivationSquareZero`. These are now dependencies of the section-lifting
step, and remain imported by its new module. No module is claimed pruned from the targets'
import closure.

Every old proof dependency absent from the item's new direct proof_deps:
`lem-weil-pbc-closed-immersion-unit-quotient`,
`lem-weil-pbc-closed-immersion-pushforward-annihilated`,
`lem-weil-pbc-affine-morphism-cohomology-edge`,
`def-sbc-closed-immersion-ideal-sheaf`, `def-sbc-ideal-sheaf-powers`,
`lem-sc-boundary-derivation-square-zero`, `lem-sc-section-affine-open-kills-cohomology`,
and `lem-weil-pbc-locally-noetherian-quasi-separated`. All remain in the lift's proof plan.
The old `lem-weil-pbc-invertible-pullback-tensor` and
`def-weil-pbc-ample-invertible-module` remain direct dependencies.

## Where the brief, the DAG or earlier work was wrong

The first worker's core conclusion was equivalent to the original conclusion under hU,
with all the same hypotheses. Rewriting the locus did not make it a smaller argument.
The core node also cited the original node as a proof dependency, creating a cycle if
the parent's dependency were corrected. Rejected the first report's claim of a weaker
core, replaced it with the actual lifting step, and proved the subsequent locus comparison.

Read the Stacks proof in the local source copy
`/home/ubuntu/c1-stacks-review/coherent.tex`, label `lemma-ample-on-reduction` (Tag 09MS),
particularly the tensor exact sequence and boundary calculation. The new lift is that
part of the argument. A full dependency DFS also found an existing baseline cycle at
`lem-weil-pbc-sheaf-algebraic-structures-objects`; this delivery does not repair unrelated
nodes. A separate reachability check confirms that the new lift has no path back to the
original theorem, hence introduces no cycle through the changed proof edges.

## New nodes

`lem-sc-square-zero-section-power-lift`, in
`dag/nodes/sec-curve-estimates/lem-sc-square-zero-section-power-lift.json`: actual section
lifting, with no nonvanishing conclusion. The node includes a self-contained statement,
source, four proof steps, dependencies, verbatim Lean signature, and actual msearch.py
searches. LeanSearch returned HTTP 500 and is recorded unavailable; LeanFinder, Loogle,
and Mathlib grep found no exact lifting statement. Searches in Sheaf and WeilConjectures
also found no duplicate. No change record is required.

## Second reading by T1

1. Compared every module with the repository. All dependency copies were identical and
   were removed from the delivered set. The original signature is byte-for-byte unchanged;
   public imports and its docstring are unchanged. No existing data definition changes.
   Verdict: pass after repair.
2. Compiled both modules locally in import order with no error or warning. Exactly one
   new named theorem contains sorry, as listed above. Searched for axiom, unsafe, opaque,
   implemented_by, extern, and hidden holes: none. Scratch axiom checks give only the
   three allowed axioms and expected sorryAx. Verdict: valid decomposition.
3. Rejected the equivalent core restatement. The replacement is the section-equality step
   before the nonvanishing argument. Checked n=0 (unit comparison and powers of a function),
   s=0 (zero lift), empty schemes (unique sections), and j=id (canonical tensor-power
   comparison). No positivity hypothesis on n or ampleness assumption was introduced.
   Read the sourced docstring proof and planned dependency declarations. Used the existing
   proved zero-locus and pullback lemmas instead of adding holes for those calculations.
   Verdict: true, necessary section-lifting gap, strictly a part of the argument.
4. The reduction follows the source lift with a proved locus calculation. Proof-only
   imports use plain import. The report lists every removed direct dependency and makes
   no global pruning claim. The unit sk-thm-curveestimate realizes thm-sc-proper-cohomology
   and has no realized steps; this local reduction preserves its statement and route.
   Verdict: pass.
5. Updated the existing node's proof, proof_deps, and proof_origin to match Lean. The new
   node has the required fields and a matching Lean signature. Neither the lift statement
   nor its proof depends on the original theorem; no new dependency cycle is introduced.
   Each proof_deps is exactly the union of its proof steps' uses. Verdict: pass.

Changed by this reader: removed the invalid core module/node; added the actual lifting
module/node; proved the locus comparison; replaced direct proof imports; updated the parent
proof metadata; corrected the progress accounting and recorded this review. No signature changed.
