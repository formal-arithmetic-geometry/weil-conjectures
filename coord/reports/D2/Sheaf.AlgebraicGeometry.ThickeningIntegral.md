## What changed

Proved `AlgebraicGeometry.isIntegralHom_iff_of_thickenings` with its original signature, using Mathlib composition, integral cancellation, universally-closed cancellation along a surjection, and the affine component `AlgebraicGeometry.isAffineHom_of_thickenings` in the new module `Sheaf.AlgebraicGeometry.ThickeningAffineHom`. The second reader proved that component from the existing `AlgebraicGeometry.isAffine_of_isThickening`: preimages of affine opens are affine, and the restricted source thickening remains a surjective closed immersion. Proof-only imports are plain imports. Updated both node records to follow the Lean proof.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.isIntegralHom_iff_of_thickenings` (node `lem-weil-pbc-thickening-integral`). Also proved the new `AlgebraicGeometry.isAffineHom_of_thickenings` (node `lem-weil-pbc-thickening-affine-morphism`), closing the first worker's proposed split hole before delivery. Added holes: none. Neither delivered module contains `sorry`.

The unchanged imported theorem `AlgebraicGeometry.isAffine_of_isThickening` in `Sheaf.AlgebraicGeometry.ThickeningAffineScheme` is still open. Explicit `#print axioms` checks for both delivered theorems show only `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx` through that existing dependency. This closes one hole relative to the delivery baseline, without claiming completion of the entire import closure.

## No longer needed

Removed the direct proof-only import `Sheaf.AlgebraicGeometry.ThickeningAffineScheme` from the integral module; it is now imported exactly where it is used, in `ThickeningAffineHom`. No module is pruned from the import closure.

Old direct proof dependencies `pqf-def-affine-morphism`, `def-weil-closed-immersion`, `lem-weil-pbc-affine-morphism-permanence`, and `lem-weil-pbc-thickening-affine-scheme` are replaced in the integral node by the affine-component node. The affine-scheme result remains used by that component, and affineness of inverse images and closed immersions is supplied by the existing Mathlib API; no unit route is bypassed. All other old direct proof dependencies remain.

## Where the brief, the DAG or earlier work was wrong

The first worker left the affine component as a new hole, but the existing affine-scheme theorem plus Mathlib's restriction and inverse-image APIs suffice to prove it in a short argument. The first node record lacked actual proof steps, searches, a verbatim Lean signature, and complete creation metadata. The first target node was absent from the sandbox, so its dependencies did not reflect the new proof. The original proof compiled with style warnings that prevent delivery. All these faults were repaired.

## New nodes

`lem-weil-pbc-thickening-affine-morphism` isolates only the affine direction of Stacks Tag 09ZV (1), strictly below the integral equivalence, and is proved from the existing affine-scheme theorem (Tag 06AD) and Mathlib. No new unproved statement and no change record are needed.

## Second reading by D2

1. Compared the integral module with the repository version and checked the existing theorem signature byte for byte: unchanged, with no statement or definition edits. Only proof bodies and proof-only imports changed. The affine theorem is a new declaration in its own module. Verdict: pass.
2. Compiled both modules in import order through `lcompile.py --all`: no errors or warnings. Neither contains `sorry`, forbidden axioms, unsafe/opaque declarations, foreign-code attributes, or definitions choosing arbitrary data. Explicit scratch-copy `#print axioms` checks for both declarations show only the three permitted axioms and `sorryAx` from the existing open affine-scheme theorem. Verdict: pass.
3. Checked the affine statement, including identity thickenings and empty schemes: the proof uses no nonemptiness, finite-order or cartesian hypothesis. Verified the source at https://stacks.math.columbia.edu/tag/09ZV and https://stacks.math.columbia.edu/tag/06AD. Searched with fresh leansearch (service unavailable), leanfinder, loogle and grep queries recorded in `searches.jsonl`, and searched the upstream library and `lean/Sheaf`: no duplicate general thickening-affine-morphism theorem. Proved the first worker's split theorem from the existing affine-scheme theorem. Verdict: pass, no split holes remain.
4. Kept the integral composition/cancellation and affine-open route. Removed the redundant direct affine-scheme import from the integral module, retaining it in the affine component where used. Imports required by signatures are public; imports used only by proofs are plain. Checked `dag/units/sk-thm-p1.json` realized entries: these subsidiary nodes are not designated unit steps, and the unit's route and realized nodes remain untouched. Verdict: pass.
5. Repaired the new node with proof steps and their dependency union, source, three recorded kinds of search, creation metadata, `lean.existing`, and verbatim Lean signature. Updated the existing integral node's affine step, dependency union and proof origin. Both records follow the actual proof; all other fields of the existing node are preserved. Verdict: pass.

Second reading changed: proved the affine component; fixed all compiler style warnings; removed the redundant direct proof import; completed the new node; updated the original node; corrected the report's accounting and recorded axiom and source checks.
