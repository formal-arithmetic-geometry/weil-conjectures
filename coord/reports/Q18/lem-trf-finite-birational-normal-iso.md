# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-birational-normal-iso.json`: statement item, split into three proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-normal-affine-open-domain.json`: new statement-only node; Mathlib search found no exact declaration.
- `citations.json`: verbatim statement excerpts for every cited node at every step.

## Attachments

- `AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen` belongs to `lem-sc-integral-function-field-affine-fraction` (existing Mathlib leaf).
- The target has no sorry-free project declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`.

## WANTED:

None.

## Not duplicates

- `lem-trf-normal-affine-open-domain` vs `lem-sbc-normalization-dense-open`: the existing node concerns a relative normalization morphism over a dense open and its isomorphism; the new node concerns the normal-domain property of global sections on an arbitrary nonempty affine open of an integral normal scheme.
- `lem-trf-normal-affine-open-domain` vs `lem-sbc-normal-dense-open-integral-section`: the existing node extends integral sections from a dense open; the new node identifies the entire affine section ring as a normal domain.
- `lem-trf-normal-affine-open-domain` vs `lem-sc-normalization-properties`: the existing node gives properties of normalization of finite-type curves; the new node is the local normality-to-affine-sections implication for any integral scheme.

## What I checked and corrected

I read the target node, its unit `sk-i-curve-zero`, and the Stacks source `literature/stacks-project/morphisms.tex`, Tag 0AB1 (`lemma-finite-birational-over-normal`). I also read `properties.tex`, Tag 033L (`lemma-integral-normal`), which supplies the one new dependency. The target statement matches Tag 0AB1 clause by clause: both schemes are integral, the morphism is finite, the function fields are identified, and the target is normal at every local ring. No normality of the source, properness, dimension, or field perfection was added.

Step 1 uses the finite affine-local definition from `def-weil-finite-integral-morphism`, the integral-scheme hypotheses, the function-field definition, and the existing `lem-sc-integral-function-field-affine-fraction` leaf. These statements provide affine inverse images, domain section rings, injective germ maps, and fraction fields. The birational function-field isomorphism therefore gives the affine ring inclusion with equal fraction fields. Step 2 uses the new Tag 033L node and finiteness: the target affine section ring is a normal domain and every source section is integral over it, so integral closedness gives equality. Step 3 uses the finite affine-local description and the single sheaf morphism to glue the equalities over the affine cover to an isomorphism.

For the new node I searched the full DAG and blueprint before writing it; no node stated Tag 033L. Its statement is strictly smaller than the target and is statement-only. I ran LeanFinder, Loogle, grep, and LeanSearch through `msearch.py`; LeanFinder/LeanSearch found only the domain component theorem, Loogle was unavailable for the malformed pattern, and grep found no normal-affine theorem in Mathlib. The existing function-field leaf was read directly and its exact statement is quoted in `citations.json`.

I tested the edge cases conceptually: the identity on an affine normal integral scheme satisfies all steps; the normalization of a cusp shows why target normality is necessary; an open immersion missing a point is birational but not finite, showing finiteness is necessary. The empty affine open is excluded exactly as in Tag 033L and the item quantifies over nonempty affine opens. No SGA source is used. The pre-report server `check_dag` check passed.

## Review by Q18

I checked the target source and every cited node file, including all four definition/function-field inputs in Step 1 and both inputs in Step 2. Their quoted statements in `citations.json` are verbatim. I verified the hypotheses at each use: integrality supplies domains and generic points; finiteness supplies affine inverse images and finite ring maps; the function-field node supplies injectivity and fraction-ring descriptions; Tag 033L supplies normality of target affine sections. The final gluing is the affine-cover criterion stated in Tag 0AB1. I corrected the imported item by adding the missing affine-normal-sections dependency and by replacing the empty proof with the source's complete affine ring argument. I also recorded all required Mathlib searches and checked the duplicate candidates listed above.

## What remains

Nothing remains for this split; the delivery dry run is the next required check.
