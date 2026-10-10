# Stage 1 report

## Files written

- `dag/nodes/sec-smooth-base-change/sbc-lem-higher-direct-image-limit.json`: item split, no new nodes.
- `citations.json`: verbatim quotes for every cited node in the proof steps.

## Attachments

The Lean declaration `AlgebraicGeometry.Etale.higherDirectImage_limit` was checked in `WeilConjectures/SixFunctors/Etale/SmoothBaseChange/HigherDirectImage.lean:115-140`. Its theorem body is `sorry`, so it is not an attachment.

## WANTED

None.

## Review by K1

I read the imported item, its blueprint source, Stacks Tags 03Q8 and 09Z1, and the Lean declaration. The declaration has the exact blueprint tag but an unfinished proof, so the item needed a split. I also read the existing nodes `sbc-lem-higher-direct-image-presheaf` and `lem-weil-pbc-etale-cohomology-limit-complex-systems`; the former states the sheafification description used in step 1, and the latter states continuity of cohomology for bounded-below complexes under affine-transition limits, which specializes to degree-zero sheaves in step 2. Step 1 uses the presheaf node and the etale-cohomology definition; step 2 uses the continuity node and checks that affine etale base change preserves the qcqs and affine-transition hypotheses; step 3 is the elementary sheafification/gluing conclusion from the local isomorphisms. I searched the whole DAG and blueprint for duplicate continuity or direct-image-limit nodes before adding none. Mathlib searches (LeanFinder, Loogle, grep, and unavailable LeanSearch) found no matching higher-direct-image theorem. I checked the item hypotheses at the affine-base-change step and retained the original statement unchanged.

## Second reading by K1

- Statement: checked against Stacks Tag 09Z1 (Lemma 59.51.7), hypothesis by hypothesis; restored the omitted transition maps `\\varphi_{i'i}` and their compatibility, and made the projections and sheaf notions explicit.
- Step 1: checked against Tag 03Q8 and the full statement of `sbc-lem-higher-direct-image-presheaf`; the two presheaves and their sheafifications now match the cited node.
- Step 2: checked against Tag 09Z1's proof and `lem-weil-pbc-etale-cohomology-limit-complex-systems`; affine base change preserves the qcqs and affine-transition hypotheses, pullback preserves the compatible system, and degree-zero complexes have uniform lower bound 0.
- Step 3: checked against the sheafification argument in Tag 09Z1; restriction compatibility and the local affine-cover argument are stated explicitly, with only the two-line categorical gluing step marked elementary.
- New nodes: none; duplicate and Mathlib searches were checked, and the existing continuity node is the required tool.
- Changed the item statement and dependencies to match the source's actual sheaf system; removed the unused cohomology-definition citation from the proof and dependency union; replaced both citation entries with verbatim statement quotes; recorded empty `uses_not_cited`.
- Small cases checked: the zero sheaf system gives zero on both sides, a constant system reduces to identity, and $p=0$ is the direct-image colimit statement; no hypothesis fails for an empty scheme or a field base.
