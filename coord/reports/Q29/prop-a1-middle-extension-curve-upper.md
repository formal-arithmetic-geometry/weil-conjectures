## Files written

- `dag/nodes/sec-deligne-laumon-a1/prop-a1-middle-extension-curve-upper.json`: current main-20261015 statement, two-step natural-language split, and updated blueprint metadata; no new nodes and no Mathlib leaves.
- `citations.json`: 10 exact statement citations, covering both proof steps.

No auxiliary node files were needed. The item is a specialized Weil-sheaf theorem, so it is not a Mathlib candidate; no Mathlib search was required. No Lean files, compiler, Lake, or live project files were touched.

## Attachments

None. I searched the reference `WeilConjectures/` trees for the exact item id, blueprint tag, and the middle-extension/curve-upper terminology. No sorry-free project declaration states this proposition exactly.

## WANTED

None.

## Statement and source check

The proposition statement agrees with the current `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-a1/sk-thm-dl-a1-upper/prop-a1-middle-extension-curve-upper.md`: a dense open immersion of smooth geometrically connected curves, a lisse punctually pure sheaf, and the upper bound `w+r` for compactly supported cohomology of the ordinary middle extension. No hypothesis or conclusion was changed. The imported source and proof metadata pointed to the older master snapshot; these now point to the current main-20261015 snapshot.

## Review by Q29

I read `coord/brief-stage1.md`, `stages/1-dag.md`, the B–E delivery-error checklist, the current unit and chapter records, the current proposition statement and proof, and the statements of every cited node. The two proof paragraphs follow the current blueprint route.

Step 1 cites `lem-a1-affine-core-of-curve` for a nonempty dense affine open with finite complement and `lem-a1-lisse-middle-extension` for recovery of a lisse sheaf under the dense-open ordinary direct image. I checked that the restriction of the given lisse sheaf to the chosen affine open satisfies the recovery lemma, that a dense open in a smooth geometrically connected curve has finite complement, and that ordinary direct image is transitive. Thus the middle extension from the affine open is the same `j_*\\mathcal F` in the item.

Step 2 cites `thm-a1-affine-curve-upper` for the affine cohomology weight bound and vanishing outside degrees 0, 1, 2. It cites `lem-wf-boundary-semicontinuity` for the boundary weight bound under the punctually pure hypothesis and `lem-wf-boundary-stalk-invariants` for the Frobenius-equivariant inertia-invariant stalk description. I checked that the finite boundary is the complement of a dense open in a finite-type curve. It cites `lem-a1-finite-boundary-cohomology` for concentration of the finite-boundary term in degree zero and `lem-a1-finite-boundary-weights` for its upper weight bound. It cites `prop-a1-curve-boundary-sequence` for the localization triangle, then `lem-a1-subquotient-extension-bounds` and `lem-a1-extension-bounds` for the Frobenius-stable quotient/subobject and extension weight arguments.

The imported second paragraph described the long-exact-sequence pieces with an ambiguous and, in degree zero, reversed extension orientation. I corrected it explicitly: degree zero is an extension of a subobject of the boundary group by the affine group; degree one is a quotient of the affine group; degrees at least two are isomorphic to the affine groups; and the same triangle gives vanishing outside 0, 1, 2. This supplies the claimed `w+r` bound in every degree, including the vacuous negative and high degrees. Every citation quote in `citations.json` is copied verbatim from the corresponding node statement, and `proof_deps` is exactly the union of the two steps' uses. No duplicate or hidden auxiliary lemma was introduced, and no off-unit tool citation is needed.

## What was corrected

The imported proof's localization conclusion was rewritten degree by degree to match the actual long exact sequence. The blueprint metadata and proof provenance were updated from the older master snapshot to main-20261015. The mathematical statement itself remains unchanged.

## Unfinished work

None. The required server dry run remains to be run on this sandbox.
