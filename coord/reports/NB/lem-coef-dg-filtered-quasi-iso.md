# Stage 1 report: lem-coef-dg-filtered-quasi-iso

## Files written

- `dag/nodes/sec-six-functors/lem-coef-dg-filtered-quasi-iso.json`: statement node, split into four proof steps; no new nodes; existing Mathlib leaves are cited through the DAG.
- `citations.json`: verbatim statement quotes for the three non-elementary citations in step 2.

## Attachments

None. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this filtered quasi-isomorphism criterion.

## WANTED

- WANTED: Toën, arXiv:math/0408337, Section 3 (the dg-module semi-free filtration argument in the source route); the paper is absent from `literature/`, so the detailed filtration proof here is agent-written from the blueprint route.

## What was wrong or incomplete

The imported node was unsplit and had no proof. Its statement is well-typed and agrees with the exhaustive-filtration auxiliary assertion used in paragraph 2 of `prop-coef-integral-exceptional-adjoint.proof.md`. I found no duplicate statement in the DAG or blueprint and no existing project declaration tagged with this item. The existing Mathlib searches for the item found only generic quasi-isomorphism criteria, with no exhaustive filtered-union theorem; those recorded searches were retained.

No new nodes were created, so there are no new-node duplicate pairs to report.

## Review by NB

I read the item source and the blueprint ancestor `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`, paragraph 2. Step 1 checks that the split graded inclusions give degreewise short exact quotient rows and that the map preserves the rows. Step 2 uses the statements of `lem-weil-pbc-complex-ses-homology-long-exact` (the long exact cohomology sequence), `lem-weil-pbc-complex-ses-long-exact-naturality` (the connecting-map comparison), and `lem-weil-pbc-five-lemma` (four surrounding isomorphisms imply the middle isomorphism); I opened each cited node and copied the exact sentences into `citations.json`. The induction starts at the zero stage and uses the quotient quasi-isomorphism in the required degrees. Step 3 checks explicitly that cycles and boundaries in an increasing union are unions of the stage cycles and boundaries, including the later-stage witness for equality or null-homology, so cohomology of the union is the directed colimit of stage cohomologies. Step 4 evaluates at each dg-module object and applies the complex result, exactly matching the objectwise quasi-isomorphism convention from `lem-coef-dgcat-model-structure`. I tested the edge cases of the zero filtration and a map from the zero complex to an acyclic exhaustive filtration; both reduce to the stated induction and union argument. The three cited homological nodes are generic tools from another unit and are declared in `split_report.tool_uses`; no SGA source is used.

## Could not finish

Nothing remains for this stage-1 split; the missing Toën paper affects only source availability, and the proof is recorded as agent-origin with the requested WANTED line.
