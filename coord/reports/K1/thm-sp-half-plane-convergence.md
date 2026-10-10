# Stage 1 report: thm-sp-half-plane-convergence

## Files written

- `dag/nodes/sec-abelian-varieties/thm-sp-half-plane-convergence.json` (item, split; no new nodes)
- `citations.json` (verbatim citations for all uses of `lem-sp-derived-couple-exact`)

## Attachments

No Lean declaration matched this item. The existing DAG node `lem-sp-derived-couple-exact` is cited as a tool dependency; it is not duplicated.

## WANTED

None.

## Not duplicates

`thm-sp-half-plane-convergence` vs `lemma-weil-pbc-hypercohomology-convergence`: the latter is a specialized hypercohomology statement for three geometric exact couples, while this item is the general half-plane exact-couple theorem with an arbitrary lower bound `a`.

## Review by K1

I read the item source path recorded in the node and the definitions `def-sp-exact-couple`, `def-sp-convergence`, and `def-sp-filtration`. I also read `lem-sp-derived-couple-exact` in full. Its statement explicitly supplies the iterated exact-couple bidegrees, the formula for `D_r`, and the page-cohomology quotient defining `E_{r+1}`; these are the cited facts in Steps 1, 2, and 4, and the verbatim portions are recorded in `citations.json`.

Step 1 checks the two index bounds separately: incoming sources vanish for `r > p`, outgoing targets vanish for `r > q-a+1`, giving exactly the stated maximum. Step 2 uses only the convergence definition after those differentials vanish, and checks completeness from `D^{p+r,q-r}=0` when `q-r<a`. Step 3 checks the negative-first-index hypotheses needed to make the relevant `alpha` map an isomorphism, then checks the endpoint values of the image filtration from its definition. Step 4 uses the exact `D_r` image formula from the cited node and the lower-bound vanishing to identify the successive quotient with the filtration graded piece.

I searched the whole DAG for the Stacks tags and for exact-couple/spectral-sequence statements. The only reusable general result was `lem-sp-derived-couple-exact`; the hypercohomology convergence node has stronger, specialized hypotheses and is not a duplicate. Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and is recorded as unavailable in the item.

## Source or statement issues

The imported proof had a free-standing Stacks citation with no DAG citation and omitted the exact-couple iteration node. I attached that existing node to each relevant step, made the Stacks paragraph an elementary application of the cited statement, and filled the blueprint and split metadata. No statement was changed.

## Unfinished

No unfinished work remains in this stage.

## Second reading by K1

- Item statement: checked against the blueprint node and Stacks Tags 011T and 012F; hypotheses, stabilization bound, image filtration, and associated-graded conclusion agree.
- Step 1: checked incoming and outgoing bidegrees against `lem-sp-derived-couple-exact`, and regularity/completeness against `def-sp-convergence`; the negative-index and lower-half-plane cases are valid.
- Step 2: checked iterated bidegrees and image-filtration indices against `lem-sp-derived-couple-exact` and `def-sp-filtration`; repaired the missing coordinates, large-page choice, and surjectivity argument from exactness.
- Step 3: checked the cited Stacks facts against Tags 011T and 012F and the citation quote against `lem-sp-derived-couple-exact`; the paragraph is an elementary source application.
- New nodes: none; the existing `lem-sp-derived-couple-exact` is the only non-elementary dependency, and its statement supplies the iterated exact-couple formulas used here.
- Small cases: the zero couple gives zero filtration and pages; a field concentrated in one bidegree stabilizes immediately; the zero abutment and `n=0,1` boundary ranges satisfy the stated bounds.
- Changes: rewrote Step 2 to identify `u=p-r+2`, `v=q+r-2`, relate both `D_r` images to `G_q` and `G_{q-1}`, and derive the quotient from the exact three-term sequence; appended this second-reading audit.
