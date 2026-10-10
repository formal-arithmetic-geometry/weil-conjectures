# Delivery report

1. Files written:
   - `dag/nodes/sec-curve-estimates/lem-sc-invert-s-cohomology-induction.json` — item, statement, three proof steps, and split report.
   - `dag/nodes/sec-curve-estimates/lem-sc-invert-s-cohomology-separated-induction.json` — new unsplit statement node; Mathlib search found no direct induction theorem.
   - `citations.json` — verbatim statement excerpts for every cited node at every step.

2. Attachments: none.

3. WANTED: none. The Stacks source is identified by Tag 08DR and is available from the project’s cited Stacks metadata; no additional document was needed.

4. The original item was unsplit. Its statement already matches Stacks Lemma 08DR: X is qcqs, P is a property of quasi-compact opens, the affine base case and two-open gluing implication are the only hypotheses, and the conclusion includes X. I added the separated-open induction as a strict substatement because the general proof invokes it on the overlap inside an affine open. Existing DAG searches found no blueprint node stating either induction lemma. The proof cites the existing finite-affine-cover Mathlib leaf, the existing separated-affine-intersection Mathlib leaf, and the existing quasi-separated affine-cover criterion; no proof is moved into a new node.

## Review by H1

I read the Stacks Project page for Lemma 08DR (Induction Principle), including both proof paragraphs. The item statement agrees hypothesis by hypothesis with that lemma. The new separated-open node states exactly the first paragraph’s claim, with the same qcqs ambient scheme, affine base case, and two-open gluing hypothesis.

For item step 1, I checked that `lem-weil-pbc-qcqs-finite-affine-open-cover` states the finite affine cover used for W, and that `lem-weil-pbc-separated-affine-open-intersection` states that each affine U_i intersect V is affine; these are precisely the cited inputs. The induction is on the number of affine members, with the n = 1 case the stated affine hypothesis and the n > 1 case using the stated gluing implication. For item step 2, I checked that the new separated-induction node gives P for a separated quasi-compact overlap, that the finite-cover node supplies the cover of W, and that `lem-weil-pbc-quasi-separated-affine-cover-criterion` supplies quasi-compactness of intersections of affine opens in the qcqs scheme. The overlap is an open subscheme of the affine V and is therefore separated, matching the second paragraph of 08DR. Step 3 is the direct specialization W = X and is elementary.

I checked the small cases n = 1 (an affine open, covered by the hypothesis) and n = 2 (one gluing application, with the overlap treated by the separated-open result). The cited quotes in `citations.json` were copied verbatim from the corresponding node statements. The new node has no proof by design, as required for a one-level stage-1 split.

5. Nothing remains unfinished.
