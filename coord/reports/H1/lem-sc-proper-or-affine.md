1. Files written

- `lem-sc-proper-or-affine.json`: statement node, split; no Mathlib match.
- `citations.json`: verbatim citations for both proof steps.

2. Attachments

None.

3. WANTED

None.

4. Problems found

The Lean source has no declaration tagged `lem-sc-proper-or-affine`; the nearby declarations `IsConnectedCurve.exists_smooth_properCompactification` and `IsConnectedCurve.isAffine_of_ne_top` are sorry-bearing and do not state this item. The existing DAG node `lem-sc-affine-open-proper` is restricted to the algebraically closed curve setting, which is appropriate here because `def-sc-curves` itself requires an algebraically closed field. No new node was necessary: the item's proof is the two-case argument using the existing compactification and affine-open statements.

5. Unfinished

Nothing.

## Review by H1

I read the item's source context in `literature/blueprint/master/blueprint/sec-curve-estimates/sk-prop-ext-invariance/_section.md` and the Stacks source for Lemma 0A28. I also read the complete statements of `lem-sc-compactification` and `lem-sc-affine-open-proper` in the DAG. Step 1 uses exactly the compactification statement: it supplies a proper smooth connected compactification and a finite closed-point complement. Step 2 uses that same output and the affine-open statement: an empty complement makes the open immersion an isomorphism, while a nonempty complement satisfies the affine lemma's hypothesis. The transfer of properness across the resulting isomorphism is elementary. I verified that the algebraically closed-field hypothesis is supplied by `def-sc-curves`, despite the item's shorthand “field”. I checked the empty-boundary and nonempty-boundary cases separately, including the one-point boundary case. The Mathlib searches were rerun with the item id; LeanFinder and grep found no matching theorem, Loogle returned no usable hit, and LeanSearch was unavailable.

## Second reading by H1

- Item statement: checked against Stacks Lemma 0A28 (`varieties-lemma-dim-1-nonproper-affine`) and the blueprint affine-case sentence; verdict: the stated smooth separated connected curve dichotomy has the intended hypotheses, with algebraic closedness supplied by `def-sc-curves`.
- New node `lem-sc-proper-or-affine`: checked as a statement-only split node against B1-B7 and the existing DAG; verdict: self-contained, no duplicate node, correct blueprint ancestry, and `created.item` repaired to the delivered item.
- Step 1: checked against the complete statement of `lem-sc-compactification`; verdict: every asserted compactification property is supplied by that node.
- Step 2: checked against the statements of `lem-sc-compactification` and `lem-sc-affine-open-proper`; verdict: the empty-boundary isomorphism/properness transfer is elementary, and the nonempty-boundary case meets the affine lemma exactly.
- Small cases: checked a proper curve (`S=empty`), an affine line with one-point boundary, and the nonempty/empty alternatives; verdict: no edge-case failure.
- Mathlib search: checked the recorded LeanFinder, Loogle, grep, and unavailable LeanSearch runs; verdict: no usable declaration.

Changes: corrected the node ownership metadata (`created.item`) and added this second-reading audit; no mathematical statement or proof step required alteration.
