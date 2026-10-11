1. Files written:

- `dag/nodes/sec-picard-framework/cor-pc-sigma-pic-iso.json`: statement node, split; no Mathlib leaf.
- No new node was needed: the open Lean comparison declaration is already covered by `lem-pc-cohomology-sections-affine-base`.

2. Attachments: none. The Lean declaration `AlgebraicGeometry.nonempty_picardFunctorNormalized_iso_picardFunctor` was checked at `WeilConjectures/AlgebraicGeometry/Picard/RationalPoint.lean:81-105`; its extra `GeometricallyIntegral` hypothesis and lack of the representability covariance clause prevent attachment.

3. WANTED: none.

## Review by K1

4. Review details

I read the item source `literature/blueprint/master/blueprint/sec-picard-framework/sk-prop-picard-pic-split/cor-pc-sigma-pic-iso.md`, the unit route, and the statements of `lem-pc-rational-hyp`, `thm-pc-pic-split`, `lem-pc-k-sheaf`, `def-pc-pic-sigma-functor`, and `lem-pc-cohomology-sections-affine-base`. Step 1 records the existing affine cohomology comparison node and checks that the rational-point hypothesis supplies the section and pushforward hypotheses required by the split theorem. Step 2 uses exactly the split theorem's sheafification statement, the sheaf condition for the kernel presheaf, and the definition of the normalized functor to obtain the natural isomorphism. Step 3 checks the final covariance clause by the standard Yoneda transport of a representing object; the split theorem's group law is the cited structure on the representing object. I verified each citation quote against the corresponding node text. The open Lean comparison declaration is already attached to `lem-pc-cohomology-sections-affine-base`, so no duplicate node was created.

5. What was wrong: the imported attachment proposition was too strong in Lean and incomplete as a statement. The imported proof also treated the entire argument as one paragraph and did not account for the existing node covering the open Lean comparison declaration. The corrected item retains the blueprint statement and cites that existing auxiliary comparison.

6. Nothing remains unfinished.

## Second reading by K1

- Item statement checked against the blueprint node `cor-pc-sigma-pic-iso`: field, smooth projective curve, rational point, fppf functors, isomorphism, sheaf and representability clauses agree; zero/field and empty-base cases introduce no contradiction.
- Step 1 checked against `lem-pc-rational-hyp` and `thm-pc-pic-split`: the cited statements provide exactly the section and pushforward hypotheses; unused citations were removed.
- Step 2 checked against `thm-pc-pic-split`, `lem-pc-k-sheaf`, and `def-pc-pic-sigma-functor`: the sheafification of K and the identification with the normalized functor give the natural isomorphism.
- Step 3 checked against the split theorem statement: Yoneda transport gives representability covariance, and the split Picard group structure supplies the stated group law; the short transport argument is elementary.
- No new nodes are present; the existing auxiliary comparison declaration is already covered by `lem-pc-cohomology-sections-affine-base` and was not duplicated.
- Checked B1-B7 and C1-C5: statement-only item, self-contained citations, verbatim citation quotes, and no Mathlib leaf or duplicate node were introduced. The blueprint ancestry was filled from the item’s own proof paragraphs.
- Changes: set `blueprint.from` to the item proof location and removed the two citations not used by step 1; appended this second-reading audit.
