# Stage-1 delivery: lem-trf-two-term-augmentation-determinant-normalization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-two-term-augmentation-determinant-normalization.json`: item, statement, split; no Mathlib match for the whole assertion.
- `citations.json`: 15 step/node pairs, with verbatim quotations from current dependency statements.
- `report.md`: this report. Existing `prepare.py` and `searches.jsonl` were retained; the script records the previous draft and the JSON node is the final version.

No new nodes; no new Mathlib leaves. No Lean files, library records, unit realizations or repository files were written.

## Attachments

None. Searched the project library for the exact blueprint id, augmentation/determinant combinations, ordered-wedge and kernel-normalization language, and determinant files. The related `exists_completedConormalDeterminantComparison` in `lean/Sheaf/TraceFormula/CompletedConormalDeterminantComparison.lean:762` contains `sorry` at line 776 and its docstring's augmentation paragraph is not a finished declaration. Project top-exterior direct-sum declarations concern free modules, without the derived augmentation and algebraic adjunction clauses. They do not attach this item.

## WANTED

None: all sources needed for the split were available locally.

## Corrections and scope

Continued the sandbox's existing proof script and searches instead of discarding the interrupted attempt. It had no written node, report or citations file. The current repository item is still unsplit; no released repair record exists for this item. The statement and its statement dependencies are unchanged. Replaced the formerly implicit cancellation argument by the explicit kernel-normalization calculation, including the order of tensor factors. Explained why arbitrary, possibly nonflat scalar extension preserves this particular exact sequence, and distinguished isomorphisms of exact sequences from comparison chain maps that need not be termwise invertible. Added the cohomology argument giving injectivity of the smooth conormal differential.

Read the fixed chapter and unit records and the current latest blueprint chapter, ancestor statement and proof (main-20261023-1620, commit 7284bb09daf97437d544c51882b325f9c52cd345). This is the generic algebra input in the descendant chain recorded by the item, specifically the completed-conormal comparison's former Steps 8 and 10; it does not replace the unit's contracting-correspondence route. The item is not the unit's key node, so no realization record is changed. Blueprint searches for augmentation determinant, kernel-normalized and conormal determinant found no imported duplicate. DAG searches by tags 0FJI and 0E9Y and by determinant-normalization terminology located the existing smaller inputs reused below.

## Mathlib searches

Read the existing logged results and retained their exact queries and outcomes. Two semantic phrasings returned endomorphism determinants, projective-resolution comparison APIs and exterior powers of degree zero/one, not this assertion. The initial Loogle query used an unknown identifier and remains marked unavailable; the second query `LinearMap.det` succeeded. Additional recorded grep calls confirmed the types in LinearAlgebra/Determinant.lean: LinearMap.det is an endomorphism determinant and LinearEquiv.det is a determinant unit. Neither is a derived determinant-line comparison. All new search entries correspond exactly to executed msearch calls in searches.jsonl; no search was fabricated. Old unavailable service outcomes remain unavailable.

## Not duplicates

No new nodes. Reused the existing exact-sequence determinant, invertible-module duality, kernel normalization, affine determinant system, scalar comparisons, normalization equivariance, regular-sequence facts, signed Koszul comparison and smooth determinant descent nodes.

## Review by NS

I read Stacks more-algebra.tex Tag 0FJB (lemma-det-ses), both the relation-first formula and its hypotheses; Tag 0FJI (section-determinants-complexes), especially the degreewise-surjective quasi-isomorphism diagram immediately preceding lemma-canonical-element-well-defined; perfect.tex Tags 0FJX (lemma-determinant-two-term-complexes) and 0FJY (remark-functorial-det); duality.tex Tags 0E9Y (lemma-determinant), 0E9Z (lemma-fundamental-class-lci), and 0B6V (lemma-lci-shriek). The tag-to-label mapping was checked in stacks-project/tags/tags. The displayed formula in 0E9Y has relation vectors before quotient lifts, and 0FJI uses ordinary tensor symmetry, so these are the same convention, without a Koszul sign from exchanging exterior vectors. I read the statements of every dependency actually cited; citations.json quotes the relevant parts directly. There are no new-node sources to review.

Step 1 uses lem-trf-projective-determinant-exact-sequence for the kernel-first canonical isomorphism and its choice independence, and lem-trf-line-module-duality for invertibility of evaluation. The first node explicitly gives an invertible determinant module, which verifies the rank-one hypothesis of the second. The proof writes the coevaluation composite and verifies its local formula; the inverse determinants from a basis change cancel, and an extra relation vector wedges to zero.

Step 2 uses lem-trf-two-term-kernel-normalization exactly for its Gamma map, differential generator and inverse T; the augmentation is degreewise surjective and a quasi-isomorphism by the given exact sequence. Its kernel is [U -> i(U)], with differential i, so the generator is the image wedge tensored with the dual relation wedge. The Gamma computation is written out rather than hidden in the word cancellation. lem-trf-affine-two-term-determinant states that derived isomorphisms act by the kernel-normalized maps. lem-trf-two-term-perfect-determinant supplies the scheme determinant functor and its exterior model. The affine-local construction in 0FJX identifies these conventions. Taking the ordinary tensor symmetry gives precisely the item's dual-first target line.

Step 3 uses the existing Mathlib leaf lem-weil-pbc-ses-projective-quotient-splits: its projective quotient hypothesis is W, which is assumed projective. The displayed direct-sum inverse verifies split exactness after any scalar extension, so no flatness is inferred. lem-trf-projective-exterior-scalar-comparisons states both exterior and dual comparisons and their compatibility with evaluation and the exact-sequence wedge. lem-trf-two-term-perfect-determinant supplies determinant pullback naturality. These are the exact three assertions needed.

Step 4 uses lem-trf-two-term-normalization-locality-equivariance for its explicit square T_a D(u) = D(v) T_a'. This is applied only to chain isomorphisms of augmentations. The final arbitrary comparison chain map is instead shown to induce identity on H^0 and isomorphisms on the zero remaining cohomology. Thus it is a derived isomorphism, and the composition law from lem-trf-two-term-perfect-determinant applies. No termwise-isomorphism assumption is smuggled into this clause.

Step 5 is elementary substitution of empty wedges in the formulas already established. Checked a=0 (the quotient is an isomorphism), d=0 (the relation map is an isomorphism), and a=d=0 (unit maps). A nontrivial test a=d=1 in V=B^2 gives u-dual tensor (i(u) wedge lift(w)), with positive sign. A split example over Z followed by Z -> Z/2 verifies that the scalar argument does not assume flatness; the zero ring causes no failure of the unit formulas. Different possible ranks for the two resolutions do not affect Step 4's derived-isomorphism argument.

Step 6 uses lem-weil-pbc-regular-sequence-koszul-regular and lem-weil-pbc-regular-sequence-conormal-free, whose statements give Koszul regularity and the specified conormal basis, including the length-zero case. These verify the hypotheses of lem-trf-lci-koszul-duality-determinant-comparison with n=a+d and c=a. Only its unconditional polynomial-chart comparison is used; its additional globally separated relative-duality conclusion is unnecessary. lem-trf-flat-lci-canonical-adjunction supplies exactly the local adjunction line K_i of the item. The Koszul comparison identifies its transitions with the determinant transitions, so equality of canonical identifications, rather than mere isomorphism of lines, is justified.

Step 7 uses lem-trf-lci-determinant-descent-smooth, whose statement explicitly supplies the canonical conormal comparisons, the smooth cotangent augmentation, rank d, relation-first smooth identification and compatibility on overlaps. Regularity and conormal rank were verified in Step 6; the affine determinant normalization assumed by this theorem was supplied in Step 2. Since U_0 is smooth, the conormal complex has H^{-1}=0 and H^0=Omega, giving the exact sequence to which Step 2 applies. Its compatibility with the canonical adjunction line uses the polynomial-chart comparison of Step 6. Equality of sheaf maps gives equality on stalks, and tensoring an equality and an isomorphism with a residue-field extension preserves both; Step 3 identifies their displayed formulas. No flatness of a stalk-to-residue-field map is asserted.

I checked delivery-errors B through E against these files. No new node restates an item clause; all non-elementary inputs are existing cited statements, not their proofs. The only elementary step is the empty-rank substitution. Every step is shorter than 2000 characters (largest about 1200), and the augmentation calculation is one direct application of an existing normalization lemma, not a hidden new lemma. Source hypotheses used here are finite projectivity and the explicit regular polynomial presentation, not properness or a global compactification from 0E9Z: that source's formula is used locally through the existing adjunction and Koszul-comparison nodes. No SGA source is used. No statement dispute was needed.

## Unfinished work

None for this stage-1 item. The cited existing nodes retain their own stage states; this delivery claims a complete one-level natural-language split, not new Lean proofs. The standalone server review_split check passed with zero new nodes. The required full dry run and push are performed after this report is written.
