# Stage-1 report: lem-sfb-graded-fibre-hilbert-functions-finite

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-graded-fibre-hilbert-functions-finite.json`: statement, split; no Mathlib match for the entire assertion. Seven proof steps, all dependencies reused.
- `citations.json`: verbatim statement quotations for every proof-step citation.
- `searches.jsonl`: actual results recorded by the authorized Mathlib search command.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for Hilbert-function and generic-freeness terminology. The Euler-characteristic Hilbert function in `AlgebraicGeometry/Modules/Ample.lean` concerns a different object and does not state this item. The generic-freeness declarations are helper results, not attachments for the whole item.

## WANTED

None for this split. The Stacks sources needed for the proof are present locally. I did not rely on the archival Bourbaki PDF mentioned by the parent.

## What needed repair

The incoming item was a correct statement with an empty proof. Its reference to flat stratification alone does not yet prove finiteness of *whole* Hilbert functions: separate finite ranges for every degree would not imply a finite range of functions. I wrote the simultaneous argument. A single application of generic freeness frees the entire graded module, so every degree is a finite projective summand on the same nonempty open of an integral base. Each rank is then constant there. No statement change or STATEMENT-DISPUTED was necessary.

The item has no imported blueprint ancestor: `blueprint_refs.py ancestor` reports `None`. I retained that inherited provenance, filled `same_as` after searching the whole imported blueprint, and explained the exact Hilbert-construction role in `split_report.blueprint`. Its unit is `sk-thm-sf-ctf-stability`; this is a subsidiary Hilbert-scheme construction in the recorded alteration branch, not a replacement of that unit's six-functor route. It is not the unit's key node, so no unit file is modified.

## Unfinished work

None within this one-level split. No new unsplit prerequisites were needed.

## Not duplicates

No new nodes. Existing helpers were found by whole-DAG searches for Tags 0ASY, 00K0, 051R, 00NX, generic freeness, finite projective rank, finite minimal primes, affine module evaluation, coherence, and Noetherian induction. Blueprint searches for Hilbert function, graded module, generic freeness, generic flatness, and flat stratification found no blueprint node stating this item. The generic graded Hilbert-polynomial node is over a field and gives eventual polynomiality; it cannot replace the finite-family assertion over a base.

## Mathlib search assessment

Ran the authorized msearch command with LeanFinder for the entire fibre-function statement, Loogle for `Module.rankAtStalk, Module.Finite`, grep for `hilbertFunction|hilbertPoly|genericFree` in RingTheory, and LeanSearch with a second phrasing through generic freeness. Read all returned hits. LeanFinder returned homogeneous-submodule and graded finite-type facts; Loogle returned rank-at-stalk identities for one finite flat module; grep returned `Polynomial.hilbertPoly` (a polynomial attached to a rational generating function); LeanSearch returned Noetherian finiteness and rank on the free locus. None states finiteness of the range of all graded fibre dimension functions. Existing item searches are retained; the new records quote the command's actual summaries. No additional helper nodes were created, and no unperformed searches were recorded.

## Review by Q60

I read the chapter and unit records, the item and its parent rank-stratum statement, and the complete delivery-errors B--E checklist. For the mathematical route I read `more-morphisms.tex`, Tag 0ASY (`lemma-generic-flatness-stratification`), including its Noetherian-induction proof; `algebra.tex`, Tag 00K0 (`lemma-graded-module-fg`), Tag 051R (`lemma-generic-flatness-Noetherian`), Tag 00NX (`lemma-finite-projective`), Tag 00FR (`lemma-Noetherian-irreducible-components`) and the Noetherian definition/permanence paragraphs; `coherent.tex`, Tag 01XZ (`lemma-coherent-Noetherian`); and `schemes.tex`, Tag 01HV (`lemma-spec-sheaves`), with the affine finite-type criterion in `properties.tex`, Tag 01PB. The explicit graded adaptation and maximal-counterexample presentation are agent-written and are labelled as such. There are no new nodes whose sources require separate verification.

Step 1 uses precisely `pqf-def-coherent` for finite type and coherence and `pqf-lem-coherent-ft-locnoeth` for the equivalence on locally Noetherian schemes. I checked that arbitrary nonnegative generator degrees cause no problem: the equation for the monomials is sum(alpha)=d-b_j, and there are none if b_j>d. Taking homogeneous parts justifies generation of each piece. No new graded-piece lemma is needed because its monomial proof is written out.

Step 2 uses `pqf-def-locnoeth` and the quasi-compactness definition to get finitely many suitable affine opens. The cited affine free-evaluation node explicitly says that an epimorphism defined by finitely many sections is equivalent to surjectivity on sections. With its morphism equal to the identity, its source, target, and algebra are exactly our affine chart and its structure sheaf, and the homogeneous pieces are quasi-coherent by assumption. This avoids an unjustified use of right exactness of arbitrary global sections. `lem-sbc-affine-module-germ-localization` really identifies affine sections localized at the point with the stalk; the remaining tensor identity is written by fractions. Thus the ring-module fibre dimensions are exactly the dimensions in the item, not just isomorphic vector spaces over an unrelated field.

Step 3 uses the maximal-submodule clause of `lem-weil-pbc-noetherian-finite-module-acc` for M=A. A counterexample ideal is therefore chosen maximally, with the induction hypothesis valid for every strictly larger ideal. `lem-weil-pbc-noetherian-finitely-many-minimal-primes` explicitly supplies the finite irreducible-component decomposition after passing to A/I. I checked quotient Noetherianity directly by lifting ideals and generators. If I is not prime every minimal prime over it is strictly larger, so the finite union of the induction hypotheses suffices. This proves that the only remaining bad base would be a domain; it does not assume that the original base is reduced or irreducible.

Step 4 uses exactly `lem-pur-noetherian-algebra-module-generic-freeness`. Its ring is the Noetherian domain A/I, its algebra is finite type because the images of the x_i generate, and its module is finite because the images of the e_j generate. The statement gives freeness of the whole module, with a possibly infinite basis. It gives a single nonzero denominator for all degrees. No geometric generic-flatness statement is misapplied to an infinite-rank O-module, and no finite-rank hypothesis is silently added.

Step 5 uses the direct-summand characterization in `def-weil-pbc-projective-module` and the actual statement of `lem-weil-pbc-finite-projective-rank-locally-constant`: finite free stalks and local constancy of their ranks. The finite-support argument shrinks the ambient infinite free module to a finite free retract for each finite degree piece, proving exactly the finite-projective hypothesis. I checked the retraction maps: inclusion into the chosen finite coordinate summand followed by the restricted degree projection has identity composite. The domain's zero prime belongs to every nonempty basic open; this makes every locally constant rank equal to its value there, separately for all degrees on the same open. Tensoring a free stalk basis to the residue field proves the rank/dimension equality used here. This is an elementary retract argument, not an extra lemma hidden in a long step.

Step 6 is the induction-closing argument. The lift of the nonzero denominator makes I+(a) strictly larger; the complement is exactly its vanishing set. I wrote both tensor maps proving preservation of residue-field fibres under the quotient, and explained inversion of the denominator at the open points. Adding the single generic function to the finite complement set contradicts maximal badness. Step 7 takes a finite union over the actual finite affine cover and uses the earlier stalk comparison. These steps are elementary set and tensor calculations, not applications of unstated flatness or descent results.

I checked empty S (empty H), zero L, B_1=0 (no positive-degree algebra generators), homogeneous generators in positive degrees, nonreduced bases such as Spec(k[epsilon]/epsilon^2), and a torsion example M=(A/(t))[x] over A=k[t]. In the last example generic freeness gives the zero module on D(t), while the distinct special function is retained on V(t); the proof does not incorrectly infer global flatness. No properness, dimension bound, finite field, or degree-zero generation of L is used. The new proof leaves the item statement and all maintainer-owned fields unchanged. Every citation's full statement was reopened and copied verbatim to citations.json. All steps are below 2000 characters. There are no new nodes restating clauses, new hollow definitions, new sources outside the permitted route, or unsplit helper proofs. Off-unit generic tools are declared in split_report.tool_uses for review.
