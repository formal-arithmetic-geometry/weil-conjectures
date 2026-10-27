# Q84 stage-1 report: lem-sfb-rees-presentation-blowup-immersion

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-rees-presentation-blowup-immersion.json`: statement, now split into six proof steps; no Mathlib match for the whole item.
- `citations.json`: one verbatim statement quotation for each of the fourteen step/node citations.
- `report.md`: this report. `searches.jsonl` was written by the mandatory search command; `prepare.py` is sandbox-only preparation code.

New nodes: 0. New Mathlib leaves: 0. The unchanged statement already has all its statement dependencies. No unit or chapter record is changed.

## Attachments

None for this item. I searched all of `lean/WeilConjectures` by the blueprint id and by Rees/blowup/relative-Proj concepts. `AlgebraicGeometry.Scheme.IdealSheafData.relProjReesIso` (RelativeProj/Rees.lean:187) supplies the canonical Rees case, while `AlgebraicGeometry.Scheme.GradedAlgebraData.relProjIsoOfIso` and `isClosedImmersion_relProjMap` (RelativeProj/Functoriality.lean:119 and :150) supply other ingredients. No single declaration or collection found states every clause for the supplied family theta and the arbitrary graded surjection phi, including the specified composite chart map and uniqueness. These ingredients therefore justify reusing their existing DAG nodes, not attaching the entire item.

## WANTED

None. All sources needed are in the read-only repository.

## What was wrong or changed

The item was unsplit. Its statement is correct and is preserved verbatim, with every hypothesis and conclusion intact. I filled its proof and exact dependency union, added the searches actually run in this session, and preserved all maintainer-owned fields. The inherited blueprint ancestor is null; `blueprint_refs.py ancestor` confirms this. The inherited place describes the alteration/projectivity prerequisite; I retained it and explained its realization in split_report. The current blueprint unit and fixed chapter were read; this is algebraic-geometric projectivity bookkeeping below their alteration input, not a replacement of the six-functor route.

A possible but unnecessary split would create a new blowup/relative-Proj comparison or surjective-Proj immersion node. Whole-DAG and blueprint searches found the existing canonical comparison `lem-sfb-blowup-rees-symmetric-presentation`, the construction `def-sfb-relative-proj-iso-of-graded-iso`, and `prop-nagata-relative-proj-functoriality`. I reused them. The quotient chart statement also already exists as `lem-sfb-graded-proj-quotient-twist-comparison`. No elementary fact was promoted to a node.

## Not duplicates

No new nodes. Existing stronger or more specific tools were cited rather than duplicated. The canonical blowup comparison is not a restatement of this item: it concerns the canonical sheaf Rees algebra, constructs the canonical symmetric surjection, and does not assert the immersion for an arbitrary locally Rees presentation and arbitrary supplied phi.

## Mathlib searches and blueprint searches

I ran all searches through `/home/ubuntu/weil-launcher-all/batch2/msearch.py` for Q84 and this item, and read their results. The saved log records two LeanFinder phrasings, LeanSearch, Loogle, and two grep queries. LeanSearch found `reesAlgebra`, `adjoin_monomial_eq_reesAlgebra`, absolute Proj material and affine closed immersion results. LeanFinder found absolute Proj charts and maps. Loogle returned no hits for the combined Proj/IsClosedImmersion query. The broad geometry grep found no relative-Proj or blowup theorem. The second grep found absolute `Proj.map_comp` (Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Functor.lean:210), whose file I read; it does not state the whole item. Thus the whole item is not a Mathlib leaf. Earlier searches supplied with the imported item were retained, and none was invented or relabelled as a search run by Q84.

I ran blueprint searches for relative Proj, Rees, gluing, blowup, and the relevant morphism/transitivity tags, as well as DAG searches for 02NS, 01NQ, 07ZK and related chart formulas. These support the reuses above. I checked the transitive dependency reach of each candidate comparison/quotient/functoriality node: none reaches this item.

## Review by Q84

I read coord/delivery-errors.md B--E in full, the stage-1 brief, SETUP's three levels, GOAL, the unit and chapter, and the current main-20261015 unit. For the mathematical source I read divisors.tex Tag 02NS (`lemma-blowing-up-projective`) and constructions.tex Tags 01MY (`lemma-morphism-proj`), 01MZ (`lemma-morphism-proj-transitive`), 01NQ (`lemma-glue-relative-proj`), and 07ZK (`lemma-surjective-generated-degree-1-map-relative-proj`). The proof retains the source's Rees/relative-Proj/projective-bundle route. There are no new nodes requiring separate sources or searches.

Step 1 uses the statement of `lem-sfb-sheaf-rees-symmetric-presentation` for the graded coefficient isomorphisms alpha and their affine restriction compatibility, and the statement of `lem-sfb-blowup-rees-symmetric-presentation` for e0 and its specified charts. I opened both node files, including the latter's proof to rule out a dependency cycle, but the step takes only their stated conclusions. Both statements allow every quasi-coherent ideal; finite type is available but unnecessary here.

Step 2 composes the given theta with alpha inverse, explicitly checks the restriction square by cancellation, and uses the existing definition of the canonical graded-isomorphism-induced Proj map for F and its fraction formula. The gamma maps and inverses meet exactly that definition's base-linearity, grading, and restriction conditions. The calculation alpha gamma = theta determines the required direction of e and its chart formula. `def-nagata-relative-proj` supplies its scalar-defined structure maps, so identity on scalars proves that e is over X. This does not cite a definition for an unstated theorem: the construction used is explicitly specified by that definition, and its source-library realization is already closed.

Step 3 uses the affine-basis theorem for refinements inside arbitrary V intersect W, the existing canonical Proj construction's stated affine restriction compatibility, and the morphism-gluing theorem's explicit uniqueness clause. These are exactly what their opened statements say. Pulling back the affine cover gives an open cover of B. Equality is checked on these opens; no affine or quasi-compact overlap hypothesis is introduced. Uniqueness is for an isomorphism respecting the specified charts, not uniqueness of all isomorphisms of the underlying schemes.

Step 4 writes out how degreewise affine surjectivity gives total affine surjectivity: only finitely many homogeneous summands occur. Clause (3) of `prop-nagata-relative-proj-functoriality`, whose full statement I read, then gives q as a closed immersion. Both graded algebras are quasi-coherent, by the item's assumptions and the canonical symmetric-algebra input already in its statement. No extra Noetherian or integrality assumption is needed. This generic tool is recorded in split_report.tool_uses; it is not an alternative proof route.

Step 5 checks the generation-in-degree-one hypothesis of `lem-sfb-graded-proj-quotient-twist-comparison` using the explicit powers-of-image grading in `def-trf-canonical-symmetric-graded-algebra`. The quotient node explicitly states the inverse-image standard opens and the fraction comorphism used, so the composite formula is justified without appealing only to a theorem name or its hidden proof. It is applied to phi_V, whose total surjectivity was established in Step 4. The structural-map definition and morphism-gluing uniqueness prove projection composed with j = b. `def-trf-projective-bundle-morphism` explicitly identifies Proj(Sym I) with the projective bundle; its finite-type and quasi-coherent module conditions are present. I take no invertibility or local freeness of I from the word bundle.

Step 6 is elementary from the two explicit defining properties in `def-weil-closed-immersion`: a source isomorphism preserves the closed image and makes the sheaf comorphism change by an isomorphism. This avoids introducing a new composition lemma or silently relying on one. The argument is written in the step. All fourteen uses have verbatim matching citations in citations.json. Each proof step is shorter than 2000 characters; none hides an additional lemma with its own hypotheses.

For small cases, I tested I=0: its Rees algebra has no positive-degree elements, so its Proj and the blowup are empty, as is Proj(Sym 0), and uniqueness and the immersion remain correct. For I=O_X, the Rees algebra is O_X[t] and Proj is X; an arbitrary supplied graded presentation can change the algebra identification, but the prescribed theta still fixes the intended e. For a nilpotent ideal, positive-degree Rees elements are nilpotent and the blowup can be empty; the fraction and gluing arguments allow this. I also checked a zero base ring, empty X, zero standard opens, and the ideal (epsilon) in k[epsilon]/(epsilon^2). No cancellation by a homogeneous element is used. Arbitrary nonaffine overlaps are addressed explicitly in Step 3. These checks reveal no statement dispute.

The B checklist is satisfied by creating no duplicate, elementary, or clause-copy nodes and preserving the exact TeX. The C checklist is satisfied by opening every cited statement and recording the actual quoted property, with acyclicity checked. The D checklist is satisfied by the explicit gamma construction and chart calculation assembling previously available tools. The E checklist is satisfied by the hypothesis and edge-case checks above.

## What remains unfinished

No mathematical portion of the split remains. The required server dry run and direct delivery follow this report. I have written no Lean and run no compiler, Lake, build, local preflight, or local DAG/review checker.
