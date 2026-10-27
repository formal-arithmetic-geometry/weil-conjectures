# Stage-1 report: lem-sfb-open-stack-algebraic-lfp

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-open-stack-algebraic-lfp.json: item split into six proof steps. Not a Mathlib leaf: the search hits state scheme-level properties, not algebraicity of categories fibred in groupoids.
- citations.json: twelve step/node entries with verbatim statement extracts.
- No new nodes; zero new Mathlib leaves. The sandbox also retains searches.jsonl, the actual search output files, and the preparation script.

## Attachments

None. I searched lean/WeilConjectures for the exact item id, OpenSubstack/openSubstack, algebraic-stack terminology and open fibred categories. No project declaration states this item. Scheme-only results and the additional local Sheaf definitions are not finished upstream proofs of the item.

## WANTED

None. All proof sources used are present in literature/stacks-project.

## Corrections and scope

The item statement is unchanged. Its previous proof was empty. The statement uses the project's etale-stack convention, whereas Stacks normally uses fppf stacks. I use the existing etale scheme-representable descent node and the arbitrary-fibred-groupoid smooth calculus; both statements explicitly cover this convention. The local finite presentation conclusion is proved with the item's stated existential smooth-atlas convention, so no uncited independence-of-atlas theorem is used. No full-subcategory hypothesis on j was added: step 2 derives fibrewise full faithfulness from the actual open scheme tests.

Read GOAL.md, the worker role, the stage-1 brief and stage document, SETUP's three blueprint levels and tool-lemma rule, the chapter and unit records, tools/README, and both copies of delivery-errors B--E in full. No repair note exists for this item. The sandbox initially contained no node or earlier split. No repository, launcher, Lean file or unit record was written, and no compiler was run.

## Blueprint and duplicate search

I read the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). This local lemma supports the inherited Picard-stack open invertible locus within the existing alteration/moduli prerequisite route; it changes neither a chapter nor a unit route. blueprint_refs.py ancestor returns None, consistent with the existing null from.node, which is retained. blueprint_refs.py search for 'open substack', 'open immersion' and 'finite presentation', and whole-DAG tag and statement searches, found no imported equivalent of this item. same_as stays [].

The whole-DAG searches found lem-sfb-representable-fibred-category-stack, lem-sfb-fibred-groupoid-representable-smooth-calculus, lem-weil-pbc-open-immersion-monomorphism and lem-sbc-locally-finite-presentation-composition; these are reused. lem-sfb-dm-open-finite-etale-permanence has extra field, smoothness, finite-type, DM and finite-diagonal assumptions, so does not prove the general item. I created no alternative node for any of these facts.

## Mathlib searches

Five searches were run using the required msearch.py command and read from the saved actual output: LeanFinder with the item formulation, LeanSearch with the smooth-atlas formulation, Loogle with '"Stack", "Open"', grep with 'openSubstack|OpenSubstack|IsAlgebraicStack|AlgebraicStack', and a second LeanFinder phrasing about a representable open immersion. All services returned answers. Loogle and grep had zero hits. The semantic hits include locallyOfFinitePresentation_of_isOpenImmersion and locallyOfFinitePresentation_comp, which concern schemes. I read Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean:65--83; composition is already an existing Mathlib leaf. Scheme.LocalRepresentability.isRepresentable handles a set-valued Zariski sheaf glued from open representables, not a fibred groupoid over a stack. The earlier item search records were retained and the actual new results appended. No unrun query was recorded.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs.

## Review by NH

I read algebraic.tex Tag 05UN (lemma-open-fibred-category-is-algebraic), its full proof and the adjoining Tag 05UM atlas construction, as well as Tag 045G (lemma-representable-diagonal) and its explicit fibre descriptions. For the finite-presentation part I read morphisms.tex Tags 01TT and 01TR; the item's 06Q7/06Q3 references are the corresponding stack statements, but the argument only needs their scheme versions on the chosen atlas. There are no new-node sources to review.

Step 1 uses def-sfb-algebraic-moduli-stack for the etale descent hypothesis on Y and lem-sfb-representable-fibred-category-stack for descent on U. I read both full statements: the latter permits arbitrary T-scheme fibres and assumes no stack, smoothness, finiteness or surjectivity condition on U. The specified open fibres satisfy exactly its representability hypothesis.

Step 2 uses the groupoid triple/arrow definition and the existing open-immersion monomorphism theorem. I checked the orientation: with comparison maps 1 and alpha, the equation is j(a)=alpha. The two sections of W lie over the identity of T; monomorphy makes them equal, and the equivalence to a discrete represented groupoid makes the lifting arrow unique. This explicitly proves full faithfulness even though j was not given as a literal inclusion. It is an elementary application of the two cited statements, rather than a new lemma node.

Step 3 again uses the actual triple and arrow definition and the representable-diagonal clause of the algebraic-stack definition. The map (u,a,b) to b a^{-1}, its inverse and the isomorphism supplied by a are written out. Thus the scheme test of U's diagonal is equivalent over T to that of Y's diagonal. I checked the same-base T (not an unrelated absolute product) and restriction compatibility. The use of step 2 is internal to the proof, not a new dependency or a circular citation. This elementary identification warrants no new node.

Step 4 uses the smooth atlas provided by the definition and the statement of lem-sfb-fibred-groupoid-representable-smooth-calculus. I read that whole statement: it preserves representability, smoothness and surjectivity under arbitrary 2-base change with no pre-existing algebraicity assumption on the base-changing category. This is why its application to U is legitimate before concluding U is algebraic. W is a scheme because of the hypothesis on j, and its two projections have their specified meanings.

Step 5 uses the open-immersion definition (isomorphism with the open subscheme) and the pointwise affine definition of local finite presentation. An affine open neighbourhood contained in the open image identifies the source and target ring; zero generators and zero relations give a finite presentation of the identity algebra. This supplies the actual proof of 01TT instead of hiding a cited fact. It uses no quasi-compactness of W.

Step 6 uses the local finite presentation definition and lem-sbc-locally-finite-presentation-composition, whose full statement only requires the two scheme maps to be locally of finite presentation. Choose A at the outset with the required structural composite, repeat step 4 with that choice, and apply composition to W -> A -> S. The conclusion is exactly the item's atlas definition; there is no extra smooth-lfp descent claim.

I checked B1--B10: no new node, all notions are existing definitions, TeX has single escapes after JSON decoding, sources have verified tags and labels, actual searches are recorded, and no finished project attachment was missed. For C1--C8, every external non-elementary input is a cited existing statement, all twelve citation quotes were verified as literal substrings, no proof of a dependency is used, and the off-unit statements are Mathlib leaves. For D1--D5, no item clause is relabelled as a child, and the steps carry the groupoid and affine calculations. For E1--E7 I checked the hypotheses and projections just described and found no statement/source dispute. All steps are under 2000 characters and none hides a standard omitted comparison.

Edge cases: U empty gives W empty and a vacuous local finite presentation check. Taking j an equivalence gives the same atlas argument with W=A. Nontrivial automorphisms of Y are retained; step 2 identifies the whole Isom functor, not just isomorphism classes in Y. An arbitrary non-Noetherian or nonreduced S and a non-quasi-compact open cause no change: all scheme finite-presentation assertions are local and never claim finite presentation or finite type. No algebraicity of U is used to invoke the calculus. There is no SGA source.

## Unfinished work

None within the one-level split. The requested server dry run and direct delivery are the final validation steps; the existing unsplit dependencies remain their own items.
