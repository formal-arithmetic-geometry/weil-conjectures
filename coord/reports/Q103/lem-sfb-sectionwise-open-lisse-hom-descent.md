# Q103 stage-1 delivery: lem-sfb-sectionwise-open-lisse-hom-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-sectionwise-open-lisse-hom-descent.json: statement, split into seven steps; no Mathlib match.
- citations.json: verbatim statement quotations for every node cited by every proof step.
- report.md: this report. searches.jsonl contains the actual msearch results; write_split.py is sandbox-only preparation material.

New nodes: 0. Mathlib leaves: 0. No unit realization is changed: this auxiliary node is not the unit's statement node.

## Attachments

None. Searched the whole project WeilConjectures tree by the exact blueprint id and by restriction/lisse/full-faithfulness notions. DenseOpen.lean:93, AlgebraicGeometry.WeilSheaf.upperStar_map_bijective_of_isLisse, requires smooth curves over a finite field, dense quasi-compact opens, and Weil sheaves with algebraic-closure coefficients. It does not state this arbitrary-scheme arbitrary-condensed-ring assertion. Other geometric lisse-monodromy results have the same coefficient and geometric mismatch. No attachment is claimed.

## Literature wanted

None. The item is already explicitly an agent-formulated auxiliary assertion rather than a verbatim blueprint theorem. The general tools needed for it are available locally.

## Audit of the imported material

The item was unsplit and the sandbox had no previous item, report or split. There is no released repair note for this id. The statement is retained without alteration; no STATEMENT-DISPUTED finding. The chapter route and the unit record were read. The current main-20261015 direct-images proof paragraph (3) gives the open-direct-image context, rather than a proof of this general ringed-site auxiliary assertion. The new proof is correctly marked agent-written.

The inherited blueprint ancestor is null. tools/blueprint_refs.py ancestor explicitly reports None for this created-node chain. The inherited via chain is retained; from.place now specifies the exact intended direct-images paragraph and local Hom argument. Whole-blueprint searches for finite free matrix, internal hom sheaf, and coefficient restriction found no equivalent statement. The internal-hom search found lem-pur-lisse-morphism-rigidity, whose finite-coefficient finite-type rigidity conclusion is different; it is not a duplicate or an adequate replacement. The coefficient-restriction result is an unrelated finite-origin exchange theorem. Existing general matrix and Hom-sheaf nodes are reused, so no duplicate helper nodes are introduced.

Five fresh msearch commands were run and their actual queries/results are recorded in searches.jsonl and appended to the item's existing historical searches. LeanFinder was tried with two different descriptions; Loogle, LeanSearch and grep also ran successfully. I read Mathlib/Algebra/Category/ModuleCat/Sheaf.lean:74 and 221 and Sheaf/PullbackFree.lean:55. The former results concern a forgetful fully faithful functor or Hom out of a locally bijective presheaf map on one fixed site. The latter concerns sections of pushforward along a final site functor. They do not prove the coefficient-specific open-restriction assertion. The search hits about locally constant condensed embeddings and scheme module restriction definitions also lack this assertion. No unsuccessful service was recorded as evidence of absence.

## Review by Q103

I read the item, the main blueprint paragraph (3), the complete statements of all proof dependencies, Stacks sites-modules.tex Section 04TT (internal Hom), Tag 03EM lemma-internal-hom, its localization lemma, Definition 04IX definition-localize-ringed-site, and sites.tex Tag 04TQ lemma-glue-maps. I also read schemes.tex Tag 01IT lemma-basis-affine-opens and its warning that affine intersections need not be affine, and more-morphisms.tex Tags 094T, 094U and 0951 for the weakly-etale site tools. Hemo--Richarz--Scholbach Example 3.1 on p. 6 was checked for coefficient context; its derived-dualizable use of “lisse” is not substituted for the finite-locally-free definition in this item. There are no new nodes whose sources require independent review.

Step 1 uses def-weil-pbc-internal-abelian-sheaf-module-equivalence precisely for the equivalence preserving underlying sheaves, sections and restriction maps. It uses lem-sfb-coefficient-sections-localization for the pro-etale slice identification, inverse-image restriction and actual coefficient-section compatibility, valid for arbitrary commutative condensed rings. This avoids incorrectly using the admissible-coefficient-only cartesian-coefficients theorem. The module-pullback definition supplies the scalar tensor formula; the explicit map along the coefficient isomorphism identifies it with slice restriction. Thus the later ringed-module statements apply to the actual internal objects and maps of the item.

Step 2 uses def-sfb-lisse-coefficient-module for finite free local frames with varying ranks, the site definition for base change and composition of covers, affine-opens-basis for arbitrary schemes, and source-local weak-etale stability to retain site objects. The refined covering condition is verified directly from the witnesses of the original pro-etale cover: all its finite affine witnesses are members of the family of all affine opens. I corrected an initial draft that needlessly appealed to quasi-compactness when the original covering witnesses give the result directly. This step imposes neither global quasi-compactness nor quasi-separatedness, and does not assert affine overlaps.

Step 3 takes the complete global free-matrix bijection and its explicit section formula from lem-sfb-ringed-site-free-matrix-scalar-extension. The sites here are the small localized sites with their final objects and sheaf tensor products, so its hypotheses hold; the internal/sectionwise equivalence was established in Step 1. Only the Hom-coordinate clause is needed, not a derived comparison or arbitrary tensor-of-sections formula. Coefficient-sections-localization identifies actual entrywise restriction. The coefficient hypothesis is used on the affine T; the target T_V is permitted to be nonaffine. Entrywise inversion of a finite matrix is elementary once this bijection is cited.

Step 4 invokes lem-pur-sheaf-hom-is-sheaf exactly for its clauses (2) and (3), including localized morphism sets and their sheaf separatedness/gluing. On a possibly nonaffine overlap P, both morphisms are compared on affine opens T, expressed in the same bases inherited from W_i; their equality follows from Step 3. This resolves the basis-change issue before applying descent. The cited node is about module sheaves; the equivalence in Step 1 supplies that setting. The site axioms used in Step 2 guarantee the required overlap and base-changed coverings. Restriction of the glued map equals u by the same Hom-sheaf separatedness on V.

Step 5 uses the same Hom-sheaf statement for equality of global morphisms after equality on a cover. The coefficient injectivity already proved in Step 3 yields local equality. The proof establishes both sides of bijectivity and shows that another cover/bases produce the identical global extension. Agreement on affine overlap refinements is established before arbitrary further restriction; it is not asserted merely by the word “naturality”.

Step 6 uses only the stated natural module composition isomorphisms of sk-def-sfb-module-pushforward-pullback. The formula with c_M and c_N explicitly checks the square and its direction. Applying the established Hom injectivity on X' is licensed by the separate coefficient-section hypothesis and lisse pullbacks on X'. No claim that pullbacks of affine charts remain affine is made. The elementary designation refers to this short functoriality-and-uniqueness calculation, not an uncited base-change theorem.

Step 7 uses the matrix node's explicit singleton-zero-group clause and the Hom sheaf's empty-cover axiom. Checked zero source rank, zero target rank, zero coefficient ring, empty X, identity V=X, and V empty. In the last case the section-bijection hypothesis forces zero coefficient sections on each affine test, so the matrix and gluing argument still works. V empty with a nonzero ring on a nonempty affine does not satisfy the assumptions; it is not a counterexample. No constant global rank, connectedness, normality or finite-type assumption enters any step.

I checked delivery-errors B--E individually: no new unsplit node contains a proof; notions and their definitions are already cited in the unchanged statement; no new Mathlib leaf or unverifiable search is claimed; quotes in citations.json are literal statements, not proof snippets; no dependency is being used for more than its statement says; existing tools replace potential duplicate nodes; every non-elementary ingredient is cited. Steps carry the matrix-extension and overlap argument, so no clause is moved wholesale into a new node. Every step is below 2000 characters. Cross-unit tools are declared individually in split_report.tool_uses with their purpose; no top-level maintainer tool_uses field is written.

## Not duplicates

No new nodes. No duplicate-node pairs require justification.

## Unfinished work

None in the one-level split. The existing dependency nodes retain their own proof/status responsibilities.

## Validation

The first server review_split invocation passed with 0 new nodes. The complete delivery dry run and final push are performed after this report is written; their terminal results are the delivery evidence.
