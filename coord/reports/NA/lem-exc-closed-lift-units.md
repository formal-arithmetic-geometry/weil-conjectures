# lem-exc-closed-lift-units — stage 1

## Files written

dag/nodes/sec-smooth-purity/lem-exc-closed-lift-units.json: statement, split; four proof steps, no exact Mathlib match for the item. citations.json records every step citation. searches.jsonl contains the actual msearch runs.

## New nodes

None. No new Mathlib leaves; three existing theorem leaves and one existing definition leaf are reused.

## Attachments

None. Searched WeilConjectures in the read-only slopmaster2 source for the exact blueprint id and closed-lift, ind-etale-lift, and unit-lifting concepts. The results concern other lifts and ind-etale constructions, not this colimit and its unit-reflection assertion. The item has lean_audit state none. Master was also searched as reference material; its sorry declarations were not treated as finished proofs.

## WANTED

None.

## Corrections and scope

The imported statement is correct and unchanged. The imported one-paragraph proof omitted explicit citations for stage representatives, localization extension and etale finite presentation of the new stage. These are repaired by existing DAG leaves, rather than new nodes that duplicate them. The final step exhibits the inverse and cocone equality. The chapter and unit records were read: this is an auxiliary ring lemma below the closed-immersion branch of the open–closed triangle, not the unit's key statement; no unit or chapter record was changed.

## Not duplicates

No nodes were created. Whole-DAG searches for localization with etale and for filtered ring colimits found lem-weil-pbc-etale-algebra-finite-presentation-localization and lem-pc-filtered-colimit-commrings-elementwise. The directed-set finite-data node lemma-nagata-filtered-colimit-finite-data would impose the wrong shape of index, so it was not used. The statement of lem-weil-pbc-ind-etale-stability gives ind-etale stability, not finite-presentation etale localization, so it was not used. Blueprint searches for localization, filtered colimit, units, closed-lift-units and invertible if found no second blueprint statement of the item; same_as is [].

## Mathlib searches

All recorded searches were run with msearch.py and their actual outputs read. Two semantic phrasings for the item found standard etale presentations and RingHom.Etale results, not unit reflection for this lift. Supporting-localization searches found Algebra.Etale.instAway; its source at Mathlib/RingTheory/Etale/Basic.lean:256 and the finitePresentation field at 208 agree with the existing localization leaf. LeanSearch returned Internal Server Error and is recorded unavailable. Loogle and LeanFinder worked. No unavailable response was recorded as absence.

## Review by NA

I read the master blueprint item (order 1840), its lift definition and filteredness node, the chapter and unit, and Stacks algebra.tex Tag 00CP, proposition-universal-property-localization, Tag 00U1, definition-etale, and Tag 00U2, lemma-etale (1),(2). I also read the filtered-set description in categories.tex Tag 04AX and the underlying-set formula of sheaves.tex Tag 008N cited by the existing ring-colimit leaf. No new statement needs a source review.

For step 1 I opened def-exc-ind-etale-closed-lift: it supplies precisely the factoring objects, their compatible arrows, the algebra colimit and its map to the fixed target ring. I opened lem-exc-closed-lift-filtered: its statement says that very category is filtered. I opened lem-pc-filtered-colimit-commrings-elementwise: clause (1) supplies every stage representative for a small filtered category and a ring colimit. I checked both hypotheses explicitly: finite presentations and maps into the fixed target form a set, allowing a small skeleton, and the common-successor argument makes the algebra colimit a ring colimit. No directed-poset assumption is made. The identity object ensures the index is nonempty via filteredness. The common base map in the universal-property argument uses compatibility of all stage maps and their A-algebra transitions.

For step 2 I opened def-weil-ring-localization-away and lem-weil-pbc-ring-localization-universal-property. The former supplies fractions and the ring structure, the latter the extension formula and its restriction to B. The multiplicative subset consists of powers of b, all of whose images are units because beta(b) is a unit. The displayed formula also shows the extension respects the A-structure. This is not an unsupported assertion that a map exists.

For step 3 I opened lem-weil-pbc-etale-algebra-finite-presentation-localization. Clause (2) gives etaleness over A after localizing B at any element b, and clause (1), reapplied to that localized algebra, gives finite presentation. These are exactly the two object hypotheses in def-exc-ind-etale-closed-lift. Compatibility beta_b lambda = beta, established in step 2, is exactly the arrow hypothesis. The tag 00U2 is carried by this cited node. I did not infer finite presentation merely from ind-etaleness or apply any prime-localization theorem.

For step 4 I opened the localization definition again: b/1 has inverse 1/b. The lift definition gives the cocone and hence its transition equality. Multiplying and applying its ring map explicitly yields both inverse identities; this step is elementary and uses no additional localization or unit lemma. All quotes in citations.json are copied verbatim from the cited statements, including the clauses actually used.

I checked B=0 and b=0: the hypothesis then forces the target ring to be zero, and localization at zero is the zero ring; its unit identities still hold. For b already a unit the same construction works and adds no hypothesis. For I=0 and for the zero quotient target no proper-ideal or nontrivial-ring assumption is needed. No Noetherian, locality, finite target presentation or injectivity assumption occurs. The inverse is required only in the colimit, not in the original stage B; for example a nonunit integer can map to a unit in a residue field and be inverted at the next stage. Thus no hidden unit-reflection claim for B itself is used.

I checked B–E of delivery-errors against the proof: no new nodes or relabelled clauses, all non-elementary ingredients are cited statement clauses, dependency union agrees with the steps, and the route and original statement are preserved. No statement dispute, source error or unfinished argument remains. No Lean was written or compiled, and nothing was pushed.

## Unfinished work

None for this one-level split. Its filteredness dependency remains a separate item for its own worker. Independent second reading and delivery remain the next worker's responsibility.

## Second reading by NA

- Item statement: compared verbatim with master blueprint lem-exc-closed-lift-units, order 1840, and read def-exc-ind-etale-closed-lift, order 1838; agrees, including the ideal and ind-etale quotient-algebra setting inherited through the definition. No statement dispute.
- Step 1: opened the statements of def-exc-ind-etale-closed-lift, lem-exc-closed-lift-filtered and lem-pc-filtered-colimit-commrings-elementwise; the latter clause (1) applies after the explicitly justified small-skeleton and underlying-ring reductions. Checked Categories 04AX (section-directed-colimits), Sheaves 008N (section-abelian-presheaves-functorial), and Mathlib Concrete.isColimit_exists_rep (ConcreteCategory/Basic.lean:130) with CommRingCat.FilteredColimits.forget_preservesFilteredColimits (Ring/FilteredColimits.lean:363). Verdict: correct; compatible ring maps restrict to the same map on A through a common successor, and the resulting algebra universal property supplies existence and uniqueness.
- Step 2: opened def-weil-ring-localization-away and lem-weil-pbc-ring-localization-universal-property; compared with Algebra 00CO (definition-localization) and 00CP (proposition-universal-property-localization), including its fraction formula. Verdict: correct; all powers of beta(b) are units, and the restriction identity proves A-linearity without an extra hypothesis.
- Step 3: opened def-exc-ind-etale-closed-lift and both clauses of lem-weil-pbc-etale-algebra-finite-presentation-localization; compared with Algebra 00U1 (definition-etale), 00U2 (lemma-etale), clauses (1),(2), and Morphisms 02GJ (lemma-etale-characterize). Also read Mathlib Etale/Basic.lean:204-256. Verdict: correct; localization and composition give etaleness, the definition gives finite presentation, and beta_b lambda = beta is exactly the indexing-arrow condition.
- Step 4: reopened the two cited definition statements and checked their fraction multiplication and colimit cocone identities. Verdict: elementary as marked; applying the cocone ring map to (b/1)(1/b) = (1/b)(b/1) = 1 gives the claimed inverse explicitly.
- New nodes: none; the sandbox contains only the existing item node. B1-B7 and duplicate/Mathlib-leaf checks for new nodes are therefore vacuous. All three supporting theorem nodes and the localization definition are existing Mathlib leaves, not new obligations or restatements of the item.

Checked the chapter and unit source files: this remains the auxiliary localization argument in the closed-immersion branch of the open-closed triangle. Checked source checkouts read-only for the item id and closed-lift/ind-etale-lift names; no exact closed attachment was found. The master checkout was reference material only. Checked every citations.json entry against the actual full cited statement: all nine quotes agree verbatim, and the proof dependency list is precisely the union of step citations.

Small cases: for b = 0 the unit-image hypothesis forces the target ring to be zero, and B[1/0] is the zero ring with the same inverse identities; for B = 0 the same argument applies. For a field stage, nonzero b is already invertible and the construction still works. For I = 0, the identity stage A, and presentations with zero variables or zero relations, no step imposes a nontriviality or positive-size condition. Empty spectra are covered by the zero-ring case. No locality, Noetherian hypothesis, or unit reflection at an individual stage is used.

Changes: appended this independent second-reading record only. The statements, four proof steps, node set and citation quotes needed no repair and were left unchanged. No Lean files or compiler/build tools were used, and no manual git command was run.
