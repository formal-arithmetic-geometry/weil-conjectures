# Stage-1 report: lem-sfb-space-finite-type-eventually-proper

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-finite-type-eventually-proper.json: statement, split into eight steps; Mathlib verdict no match. No new nodes and no Mathlib leaves.
- citations.json: one verbatim statement quotation for every step/node pair (35 entries).
- report.md: this report. searches.jsonl records the actual search commands; prepare.py is sandbox-only preparation scratch.

## Attachments

None. Searched the exact blueprint tag and eventual-properness terminology under lean/WeilConjectures. AlgebraicGeometry.exists_isProper_baseChange_of_isLimit in AlgebraicGeometry/EventuallyProper.lean proves the scheme version, not the algebraic-space statement: its X₀ and Y₀ are Scheme. This does not attach this item. No compiler or Lean editing was used.

## Wanted literature

None.

## What was wrong and what changed

The item had no proof. Its statement is correct: Stacks spaces-limits.tex Tag 08K1, in Situation 084W with B_i=Y_i=T_i, assumes local finite type rather than finite presentation. The split preserves the statement exactly. The finitely presented nodes lem-sfb-space-eventually-proper and lem-sfb-space-qcqs-base-eventually-proper cannot justify it. Likewise lem-sfb-space-descend-separated requires finite presentation and cannot be used here. Instead steps 1-2 apply the existing, stronger closed-immersion descent node to the diagonal, as Tag 0851 prescribes.

The inherited blueprint.from.node is null. tools/blueprint_refs.py ancestor returns null for this item; I retained the exact inherited provenance and its long explicit from.place and via chain. The ultimate named blueprint proof is det-thm-sf-ctf-stability-direct-images, proof (3). I read its current text and the current unit and chapter in literature/blueprint/latest. The latest proof now gives a shorter direct-image argument; this inherited branch is retained as the supporting approximation input, without changing the human's unit or chapter. No unit realization fields are edited because this is not its key node.

## Searches and duplicate audit

Read the existing Mathlib search records in the live item. Ran the required msearch leanfinder, loogle, grep and leansearch queries, then a second semantic phrasing. Every query and actual result is appended to mathlib_searches and logged by the search command in searches.jsonl. All services responded. Read the returned signatures: projective-spectrum properness, scheme properness and its base-change stability, eventual affineness/quasi-affineness, and equality of scheme morphisms do not state this algebraic-space limit theorem. Read Mathlib/AlgebraicGeometry/Morphisms/Proper.lean, including IsProper, isProper_eq and its stability instances.

Searched the full DAG by 08K1, eventual properness, 0850/closed-immersion descent, weak Chow, diagonal local finite type, proper cancellation and point-map continuity. Ran blueprint_refs.py search for eventual properness and 08K1 (the latter has no imported blueprint match), and searched the full current blueprint. All needed facts already have nodes. No new node is elementary, a duplicate, a clause of the item, or an overlooked Mathlib lemma, because none is created.

## Not duplicates

No new nodes. The item's hypotheses differ from the existing eventual-proper nodes by not requiring finite presentation. lem-weil-pbc-eventually-proper concerns schemes; lem-sfb-space-fixed-base-eventually-separated concerns a fixed target and is not needed; lem-sfb-space-descend-closed-immersion is the correct general local-finite-type input.

## Review by Q20

I read spaces-limits.tex Tag 08K1 (lemma-eventually-proper) and Situation 084W, including its uses of Tags 0851 and 0850. I read the actual diagonal reduction in 0851, the closed-immersion statements and proofs in 0850 and in limits.tex Tag 01ZP, and spaces-cohomology.tex Tag 089J (lemma-weak-chow). I also read spaces-morphisms.tex Tag 03HK for the diagonal, Tag 073B for qcqs permanence, Tag 04NX for proper cancellation, and Tag 08AJ for the final universally closed image argument. There are no new node sources to audit. Every cited node statement was opened in full and is copied verbatim in citations.json; none of the proof steps takes an unstated construction from another node's proof.

Step 1 uses affine-scheme qcqs, space qcqs morphism permanence, qcqs source products, and diagonal local finite type. These statements give exactly the finiteness of W_a and W_a×_{T_a}W_a and the lft hypothesis for its diagonal. No finite presentation of W_a or flatness is used. Finite type of h_a is simply quasi-compact plus its given lft condition.

Step 2 uses the fibre-product universal property and the explicit definition of properness to see that the limit diagonal is closed. The closed-immersion descent node allows arbitrary qcqs algebraic spaces and a locally finite type morphism, so step 1 supplies all its hypotheses. A later diagonal is closed, which is precisely separatedness. This corrects the tempting but invalid application of the finite-presentation separatedness node.

Step 3 verifies rebasing explicitly: the upper tail is nonempty directed and cofinal, with the cone extension described by upper bounds. The qcqs source-product statement applies with W_a,T_i,T_a. Stack finite-type calculus explicitly includes algebraic spaces and arbitrary base change of lft. Space qcqs permanence gives quasi-compactness, and separated-fp-composition explicitly includes separatedness under arbitrary base change. Associativity of fibre products is verified by compatible test sections rather than asserted as an extra comparison lemma.

Step 4 applies weak Chow only after h_b is separated finite type over the affine T_b. Its statement supplies a qc separated scheme, a qc immersion, and universal surjectivity, exactly what is used. Proper base change supplies properness of π_i. The integral-model definition of projective space identifies its base changes by associativity; the scheme immersion node supplies immersion base change. Universal surjectivity is retained after arbitrary base changes directly from its quantifier in weak Chow.

Step 5 uses proper composition and the representable-proper test equivalence: the composite C→T is a scheme map, and the identity scheme test gives scheme properness. Projective-space properness gives separation of P→T; scheme proper-over-separated then makes j proper. The cited proper-immersion node says it is closed. No algebraic-space immersion is incorrectly treated as a scheme immersion: C and P really are schemes.

Step 6 checks both scheme sources required by 01ZP. C_b is quasi-compact separated by weak Chow; separated-implies-quasi-separated applies to its absolute structure map. P_b is proper over the affine qcqs base, so scheme qcqs permanence gives qcqs. The immersion node gives local finite type of j_b. The limit closed immersion is step 5, and 01ZP requires no finite presentation despite the historical wording of its label. Thus its conclusion supplies j_c closed with c≥b.

Step 7 uses exactly the closed-immersion, proper composition and proper base-change clauses of the scheme permanence node and projective-space properness. The scheme-test equivalence transports the resulting proper scheme map to intrinsic algebraic-space properness: every scheme test is a scheme fibre product with proper projection.

Step 8 writes out 08AJ instead of inventing an image-proper lemma. The existing point-open-calculus statement supplies continuity. Weak Chow's universal-surjectivity clause already used in step 4 gives surjectivity after every B→T_c. Proper base change gives the closed map p_B. For a closed F its inverse image is closed, and surjectivity gives h_B(F)=p_B(π_B^{-1}(F)). This is a few-line elementary argument from those statements and the definition of properness. It establishes universal closedness; separated finite type was independently obtained in step 3. The step is marked elementary with all inputs cited, as permitted by the brief's 08AJ-style two-or-three-line exception, not treated as an uncited theorem.

Checked delivery-errors B1-B10, C1-C8, D1-D5 and E1-E7 against the open node statements: no new statement-only obligations, no disguised restatement, no use of proof-only data, no changed coefficients, missing flatness, fp, Noetherian or representability assumption. The off-unit fibre-product, point-map and scheme descent statements are declared generic tool uses in split_report, with their actual roles explained, and not installed as top-level tool_uses. Each proof step is under 2000 characters (maximum 742); there is no long step hiding a lemma.

Small cases: the empty space and empty affine stages are allowed; weak Chow permits an empty source scheme and the final surjection/image equality still holds. A constant directed system yields a proper stage directly, without using an injective or faithfully flat transition. Infinitely generated defining ideals of closed immersions cause no fp problem because both closed-immersion descent and properness only require local finite type. Non-Noetherian affine bases and non-flat transitions are covered verbatim by the cited statements. No source or statement dispute was found.

## Unfinished work

None in this one-level split. Existing dependency nodes retain their own statuses. Required server dry run and direct delivery follow.
