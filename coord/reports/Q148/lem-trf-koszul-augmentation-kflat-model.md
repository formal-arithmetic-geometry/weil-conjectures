# Worker report: lem-trf-koszul-augmentation-kflat-model

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-koszul-augmentation-kflat-model.json`: statement node, now split into four proof steps; not a Mathlib leaf.
- `citations.json`: nine verbatim statement quotations, covering every citation in the four steps.
- `report.md`: this report. The search command also maintains `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. No unit record changed: this auxiliary node is not the unit's key statement.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for Koszul regularity, augmentation, projective resolutions and scalar-extension counits. The Koszul projective and normalized projective resolutions exist, and bounded-flat K-flatness exists; none states all clauses of this item, especially the formula for the specified arbitrary derived pair. Thus no whole-item attachment is claimed.

## WANTED

None. All mathematical source material used is available in the read repository.

## Findings and changes

The imported statement is correct, and its text and statement dependencies were preserved. Its proof was empty. I supplied the degree-zero boundary computation, the check of every cohomology degree, the bounded finite free K-flat model, and the actual counit factorization. There is no hypothesis of ordinary regularity or a proper ideal: only vanishing of nonzero Koszul homology is used.

The pointwise mixed-tensor result asserts existence of one universal pair with counit invertible on K-flat complexes. It does not assert that property for an arbitrary pair. Step 3 now writes out the universal-property comparison in both directions and proves that the comparisons are inverse by uniqueness. This avoids treating an existence assertion as a universal assertion, and avoids substituting the homotopy-level scalar-extension counit theorem for a cochain-level counit without justification. The mixed-tensor node is for modules with the second-factor coefficient action required here, not sheaf coefficients or a different derived category.

No blueprint or source error was found, and no mathematical route was replaced. The long inherited blueprint ancestry connects this generic algebra calculation to the trace unit through the lci cotangent/Koszul quotient branch. This split handles precisely the already assigned augmentation-model component.

## Search record and reuse

Searched the entire DAG by Koszul regularity, augmentation, finite free resolutions, bounded-above K-flatness and scalar counits; ran `tools/blueprint_refs.py ancestor` for the item and blueprint searches for `Koszul`, `K-flat` and `augmentation`. Reused existing statements rather than creating general homological-algebra lemmas. The exterior-basis node is a Mathlib leaf. The bounded-flat module and mixed-tensor pointwise results are generic tools from the Picard framework, explicitly declared as tool uses in `split_report`; the trace unit does not provide alternative statements of these generic facts.

Ran five logged Mathlib searches with msearch.py: LeanFinder on the Koszul resolution/comparison, Loogle on `"Koszul"`, grep on `Koszul|koszulComplex|derivedTensorProduct`, LeanSearch on the Koszul augmentation counit, and a second LeanFinder phrasing about the K-flat counit. Read all hits. Mathlib's `RegularSequence.lean` explicitly lists Koszul regularity as TODO (line 21). The generic total-left-derived counit and Kan-extension API supplies universal-property machinery, but not this Koszul model. Cotangent-module exactness, differential geometry's Koszul connections and local-cohomology TODOs do not state the item. The original Q16 searches are retained and the five Q148 searches appended exactly with their logged queries, results and digests.

## Not duplicates

No new nodes were created, hence there are no new/existing same-tag pairs. In particular, `new-j3-koszul-projective-resolution` and `new-d3-koszul-normalized-projective-resolution` are existing nodes, not recreated auxiliary nodes. The augmentation computation here is a short elementary step from the Koszul differential and regularity definitions.

## Review by Q148

I read cotangent.tex Tag 08SJ, `lemma-mod-regular-sequence`, particularly its first proof paragraph identifying the Koszul regular quotient with the derived tensor calculation. For the expanded ingredients I read more-algebra.tex Tags 0623 (`definition-koszul-complex`), 062E (`definition-koszul-regular-sequence`), 064K (`lemma-derived-tor-quasi-isomorphism`), and the construction and proof of Tag 06Y6 (`lemma-derived-base-change`); I also read derived.tex Tag 06XN (`lemma-find-existence-computes`) and the finite exterior basis paragraph of algebra.tex Tag 00DM. I checked the tag/label table. There are no new nodes whose sources need separate review.

For step 1, I opened the full statements of `def-weil-pbc-koszul-complex`, `lem-weil-pbc-exterior-power-free-basis`, `lem-pc-module-bounded-flat-kflat` and `def-pc-module-kflat-complex`. The exterior-basis statement gives both finite bases and vanishing above rank, not merely freeness of an unspecified exterior algebra. The bounded-flat statement is for ordinary modules and has only bounded-above and termwise flatness hypotheses, both verified in the step. Finite free flatness is justified coordinatewise, including zero terms, rather than cited from a definition of flatness. This proves K-flatness for the total tensor and ordinary-module convention actually in the statement.

For step 2, the cited Koszul definition expressly gives d_1(e_i)=g_i, so its image is exactly I; it is not a definition being used as an unstated acyclicity theorem. The regularity definition supplies vanishing at every nonzero chain degree. The derived-category definition says what a quasi-isomorphism means. I verified the negative-chain to negative-cochain indexing and the actual induced quotient map on degree-zero homology. No appeal to a projective resolution with an unspecified augmentation occurs.

For step 3, I opened `lem-pc-mixed-tensor-pointwise-left-derived` and checked its statement has a cochain universal counit, acts through the coefficient complex, and is invertible on ordinary-module K-flat inputs. Substitution is R=A, coefficient ring S, N=S[0]. The item's arbitrary universal pair is compared to the supplied pair by explicit maps t and u; uniqueness proves their composites are identities. No boundedness of the second complex, scalar flatness, or unproved compatibility of unrelated chosen isomorphisms is used.

For step 4, the derived-category statement explicitly says localization inverts quasi-isomorphisms. I checked that v has source LQ_A(K) and target LQ_A((A/I)[0]), so eta_K composed with v inverse has exactly the required direction. Naturality gives eta_B composed with v equals Q_S F(epsilon_g) composed with eta_K; right composition with v inverse proves the displayed conclusion for the specified counit. This is the argument, rather than an unnamed claim that the comparisons are compatible.

I checked B--E of delivery-errors.md against the finished files: no statement-only node has a hidden proof, no new duplicate or restatement node was introduced, all non-elementary inputs are cited with their actual hypotheses, and all nine quotations are verbatim parts of the cited statements. Elementary steps 2 and 4 spell out their arguments. Each proof step is under 1200 characters, so there are no non-elementary steps over 2000 characters hiding an auxiliary lemma.

Small cases: r=0 gives A/(0) and the degree-zero augmentation is an isomorphism; r=1 and g=1 gives a contractible complex with quotient zero; A=0 or S=0 is allowed throughout. For a genuinely non-flat test, A=Z, g=2 and S=Z/2 gives a zero differential after scalar extension and a nonzero degree -1 term; the conclusion correctly identifies the derived object with that two-term complex and does not assert that the counit to the ordinary quotient tensor is an isomorphism. For a nonregular test, g=0 over a nonzero ring has nonzero H_1 and is excluded by the stated Koszul-regularity hypothesis. These checks require no added properness or nontriviality assumptions.

## Unfinished work

None at stage 1. No Lean file was written or compiled and no repository file was changed. The independent maintainer review and later formalization remain the project's subsequent work.

## Landing-return repair by Q148 (2026-10-23)

The return concerns head `ebd7d6bc5ea5645f1b766e6ed74d69f5f06666a6`: the reader approved the split, but the landing found a completion only in the side DAG. I ran the retained sandbox's required dry run first; it exited successfully at `9f937a8bd48`. I then compared the returned head with server `sheaf-dag` at `6a3ffc7971aefab547f664ba50a91ec78c914d6d`, using read-only server history. The current item is unsplit, with empty proof and proof dependencies; its statement and statement dependencies agree with the retained split. There is no released repair-note file. The delivery tool assembles this repaired delivery on current live `origin/sheaf-dag`, preserving its maintainer-owned fields.

All nine cited node files are unchanged, byte-for-byte as parsed JSON, between returned head and current main: `def-weil-pbc-koszul-regular-sequence`, `def-weil-pbc-koszul-complex`, `def-pc-module-kflat-complex`, `def-weil-abstract-derived-category`, `def-pc-mixed-total-tensor`, `lem-pc-derived-tensor-second-factor-functor`, `lem-weil-pbc-exterior-power-free-basis`, `lem-pc-module-bounded-flat-kflat`, and `lem-pc-mixed-tensor-pointwise-left-derived`. I reopened every current statement, including the two used only by the item's statement. None requires replacing a dependency or changing a hypothesis.

This is a repaired split rather than an unchanged re-push. Step 3 now gives the universal counit's type in ordinary composition notation, L_0 composed with Q_A to Q_S composed with F; the dependency writes functor composition in diagrammatic order. The step explicitly substitutes the two comparison equations to obtain both composite counit identities before uniqueness yields the inverse transformations. This verifies that the counit is the one of the arbitrary specified universal pair. Step 4 now also explicitly uses preservation of isomorphisms by L. All four original arguments, source places, blueprint provenance, and logged Mathlib searches are retained. I read the saved search results and did not rerun unchanged queries.

For this renewed review I reread cotangent.tex Tag 08SJ, more-algebra.tex Tags 0623, 062E, 064K and the construction and proof of 06Y6, derived.tex Tag 06XN, and the finite exterior basis paragraph of algebra.tex 00DM. Step 1 uses finite rank and bounded-above flatness exactly as its cited statements allow; finite free flatness is the written coordinate argument. Step 2 uses only the displayed differential and the definition of Koszul regularity, not regularity in the stronger nonzerodivisor sense. Step 3 uses the mixed-tensor existence assertion, then the written universal-property argument for the specified pair. Step 4 has the correctly directed inverse and the actual naturality equation. No hypothesis of flat coefficients, a proper ideal, or nonzero rings has entered. The previous empty-sequence, unit-generator, zero-ring and Z/2 non-flat scalar-extension checks remain valid.

I checked delivery-errors B--E again. There are no new nodes, duplicate comparisons, hidden statement-only proofs or clause-restatement auxiliaries. Every non-elementary input is a cited statement, and the nine retained quotations are verbatim in the current statements. No step exceeds 2000 characters. The two Picard-framework tools remain requests for the maintainer's route approval, as explained above; no maintainer-owned top-level tool-use approval was added. The existing scalar-extension counit Lean theorem is homotopy-level and contains no whole Koszul augmentation-model assertion; the two existing Koszul projective-resolution theorems do not state the arbitrary-pair counit identity either. The exact item blueprint-tag search in WeilConjectures returns no declaration, so no attachment replaces this split. No Lean, compiler or build operation was run.
