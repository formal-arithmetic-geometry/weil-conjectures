# Q125: lem-pur-bounded-site-exchange-transposes

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-bounded-site-exchange-transposes.json: statement, split; unchanged statement, seven proof steps, no Mathlib match.
- citations.json: one exact statement quotation per step/node citation.
- report.md: this report. searches.jsonl is the unmodified search-command log; write_split.py is sandbox-only preparation material.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched lean/WeilConjectures by the blueprint id and by exchange/transpose and bounded site/origin terminology. The exceptional forward-exchange definition and isomorphy theorem in SixFunctors/Etale/Derived/Adjunctions.lean:326--357 concern a different, etale-only mate. They do not state comparison of etale and pro-etale exceptional arrows with this bounded Hom normalization. Therefore they are not attachments.

## WANTED

None. The formal categorical source and the blueprint intent are available locally.

## Findings and changes

The imported node had no proof. Its statement is retained verbatim. I did not replace arbitrary v by an open, separated, proper or smooth morphism, and did not assume that the schemes are separated over k. I added an actual counit calculation instead of appealing to unspecified transport.

The existing lem-pur-exceptional-mate-site-comparison is closely related, but requires absolutely separated schemes and explicitly supplied dimension bounds. I did not apply that restricted lemma to the present nonseparated setting. Instead lem-pur-co-smooth-exchange-transport states the arbitrary-base-change forward comparison without absolute separatedness, and lem-pur-bounded-site-adjunction-transpose supplies the bounded transposes without that assumption. The finite-dimensional compactification hypotheses of the latter are supplied by the already reviewed lem-pur-finite-setting-comparison-hypotheses. No new assertion about finite-dimensional schemes was introduced.

The proof uses the existing Mathlib leaf lem-weil-pbc-mate-pasting for its precise composition and changing-adjunction laws. The item is not itself a Mathlib leaf: Mathlib's categorical mates calculus does not supply the named geometric compactification maps or the specified bounded etale-origin Hom bijection. Five new searches were run with msearch.py, including two semantic phrasings, Loogle, LeanSearch and Mathlib grep. I read the returned hits and the relevant Mates.lean declarations. The inherited searches remain unchanged; current searches and results were added separately from the actual log.

## Not duplicates

No new node was created. I searched the whole DAG and the blueprint for exchange, transpose and site comparison and read the relevant candidate statements. In particular, the existing arbitrary-base-change exchange and bounded-transpose comparison are reused rather than recreated. The open restriction clause of lem-pur-compact-support-site-coherence is used only for further open restriction; its open hypothesis is not used to justify arbitrary v.

## Review by Q125

I read coord/delivery-errors.md sections B--E in full (including the retired-run copy), the stage-1 brief and contract, the three blueprint levels in SETUP.md, GOAL.md, the chapter and unit records, the current unit text, and the current blueprint proofs of lem-pur-co-smooth-etale-locality (Steps 1 and 4) and thm-pur-composition-coherence (Step 1 final paragraph and Step 2). The current proof is an agent-written categorical expansion of their base-change/counit compatibility intent. It does not invoke smooth purity, change the DNC route, or use any SGA source.

For the formal argument I read Stacks categories.tex Tag 0B65, lemma-transformation-between-functors-and-adjoints: the counit square and its proof characterize the conjugate by the actual adjunction Hom map. For geometric coherence I also read more-etale.tex Tag 0F7F, lemma-shriek-proper-and-open-base-change, including its properness and locally quasi-finite hypotheses and the beginning of its resolution proof; and sites-cohomology.tex Remarks 0E46 and 0E47 on both directions of pasting. These latter remarks omit verification, so the proof cites the existing mate-pasting node, not the omitted verification as an argument. I read Mathlib/CategoryTheory/Adjunction/Mates.lean:170,209,486,505 for those formal laws. No claim that the Stacks tags alone prove pro-etale comparison is made.

Step 1 uses precisely the statement of lem-pur-finite-setting-comparison-hypotheses for finite A and dimension bounds, lem-pur-bounded-site-adjunction-transpose for its domain and normalization, lem-weil-pbc-comparison-pullback for endpoint identifications, lem-pur-co-smooth-exchange-transport for equation (1) of the actual geometric maps, and thm-cbc-finite-torsion for etale exchange invertibility. I checked each statement, especially that exchange-transport allows arbitrary v and nonseparated schemes. Equation (2) follows by multiplying (1) by its invertible factors. It is not a new lemma.

Step 2 quotes the counit identity actually present in lem-pur-bounded-site-adjunction-transpose, rather than inferring a choice of adjunction from existence of a right adjoint. It introduces J and H explicitly and checks their boundedness using the assumptions already in the item. Step 3 uses naturality of the exchange stated in exchange-transport, that same counit identity, and naturality of the pullback comparison. I checked the direction of every inverse. The first two equalities in the displayed calculation are respectively naturality in a and equation (2); the third is equation (3). I spelled out the two suppressed kappa factors and checked the source C F' J and target C H, so these are equations of the same arrows.

Step 4 applies the concluding transpose assertion of lem-pur-bounded-site-adjunction-transpose to exactly the pair in equation (4). Its naturality in J, also stated there, supplies the precomposition by w* a. Its source has bounded etale witness J, and w* a changes it by an isomorphism. This uses no all-unbounded pro-etale adjunction and does not cite the more restrictive exceptional-mate-site-comparison node.

Step 5 reads condition (3) of def-pur-co-smoothness, which explicitly defines the dualizing base-change arrow using the inverse exchange and the counit. The constant coefficient identification is just composition of inverse-image functors from the point; it is a short definitional calculation. This elementary step does not claim invertibility of exceptional base change. The definition's constructible clause is used to identify the named arrow wherever that clause is in force; the bounded comparison itself remains on the larger explicitly stated bounded-origin domain.

Step 6 reads the full mate formula in def-weil-pbc-adjunction-mate, not just a reference to a definition of an abstract adjunction. I checked that the changing-adjunction laws used are clause 3 of lem-weil-pbc-mate-pasting. For exceptional adjunctions the bounded Hom normalization compares counits and the units (transpose of identities); for ordinary inverse-image/direct-image adjunctions the cited canonical-mate lemma actually states the counit equation. The latter assumes qcqs morphisms; these conditions hold here for maps between finite-type k-schemes, which are Noetherian (as supplied in Step 1), and in particular for the proper compactification maps. This is a generic tool use declared in split_report, not a replacement route.

Step 7 uses the actual statement of thm-cbc-finite-torsion for both pasting laws, identities and refinement. I checked clause 1 and clause 2 of the mate-pasting statement separately for the two directions of pasting, clause 3 for change of adjunction/refinement, and clause 4 for identities. The composition, refinement and open-restriction identities for B are actually stated in lem-pur-compact-support-site-coherence. Pullback-composition coherence is actually stated in lem-weil-pbc-comparison-pullback. Inversion reverses the factor order, so the exceptional inverse-exchange mates paste in the claimed direction. All composite-adjunction applications retain the requirement of bounded etale intermediate objects; there is no implicit extension to unbounded pro-etale inputs.

Small cases checked: v=id makes (1)--(4) the counit normalization and yields identity exceptional comparison. When j=id the forward comparison is the proper comparison; when r=id it is the open-extension comparison. Empty sources are permitted with dimension bound zero by the finite-setting lemma, and their arrows are unique. K=0 gives zero arrows throughout. K=A gives exactly the constant coefficient map. No step infers exceptional-mate invertibility from exchange invertibility (that inference is false for general mates). Nonseparated finite-type schemes cause no new hypothesis: the two central cited lemmas expressly permit them. A base change with no smoothness or properness is allowed by exchange-transport and finite-torsion. I found no false imported statement requiring a correction.

For B--E: no new statement-only nodes or duplicated clauses; all notions in the unchanged statement retain their statement dependencies; the proof dependency list equals the union of uses; every citation has an exact statement quote in citations.json; no use is of a cited node's proof; no new search was invented; no proof step exceeds 2000 characters. I checked that no new hidden comparison is asserted in the calculation: equations (1) and (3) are cited statements, and the intervening algebra is written out. Existing generic tool uses are declared for review. No Lean was written, no compiler or Lake command run, and no repository or launcher file was changed.

## Unfinished work

No mathematical subclaim remains open in this one-level split. Dependencies retain their existing statuses. The first resumed server dry run rejected the phrase “the item's” in Step 2 as a self-containment fault (B2). I replaced it with an explicit reference to the bounded-below hypotheses stated in this node; the mathematics and statement are unchanged. Server preflight and direct delivery follow this repair.
