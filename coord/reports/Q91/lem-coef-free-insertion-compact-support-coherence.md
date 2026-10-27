# Q91: lem-coef-free-insertion-compact-support-coherence

## Files written

- dag/nodes/sec-six-functors/lem-coef-free-insertion-compact-support-coherence.json: statement, split; no Mathlib match for the complete assertion.
- citations.json: eleven verbatim statement excerpts for the five proof steps.

No new nodes; no new Mathlib leaves. The statement and statement dependencies are unchanged. All existing metadata and inherited Mathlib searches are retained. The sandbox initially had no node, report, or search log. Searches made for this split are appended from the actual searches.jsonl entries.

## Attachments

None. Searches of lean/WeilConjectures by the exact blueprint id and by free insertion, quotient mate, and coefficient-system terminology found no declaration stating this item. The coefficient-system hits concern adic Frobenius and different coefficient transports, not this ordinary unbounded system adjunction. A general Mathlib mate theorem is an ingredient, not an attachment.

## WANTED

None for this split. The inherited brief mentions coord/dag-sync.md, which is absent in this shared checkout; the explicit current shared-repository instructions determine the read-only and delivery procedure.

## What was wrong or missing

The imported item was statement-only. The needed free-insertion comparison, evaluation-normalized right-adjoint Hom bijections, and actual transition formula already have DAG nodes. Creating replacements would duplicate their statements. The only additional calculation needed is the truncation equation and identifying the pre-existing comparison with the transpose specified by this item. Both are short consequences of an adjunction bijection, written in the proof itself.

The blueprint source gives the bounded integral assembly, not a standalone proof of this ordinary unbounded refinement. Accordingly proof_origin is agent. I read its middle Hom-adjunction calculation and its final assertion about finite units and counits. I also read Zheng, Six operations and Lefschetz–Verdier formula for Deligne–Mumford stacks, Construction 4.1 (printed p. 21), Constructions 5.14–5.15 and Lemma 5.16 (printed p. 35), and Lemma 5.22 (printed p. 36). Construction 4.1 gives the free-insertion adjunction, (5.16.2) is its compact-support comparison, and Lemma 5.22 is the evaluated exceptional adjoint. The ordinary-system refinements used as black boxes are stated explicitly in the existing DAG nodes; I do not attribute all their detailed coherence formulas verbatim to Zheng. No SGA source is used.

## Unfinished work

None in the stage-1 split. Existing dependency nodes remain their own items; this delivery does not claim to prove them or implement Lean.

## Not duplicates

No new nodes, hence no new/existing node pairs. In particular I reuse lem-pur-etale-system-brown-construction, lem-pur-etale-system-coefficient-projection and lem-pur-etale-system-evaluation-bound instead of creating versions of their free-insertion and mate clauses. Whole-blueprint searches for free insertion, free-insertion, coefficient projection and truncation, and whole-DAG searches for free-insertion/sigma statements, were checked. The item combines a specified comparison, its truncation equation, and adjoint identifications; it is not itself an exact copy of the evaluation-bound theorem, which assumes the comparison and has no truncation equation.

## Mathlib searches

The logged LeanFinder searches used two mathematical phrasings. The first returned analytic compact-support maps; the second returned condensed free adjunctions and CategoryTheory.evaluationAdjunctionRight. LeanSearch likewise returned analytic compact supports and condensed free modules. Loogle returned CategoryTheory.mateEquiv and its counit and pasting identities. The logged grep located evaluationLeftAdjoint/evaluationAdjunctionRight in Mathlib/CategoryTheory/Adjunction/Evaluation.lean, lines 38 and 54, and mateEquiv and mateEquiv_counit in Mathlib/CategoryTheory/Adjunction/Mates.lean, lines 84 and 123. I read those declarations and their contexts. The evaluation theorem is for a functor category with a fixed value category, not varying coefficient rings and their derived free insertion; the mate theorem does not assert the geometric projection/free-insertion isomorphism. None is a one-line specialization giving the complete item. All four services answered successfully; unavailable was not recorded for any of these searches.

## Review by Q91

I checked the full B–E checklist against the node and the open source text. There are no new unsplit statements to audit, and no extra definitions or clauses were introduced. I preserved the source statement, including its direction q inverse in the exceptional mate. The unit record is not edited: this item is not that unit's key statement. The chapter and the unit route are retained. The system construction/evaluation statements from sk-def-sf-operations are explicitly declared as generic tools in split_report.tool_uses: they are not replacements for a biduality step.

For Step 1 I read the entire statements of lem-pur-etale-system-brown-construction, lem-pur-etale-system-coefficient-projection and lem-pur-coefficient-evaluation-derived-left-adjoint. Brown gives an actual natural isomorphism with components inverse to q in its stated direction, so its inverse has components q as required here. The projection theorem explicitly normalizes the identity ring map; the free-insertion adjunction has identity unit after the displayed level-n identification. Its Hom bijection therefore identifies the inverse Brown comparison with the a_n defined in the item. This uses an actual system map already supplied by Brown, not a presumed lift of a family of levelwise maps. The finite-field and separated finite-type hypotheses apply; the general Brown theorem even permits nonseparated Y. O=R, t=varpi satisfies its nonzero nonunit condition. I read Zheng's corresponding construction and comparison as noted above.

For Step 2 the free-insertion statement explicitly says sigma is the identity below the truncation level on the specified representatives, and Brown's evaluation comparison is natural on maps. The source and target of both sides are L_n^Y F_n T^X K and F L_m^X K. Transposing once at n gives the identity for the left side and q followed after its inverse for the right side. Injectivity of this particular adjunction bijection proves equality of the two derived-system maps. This is a few-line elementary calculation from the cited results, not a new lemma. It avoids the false inference that jointly conservative evaluations detect equality of arbitrary maps.

For Step 3 I read all hypotheses of lem-pur-etale-system-evaluation-bound. Its Hom chain is exactly the one required after Step 1 identifies the chosen free-insertion comparison. It explicitly identifies both evaluated counit and unit. The theorem's extra amplitude assumption occurs only after these unconditional comparison assertions, so no boundedness hypothesis is imported. This matters because the item requires arbitrary unbounded inputs.

For Step 4 that same node explicitly states the inherited transition as G_n(t) b, specifies b as the transpose of T epsilon composed with q inverse, and says it is an actual transition with three-index compatibility. The mate-definition node explicitly gives the unit/counit word and its equivalent transpose characterization. Expanding that definition gives the exact three factors in the question, with T^X on the domain and T^Y on the counit. I checked these source and target categories; no claim that every mate of an invertible map is invertible is used.

For Step 5 I read det-sp-unique-right-adjoint and its blueprint source in full. It gives the unique counit-compatible natural isomorphism for either system or finite right adjoints. The mate definition gives uniqueness of the corresponding transposes. Substitution of the counit equations gives the two displayed transport equations in the proof, and these transport the transition and evaluated-unit formulas. This is a short application of uniqueness and the defining Hom bijections, so it is a step rather than a new node. No assertion about quotient right adjoints follows from only their evaluated objects.

I tested m=n: identity coefficient comparison and truncation yield the identity mate by the triangle identity. At r=n the comparison is the identity as used in Step 1; above n both free insertions are zero under the evaluation comparison. For f the identity, q and a are identities and the transition formula reduces to the original t. Zero inputs and empty X give zero maps, consistently with the adjunctions. Nonflat A_m to A_n and unbounded K,N are permitted explicitly by the cited projection and free-insertion statements; no finite-Tor or normalized-system hypothesis was smuggled into the argument. Each proof step has fewer than 2000 characters. All eleven citation quotes were checked as literal substrings of the cited statements. I wrote no Lean, invoked no compiler, and modified neither the repository nor launcher files.
