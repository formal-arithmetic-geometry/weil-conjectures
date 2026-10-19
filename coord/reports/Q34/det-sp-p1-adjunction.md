# Stage-1 delivery: det-sp-p1-adjunction (Q34)

## Files written

- dag/nodes/sec-six-functors-basics/det-sp-p1-adjunction.json — statement; split into eleven proof steps using existing nodes. Mathlib does not contain this geometric diagonal/trace adjunction. No new node and no new Mathlib leaf.
- citations.json — a verbatim statement quotation for every node cited in every proof step.
- searches.jsonl — actual msearch.py records, retained without rewriting. The item records those exact tools and queries, with their results.

## Attachments

None. The project source search for the exact blueprint tag and for projective-line adjunction/trace terminology found no declaration establishing every clause of this item without sorry. General pullback/pushforward adjunctions and category-theoretic triangle identities do not establish this reverse, twisted adjunction or identify its diagonal unit.

## WANTED

None. The item, its unit, and the coherence source are available locally. The proof is marked agent-written, since the blueprint is agent-written and I supplied the formal expansions.

## Statement corrected

STATEMENT-DISPUTED: the imported phrase “and hence on the classical pro-étale categories” did not retain explicitly the finite-type standing hypotheses of the unit. This matters after det-sp-p1-trace was broadened: its current statement allows any Noetherian base, but the unbounded comparison nodes require a finite-type scheme over a finite or algebraically closed field. The untyped inference is applying that comparison to an arbitrary Noetherian scheme without such a field structure; for example Spec Z[1/ell] satisfies the trace hypotheses and has no structure morphism to a positive-characteristic standing field. This is a missing-hypothesis/type-scope issue, not a counterexample to an étale triangle identity.

The delivered statement retains the ordinary étale identities over every Noetherian base with ell invertible, and explicitly gives the classical unbounded transport only in the standing finite-type range of the unit. It retains the finite-Tor restriction in the standing separated finite-type characteristic-p range. For that restriction I use bounded comparison, so no finite/algebraically closed-field hypothesis is silently imposed on the bounded assertion. Thus the hypotheses of the source unit have not been strengthened; the implicit standing scope has been made explicit. I also expand G6 and G7 into typed formulas instead of pointing at a unit record as if it were a definition node.

The only existing direct citer is lem-per-ordinary-smooth-orientation. It uses the ordinary étale projective-line orientation over Noetherian bases. That clause remains valid in the delivered statement, so its use continues to hold. No citer was edited. No target statement was edited.

## What was wrong and what changed

The imported proof cited thm-amb-p1-adjunction as if its statement were the abstract unit/counit criterion. That node instead states a specific geometric adjunction with a normalized counit; it does not identify the diagonal unit. I removed that use and wrote the inverse Hom formulas, citing the existing natural-bijection criterion. The separately existing ordinary finite projective-line theorem is cited only for its trace/counit normalization and base-change clauses, never to infer either triangle identity for this unit.

The imported first rewriting hid projection/composition and exchange/tensor coherence, and the last step had no citations and an unjudged elementary flag. The replacement names the section specialization of projection coherence, the actual exchange/projection commuting square, mate pasting, the separate full-faithfulness and essential-surjectivity results, unbounded direct-image comparison, proper preservation, and bounded finite-Tor comparison. A unit id such as sk-prop-pe-unbounded-classical is not a node citation; the delivery uses the actual nodes realizing it.

No new node is needed: a generic kernel-contraction lemma would repeat the already existing exchange/projection and section-composition tools, while new lemmas stating either triangle identity would merely restate clauses of the item. The actual cancellation and both substitutions remain in the item's steps.

## Not duplicates

There are no new-node/existing-node pairs to distinguish. Whole-DAG and blueprint searches for projective-line adjunction, triangle identities, exchange/tensor coherence, and the cited projection-formula tags found the existing interfaces now reused. thm-amb-p1-adjunction and lem-asd-ordinary-finite-p1-adjunction do not state the specified diagonal unit and its two identities; the tower and rational triangle nodes have different coefficient categories. Accordingly blueprint.same_as is empty.

## Review by Q34

I read the current main-20261015 statement and proof of det-sp-p1-adjunction, its sk-prop-geo-p1-adjunction unit record and section/proof route (G5--G9 and the complement), the six-functors-basics chapter record, and the current statement of det-sp-p1-trace. I checked the relevant local Stacks text: Tag 0B56, sites-cohomology.tex, equation-projection-formula-map (the projection arrow is the adjunct of counit tensor identity); Tag 0E48, remark-compatible-with-diagram (its entire exchange/tensor commuting diagram); and Tag 07A4, lemma-pullback-tensor-product. I checked tag-to-label mappings rather than relying on moving section numbers. No new node has an additional source requiring review.

I opened the statements of all cited nodes. Step 1 uses projective-space properness, closed-immersion properness, properness's finite-type clause, and Noetherian permanence to check all hypotheses of the ordinary unbounded projection and proper-exchange theorems. A=Z/ell^n is finite, torsion, and commutative, and ell is invertible for the twist. This explicitly permits non-perfect and unbounded M and K.

Step 2 uses the étale diagonal-integral node, whose statement contains both integrals with alpha_a and exactly the supported Kummer normalization; it does not borrow an assertion from a node's proof. The monoidal-comparison node provides the canonical adjunction-compatible composition identifications. The trace-definition node identifies the particular trace projection and the particular counit. Step 3 substitutes i=Delta, p=p_a, V=A into the stated section-specialization identity of lem-sfb-ringed-projection-tensor-composition. Its naturality then gives the displayed 1 tensor u_a; this is a short elementary consequence of the cited formula.

Step 4 specializes the actual commuting exchange/tensor square, first to E=M,Q=L_S, then to E=L_P,Q=FM with the factors interchanged. Composition coherence and mate pasting use qp_1=qp_2 and cancel the exchange inverse. The trace base-change clause is in the ordinary finite projective-line theorem's statement. Step 5 substitutes s_1=1 from the diagonal-integral statement, without an independent cohomology argument. Step 6 uses the same square and tensor-associativity formula with M=GK, for which p_1^*M=p_2^*M by the normalized twist-pullback statement; s_2=1 then gives the second identity. The shifted Tate line is even, so the indicated interchange contributes no sign. These steps retain the source's diagonal-integral route, rather than replacing it by smooth purity or by existence of some adjunction.

Step 7 proves both inverse Hom-map equations and applies the natural-bijection criterion, whose statement gives precisely the adjunction and its recovered unit and counit. Step 8 uses the supported-Kummer statement only after checking its Cartier-pullback hypothesis on all four affine charts. In the mixed charts 1-xy is regular even over a ring with zero divisors: the top coefficient in x is multiplied by y, and multiplication by y in the polynomial coefficient ring is injective. Twist pullback, trace base change, exchange/projection coherence and mate pasting then identify the actual G6/G7 arrows over S'. The claim is about commuting natural-transformation squares, not just objects being isomorphic.

Step 9 checks the finite/algebraically closed field and finite-type hypotheses separately for S,P,W. The full-faithfulness node alone does not give essential surjectivity, so the latter is supplied by lem-sfb-finite-classical-unbounded-comparison, whose statement explicitly covers all unbounded classical complexes. Direct-image comparison is likewise the unbounded theorem and is explicitly the canonical mate. Monoidal and Cartier comparisons identify the geometric maps before transporting the inverse equations.

In steps 10--11, det-ctf-finite-proper-localizing states the proper preservation clause for arbitrary standing characteristic-p fields and finite ell-primary A. For G, the pullback bounded-constructibility node applies to the standard quotient P_n=Z/ell^n. I initially considered lem-sf-pullback-tor-amplitude, then corrected this: its global finite-field hypotheses do not justify an arbitrary-field assertion. The delivered step instead uses the general ringed-site bounded-flat-model equivalence and flat-module pullback, whose statements have no field or constructibility hypothesis. The Tate-line statement supplies local freeness and flatness. Shift [2] changes [a,b] to [a-2,b-2]. The finite-Tor comparison is stated for qcqs schemes and discrete Noetherian coefficient rings; both hold here. Finally the bounded-below direct-image comparison explicitly includes compatibility with units, counits and composition, so it transports the restricted adjunction even when unbounded classical comparison is unavailable. Fullness is in the constructible-category definition. This avoids conflating ordinary constant modules with completed coefficients.

I checked the mathematical small cases: empty S and zero complexes (all maps are the unique zero/identity maps of zero objects), n=1 and n>1 (bounded constructibility alone is not substituted for finite Tor amplitude), ell=2 (even shifts still give sign +1), a complex in one degree (the [2] Tor-interval shift has the stated sign), genuinely unbounded M,K (only the unbounded proper projection/exchange theorems are used), and nonreduced bases (the diagonal chart equations remain regular). The Spec Z[1/ell] scope test explains why étale and unbounded-classical ranges must be distinguished. Each prospective new-node idea was rejected as a duplicate, elementary consequence, or restated clause. All non-elementary steps are below 2000 characters; the longest calculation invokes explicit existing coherence statements and contains no independent hidden geometric lemma.

I checked every proof dependency by statement, wrote its verbatim statement into citations.json, and checked the union of step uses against proof_deps. I checked that the principal new citations do not reach the item in the existing DAG. All off-unit tools are declared in split_report.tool_uses with their use and purpose; the source unit's diagonal-class route is unchanged. The unit's realization record is not mine to edit because this detailed triangle node is not its key statement node. The preliminary server review_split passed before the final flat-model and bounded-comparison refinement; the required complete deliver.py dry run follows this report.

## What could not be finished

Nothing in the one-level split. The cited existing nodes remain separate DAG tasks at their recorded statuses; this delivery does not claim their Lean proofs are finished.
