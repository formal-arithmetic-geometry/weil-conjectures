# Stage-1 report: lem-coef-contractible-split-inclusion-saturation

## Files written

- dag/nodes/sec-six-functors/lem-coef-contractible-split-inclusion-saturation.json — existing statement node, now split in eleven explicit steps; statement unchanged. No new nodes and no new Mathlib leaves.
- citations.json — the exact statement quotations for the definition cited in steps 1 and 3.
- searches.jsonl — search command's own log, retained verbatim.
- report.md — this report.

## Attachments

None. Searched /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact id, contractibility, split monomorphisms, and homotopy equivalences. There is no project declaration giving this item's closure and tensor assertions together. The homotopy-category/internal-Hom files and the weakly contractible ring files have different statements. The read-only upstream-master search by exact id also found nothing. No Lean was written or compiled.

## WANTED

None needed for the proof. The inherited source field mentions Hovey, Model Categories, Sections 2.3 and 4.2 as motivation and explicitly says it is not archived. I do not use Hovey's results: this delivery gives the chain-level proof directly, with proof_origin.by = agent.

## Findings and changes

The item was statement-only, created for the tensor-cell input in step 10 of lem-coef-enriched-projective-diagram-model. It is true as written: crucially it assumes a retraction which is a CHAIN map, not just degreewise splittings. I retained the statement, statement dependencies, creation metadata, unit, chapter, blueprint ancestry, and all six imported searches. The supplied unit sk-prop-sf-biduality-general has no proof steps; its realized statement is not this auxiliary node. I therefore did not edit its record. The inherited ancestor is the finite mapping-complex adjunction in paragraph 2 of prop-coef-integral-exceptional-adjoint; that paragraph explains the application but contains no proof of the chain-complex assertion. The explicit argument is agent-written and is identified as such.

The initial sandbox contained only dispatch markers. I copied the current item, then wrote the split at its required dag/nodes/sec-six-functors relative path. There was no prior split, report, or delivery process to resume.

The proof normalizes each arrow using its actual quotient: s([y]) = y - ir(y). This avoids any assumption that an arbitrary chosen module splitting commutes with the differential. The arrow-retract step induces maps on the actual quotients and transfers a contraction. The ordinal steps construct compatible isomorphisms with X_0 plus the direct sum of all earlier successor quotients; the limit case verifies the universal property, rather than claiming that arbitrary colimits preserve contractibility. The tensor step writes the contraction with the sign (-1)^a and cancels both terms containing dk. No exactness theorem for tensor and no flatness assumption is used.

All proof steps are direct algebra or universal-property checks, and hence are marked elementary. The three ordinal steps carry the actual induction for the item's transfinite-composition clause; they do not outsource that clause to a new node or hide an independent general filtered-colimit theorem. Every step is below 900 characters, so none triggers the 2000-character long-step review.

## Mathlib searches

Read and retained the six inherited search records; their hits are included in the item. Ran additional searches through msearch.py in this sandbox, recorded exactly in searches.jsonl and appended to mathlib_searches. Two semantic phrasings were tried with LeanFinder, as well as LeanSearch, grep, and Loogle. The initial Loogle queries reported unknown identifiers (recorded as unusable results, not as evidence of absence); the corrected CategoryTheory.SplitMono.comp query returns finite composition and its retraction formula only.

Read Mathlib/Algebra/Homology/HomotopyCategory/DegreewiseSplit.lean (the triangle associated to a degreewise split exact sequence) and CategoryTheory/SmallObject/TransfiniteCompositionLifting.lean (transfinite stability for an already specified left lifting class). Neither states this item. The semantic hits for CochainComplex.cm5b and isSplitMono_from_singleFunctor_obj_of_injective require boundedness/injectivity and have different conclusions. The quasi-isomorphism retract instance covers only one consequence, not the split retraction and contractible quotient. There is no exact or one-line generalized match for the whole statement.

## Not duplicates

No new nodes. Whole-DAG concept searches and blueprint_refs.py searches for contractible split inclusion saturation found no equivalent blueprint node. The existing enriched-projective-diagram-model node USES the present item, and the projective-cochain-monoidal-model node concerns dg-projectivity and a different class of cofibrations. Neither is an alternative proof dependency; citing the former would be circular. The present delivery cites neither. same_as remains [].

## Review by Q151

I read the current item, the chapter record, the assigned unit record, the main-20261015 proof of prop-coef-integral-exceptional-adjoint, and the actual step 10 statement/use in lem-coef-enriched-projective-diagram-model. I read the complete statement of def-weil-abstract-derived-category, the only node cited by the proof. It defines cochain-map commutation, cohomology as kernel modulo image, and quasi-isomorphism as an isomorphism on each cohomology; it does not assert any saturation result, and the proof takes none from it. citations.json contains the precise verbatim pieces actually used.

Step 1 uses that definition's cochain-map convention and proves its splitting by writing both inverse formulas. I checked the quotient section is independent of the representative and commutes with d because r and i are chain maps. Step 2 uses no external statement: d(shq)+(shq)d = sq = 1-ir supplies the homotopy, and the zero quotient handles isomorphisms. Step 3 uses exactly the cited cohomology definition; for a cocycle y the difference y-ir(y) is dH(y), so i and r induce inverse maps. These steps establish the homotopy and quasi-isomorphism clauses without a missing homotopy-invariance lemma.

Step 4 uses the splitting of step 1 and gives the inverse coproduct decomposition coordinatewise; contraction preserves finite support. Step 5 exhibits the pushout maps and their unique extension for every compatible pair a,b, which proves the universal property and keeps precisely the old quotient E. Step 6 checks the four square/retract equations: a r_j v retracts i, the two square equations make the quotient maps well-defined, and their composite is the identity. Thus the transferred contraction is valid even if a square fails to preserve a complement. These steps cite no node because all their maps and identities are written out, with no imported theorem being assumed.

Steps 7–9 use exactly the hypotheses of the item's ordinal chain: a retraction and contracting homotopy at every successor, and the colimit universal property at every nonzero limit. I checked the induction starts at X_0, the successor inverse has the stated type, and at a limit each E_alpha occurs at a stage alpha+1 below the limit. Compatibility makes the summand restriction independent of the chosen stage. Finite-sum extension gives the colimit map, and the inverse maps are compatible too; uniqueness gives both inverse identities. Thus X_0 maps to its own summand at the terminal stage. The proof needs no exactness or preservation result for arbitrary filtered colimits.

Steps 10–11 use the explicit total tensor convention already IN the item. Bilinearity gives the two inverse direct-sum maps, and their formulas commute with both summands of the differential. For the contraction, the coefficient of dk tensor h(e) is (-1)^a + (-1)^(a+1) = 0; the remaining coefficient is 1 and gives k tensor (dh+hd)e. I checked finite support in the possibly unbounded direct-sum totalization. No boundedness, flatness, projectivity, or termwise injectivity hypothesis has entered.

I checked delivery-errors B–E against the files: there are no new nodes to carry hidden proofs or missing hypotheses; the statement is self-contained with its notions either inline or in its existing definition dependency; the JSON is written with indent=1 and ordinary TeX escaping; there is no relabelled clause, new statement-only substitute, circular citation, off-unit theorem, SGA source, or changed target. Each proof citation is justified by its statement rather than its proof. The only issue corrected during preparation was the attempted Loogle name: the failed queries remain honestly logged, and the final qualified SplitMono.comp query was read. No statement correction or STATEMENT-DISPUTED is needed.

Small cases: for the zero ring all complexes/maps reduce to zero; for an isomorphism the quotient is zero; for an empty coproduct the arrow is 0 to 0; for ordinal length 0 the composite is the identity; at the first infinite limit every finite collection of summands occurs earlier. Over Z, tensoring a contractible identity disk by Z/2 still contracts by the signed formula, so the argument does not quietly require a flat K. A retract of an identity arrow gives zero quotient by the explicit quotient retract; characteristic 2 also satisfies the sign cancellation. All clauses survive these checks.

## Unfinished work

None mathematically. The required remote dry run and direct delivery are the remaining packaging checks; their outcomes will be recorded below.

## Resumed review and validation

The resumed session retained the existing eleven-step split, report, citations and search log. Its required initial dry run exited successfully: `OK (not pushed)` at `9e02a15b80`, with server preflight passed. Comparison with the current read-only repository shows that the item's statement, statement dependencies, source and ancestry remain unchanged; its repository status is still unsplit. I reopened the chapter, unit, blueprint paragraph, parent step 10 and the complete cited definition, and repeated the project-source attachment search. The definition quotes for steps 1 and 3 are both verbatim. The current parent uses precisely the closure and tensor assertions proved here. I rechecked the successor inverse, the finite-support limit universal property and both signed tensor terms; no mathematical repair was needed. Every step is at most 868 characters, so there is no long step to extract. The recorded Mathlib search results were retained and their DegreewiseSplit and TransfiniteCompositionLifting candidates were read again; neither states the item. Only validation and direct delivery remained from the interrupted attempt.
