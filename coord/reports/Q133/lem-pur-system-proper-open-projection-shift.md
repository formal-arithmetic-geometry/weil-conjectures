# Q133 stage-1 delivery

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-system-proper-open-projection-shift.json: statement, split; no Mathlib match for the complete system-specific assertion.
- citations.json: 18 verbatim statement excerpts covering every proof citation.
- No new nodes and no new Mathlib leaves. searches.jsonl preserves the five actual search calls; write_split.py is sandbox-only preparation, not project content.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag, semilinear/proper-open terms and shift terminology. Etale.commShift_baseChange in SixFunctors/BaseChange/DerivedComparison.lean proves a bounded-below etale base-change assertion, not all the intrinsic strict-semilinear-system, clopen, tensor and compactification clauses here. It cannot attach this item.

## WANTED

None. The shift assertion is explicitly agent-formulated rather than attributed as a theorem of the blueprint or Stacks.

## Errors and changes

The item was statement-only, with no proof. Its statement, statement dependencies, source, chapter/unit and ancestor references are retained. The imported phrase "primitive" is read as the list in the existing lem-pur-system-primitive-comparison-shift, including pullback/tensor and clopen maps; this is exactly the generator hypothesis supplied by its parent's step 2. No new hypothesis is added. The existing semilinear mate statement supplies lambda and its open-unit identity; proving lambda's shift equation through that identity avoids making an unsupported claim that finite evaluation detects derived morphism equalities.

The source file fix-prop-coherence.proof.md supplies the route through actual maps, units/counits and mates, but does not assert this shift lemma. The proof is therefore marked agent-written. Stacks more-etale.tex Tags 0F7B, 0F7C and 0F7D were read for the proper/open and pasting motivation, not cited as results for semilinear systems. No SGA is used.

## Unfinished work

None for this split. Existing cited nodes remain their own independent obligations. This delivery writes no Lean and runs no compiler.

## Not duplicates

No new nodes. Whole-DAG keyword searches and blueprint_refs.py search for shift and proper/open found the already existing primitive/clopen and CommShift tools. The whole-system assertion is not the bounded-below etale exchange result or a definition of exchange/projection. No duplicate was created.

## Review by Q133

I read the complete item, the smooth-purity chapter and the compatibility unit, and the maps-used/mates paragraph in the current main-20261015 fix-prop-coherence proof. The unit's route assembles compatibilities from their actual generators; the split follows this route. Its nearest blueprint ancestor is thm-pur-rational-and-qbar-purity. I also read the statements of every cited node, not just their proofs or titles. There are no new node sources to review.

Step 1 uses def-pur-integral-operation-shift-data for the fixed recursive, natural slot comparisons and lem-weil-pbc-commshift-nattrans-comp-whisker for composition and both whiskerings. The latter is already a Mathlib leaf. I read Mathlib/CategoryTheory/Shift/CommShift.lean around lines 370-430, including inverse, comp and whiskering instances. Its statement is phrased with [1], so the step explicitly instantiates that fixed-shift calculation with [r]; no generation-by-one inference is needed. The inverse equation is proved by multiplying by inverses. No new generic closure lemma is hidden.

Step 2 cites the primitive statement for the actual list of comparisons covered by the hypothesis, including pi_s and the open compositor, and the proper/open mate statement for the precise alpha and Gamma formulas. The former's shift squares are already hypotheses of this conditional item; they are not replaced by weaker finite-level squares. The latter has proper p,r, quasi-compact open k,i and the commuting square exactly as required here. The step explicitly composes beta, the whiskered clopen projection and the compositors, and then the proper unit/counit formula. The noncartesian clause is explicitly in the cited proper/open statement.

Step 3 takes the precise identity lambda P_i Gamma = 1 from the proper/open statement, with the open-unit identification inserted explicitly. The open unit is invertible for extension by zero, and its shift square is among the assumed adjunction squares. Thus the identified P_i Gamma is lambda inverse. The step proves compatibility of that inverse and then inverts its equation. It never assumes Gamma invertible or uses a conservative family of evaluations.

Step 4 takes from lem-sf-integral-compactification-system-realization its explicit assertion that coherent system exchange/projection maps are the composites of def-exchange-projection. The latter gives the typed order of unit, pullback comparison and counit. This matters: def-exchange-projection alone states its finite-coefficient formula, so the realization statement is cited to justify its use for systems. The fixed domain qualifier is retained; no arbitrary direct-image preservation of normalized bounded systems is inferred.

Step 5 uses those same exact formulas to write a=(epsilon tensor 1)mu and pi=S_p(a)eta. In the M slot the counit square is needed; in the N slot naturality of the signed right tensor shift in the fixed first-factor morphism epsilon is needed. Both naturalities are explicitly part of def-pur-integral-operation-shift-data. The generator mu square and the unit square are hypotheses. I wrote both slot arguments; no projection formula invertibility is used, and there is no unsigned substitution in the right slot.

Step 6 checks the two compactification composites against the exchange/projection definition and the system realization statement. Beta and gamma, including P_jP_p to P_f, are assumed shift compatible. The final assertion is a finite induction with identity base and one whiskered generator per step, not a newly assumed general pasting theorem. Refinement uses the same actual Gamma maps from the cited proper/open statement. Every cited node says what is extracted from it; citations.json contains exact substrings of all six cited statements.

I checked B-E of delivery-errors: the new-node requirements are vacuous, no statement was weakened, every non-elementary input is an existing node or an explicit hypothesis, every proof dependency is cited, and no proof of another node is used as its public statement. All six steps are shorter than 2000 characters. No off-route statement tool is introduced: the primitive and proper/open nodes have this same unit, and the general closure tool is a Mathlib leaf. I checked dependency reachability for the additional primitive/closure citations and found no path back to this item.

Small cases: r=0 makes the displayed squares identities; arbitrary positive and negative r use the same assumed comparisons. Empty opens give zero extensions/projections, and identity clopens give identity component projections; the argument never cancels pi_s. Identity proper/open squares reduce to the assumed unit/compositor equations. Zero tensor factors make both projection composites zero. Odd right-slot shifts retain the coefficient (-1)^{ri}. A noncartesian refinement with r=1 uses the same intrinsic lambda identity and requires no cartesian assumption. All shifted inputs still have common finite bounds after translating their intervals; domain closure for the operations themselves remains precisely the statement's stipulated domain hypothesis.
