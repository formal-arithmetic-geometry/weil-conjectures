# Stage-1 report: lem-sfb-continuous-partials-frechet-criterion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-continuous-partials-frechet-criterion.json — statement, split into four steps; no exact Mathlib match for arbitrary m.
- dag/nodes/sec-six-functors-basics/lem-sfb-unit-interval-derivative-bound.json — statement, Mathlib leaf: norm_image_sub_le_of_norm_deriv_le_segment_01', Mathlib/Analysis/Calculus/MeanValue.lean:346–349.
- citations.json — one verbatim statement excerpt for the node used in step 2.
- report.md — this report. Searches are preserved in searches.jsonl by msearch.py.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for Frechet, Fréchet, continuous partial, coordinate partial, HasLineDerivAt and the mean-value declaration. No project declaration supplies this item or the new leaf. Mathlib declarations are treated as leaves, not attachments.

## Wanted literature

WANTED: Walter Rudin, Principles of Mathematical Analysis, third edition, Theorem 9.21, for lem-sfb-continuous-partials-frechet-criterion. The book is absent from literature/ and has not been read. The existing source record is retained and the proof is explicitly agent-written. Its actual cited mathematical input was read in the local Mathlib source.

## Findings and changes

The imported statement is correct with the stated hypotheses, including the continuity conclusion: continuity of f must be derived rather than assumed. No statement change was needed. An initial sandbox inventory found only brief markers, with no item, proof, report or previous search log to resume. The live item was used as the starting point, including all its previous search records.

I read the chapter record and the unit record, the latest blueprint unit section and direct-images proof (3), and the statement/proof of the immediate parent lem-sfb-cauchy-green-annulus-formula. The supporting calculus fact stays below that existing route. The inherited blueprint chain has null from.node, and blueprint_refs.py ancestor confirms None; I retained that value and the full via list, describing the exact supporting place for the new leaf instead of inventing an ancestor. No unit realization field is applicable to this supporting node.

The existing search results were re-read. New searches are the actual msearch.py calls in searches.jsonl. In particular, reading Mathlib/Analysis/Calculus/FDeriv/Partial.lean uncovered hasStrictFDerivAt_uncurry_coprod at lines 59–65. It handles two blocks; arbitrary m would need induction, so it is not a one-line specialization of this item. The proof instead uses the smaller unit-interval estimate, whose hypotheses are exactly relative derivatives on the closed interval and a bound on the half-open interval. The new leaf contains only a statement, searches and the precise Mathlib match, with no proof or proof dependencies.

## Not duplicates

No existing node shares the new leaf's source theorem or supplies its statement. I searched all dag/nodes for norm_image_sub_le, bounded derivative, mean value inequality and mean-value inequality, and searched the whole blueprint with blueprint_refs.py for mean value, mean-value, bounded derivative, norm_image_sub_le, continuous partial and coordinate partial. None supplied the needed estimate. The related existing lem-sfb-real-smooth-differentiation states algebraic derivative rules, not a bound on increments, and lem-sfb-continuous-partials-frechet-criterion is genuinely multivariable. The leaf is a general one-variable estimate, not a clause of the item. There are no shared Stacks tags and hence no tag-sharing pairs to justify.

## Review by O1

I checked B–E with the statements, source and final proof open. The item itself was compared with its entire live statement; its real, not complex, differential and its operator-norm conclusion are both proved. Rudin was not available, so I do not claim to have verified the statement against that book. The leaf was checked against MeanValue.lean:346–349 in full: the scalar field is real, the normed target may be complex, derivatives are within [0,1] at every point, and the bound is required only on [0,1). Its displayed quotient defines exactly that relative derivative. Taking E = C is permitted and requires no completeness hypothesis. The stronger C >= 0 assumption is satisfied in the application.

Step 1 uses no theorem node: finite intersections of the continuity neighbourhoods give one delta; the squared-coordinate calculation keeps every broken-line segment inside U. Real linearity and boundedness of A_x follow from its explicit finite sum, so no finite-dimensional automatic-continuity theorem is hidden here. The division by m is valid because m >= 1.

Step 2 cites only lem-sfb-unit-interval-derivative-bound. I opened its statement and copied its full statement verbatim into citations.json; this is exactly the conclusion the step uses. The derivative of q_j is obtained directly by substituting h_j times the increment into the assumed one-variable partial difference quotient, with the zero-coordinate case handled separately. It never applies the multivariable chain rule before proving differentiability. The domain preimage is open around [0,1], so arbitrary extensions outside it do not change derivatives, even at endpoints. The resulting nonnegative constant is |h_j| times epsilon/m. Thus the cited node says precisely what is required, with every hypothesis checked.

Step 3 uses only cancellation of the m increments, the triangle inequality, and |h_j| <= norm h. The resulting epsilon estimate is the definition of the Frechet derivative; the explicit bound with epsilon = 1 also proves continuity of f without assuming it in step 2. Step 4 uses the formula already established, the definition of operator norm as a supremum over the unit ball, and continuity of a finite sum of the given partials. No external operator-space identification is used. These steps are elementary arguments from the hypotheses and definitions, not concealed applications to new lemmas. Every proof step has fewer than 1000 characters.

Small cases checked: m = 1 reduces to the same one-variable remainder estimate; h = 0 telescopes to zero; h_j = 0 gives a constant q_j; constant functions and affine real-linear complex-valued functions have the exact displayed differential; empty U is vacuous; disconnected U requires no global connectedness or convexity. For the leaf, g constant with C = 0 gives equality, g(t) = at has endpoint norm |a| and satisfies the bound with C = |a|, and endpoint derivatives are only relative derivatives, so no endpoint differentiability assumption was silently added.

The checks found no statement dispute and required no corrections to other nodes. I corrected the potential circularity of assuming f continuous by giving the direct difference-quotient argument. No new definition, unrelated lemma, SGA reference or long hidden subclaim was introduced.

## Unfinished work

No mathematical step remains open in this split. The original Rudin reference remains wanted; independent maintainer review remains the delivery protocol.

The first dry run required a citation quote of at least 40 characters; I replaced the short endpoint formula by the full verbatim statement, including all hypotheses.
