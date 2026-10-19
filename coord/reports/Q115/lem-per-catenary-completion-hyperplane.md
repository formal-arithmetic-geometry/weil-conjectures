# Q115: lem-per-catenary-completion-hyperplane

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-catenary-completion-hyperplane.json: statement, split into six proof steps; no Mathlib match for the whole assertion.
- citations.json: verbatim statement quotations for all 15 step citations.
- report.md: this report. searches.jsonl is the real msearch output log.

No new nodes and no new Mathlib leaves. The mathematical statement is unchanged; inline explanations specify domain, local, minimal prime and catenary. All imported metadata is retained. No unit record is changed: this is not its key node.

## Attachments

None. Searches in WeilConjectures/ of the supplied slopmaster2 and upstream master checkouts for the exact blueprint id and catenary/Catenary/equidimensional found no declaration stating this item. The upstream master is reference material only.

## WANTED

None. All sources used are available in literature/stacks-project/.

## Problems and repairs

The item was a statement-only child of the reviewed Ratliff split. Stacks 0AW3, lemma-not-formally-catenary, ends its d>1 paragraph by asserting that the hyperplane quotient is not formally catenary. Its compressed argument does not explicitly choose the minimal prime of A/fA or show that the selected component of V(q,f) remains a component of V(f). These inferences are what this split supplies. No false statement or missing hypothesis was found in the dispatched item. Catenarity of A is essential for the dimension of every prime quotient selected this way; universal catenarity or excellence of A is not assumed or used. No theorem that the completion is catenary is needed.

Step 2 adds the contraction of q and (0) to the avoidance list, explicitly ensuring f is nonzero and has nonzero image in B/q, including when the intersection list is empty. Step 4 uses the one-equation height bound from Step 3 to rule out a second component below P. Step 5 uses going down to prove the required minimality of the contraction, rather than claiming this for arbitrary ring maps.

The recorded Mathlib searches were actually run with msearch.py. Both semantic phrasings, Loogle and grep were read. The dimension-drop hits are genuine matches to an existing dependency, lem-weil-pbc-dimension-quotient-nonzerodivisor (Regular.lean:189), not to this item. The height-one search hits give only individual algebra tools and do not state the hyperplane/component-selection theorem. All five new logged searches are preserved, alongside the item's inherited searches.

## Not duplicates

No new nodes. Before deciding this, I searched the whole DAG by concepts and Tags 0AW3, 00DS, 00FR and 00KW, and used blueprint_refs.py for catenary, prime avoidance, principal ideal, minimal primes, principal, height and hyperplane, plus the ancestor lookup. In particular I reused the existing dimension-drop Mathlib leaf, the existing height-quotient bound, prime avoidance and finiteness nodes instead of creating specialized copies. The unrelated hyperplane result in the imported blueprint does not state this local-algebra assertion.

## Review by Q115

I read coord/delivery-errors.md B through E in full and checked this split against each issue with the source and cited statements open. I read Stacks more-algebra.tex Tag 0AW3, lemma-not-formally-catenary, including its entire d>1 paragraph and the surrounding induction, and the reviewed parent Ratliff node to verify the exact downstream clause. I read the chapter and unit records and the blueprint ancestor. This is a commutative-algebra tool below the unit's duality route, not an alternative proof of its Fourier/perverse theorem. Generic off-unit uses are declared in split_report.tool_uses for maintainer review, not asserted as already accepted.

Step 1 uses the full statements of lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-local-completion-local-ring, lem-weil-pbc-noetherian-local-finite-krull-dimension, lem-weil-pbc-noetherian-finitely-many-minimal-primes, and lem-sc-finite-minimal-primes-over-ideal. They respectively give Noetherianity of B, its exact maximal ideal mB, finite local dimensions, a finite minimal-prime list, and finite lists over each sum q+q_i. I checked algebra.tex Tags 0316 (lemma-completion-Noetherian-Noetherian), 05GI/05GG, 00KQ (proposition-dimension), and 00FR (lemma-Noetherian-irreducible-components). Quotient Noetherianity and locality are justified directly in the step. No irreducible-component topological theorem is smuggled in: everything is formulated using primes.

Step 2 uses exactly lem-weil-pbc-prime-avoidance. Its statement allows a finite list of prime ideals and an ideal not contained in any of them. I read Tag 00DS, lemma-silly. Every excluded contraction is strictly below m because its extension would otherwise contain mB, whereas its B-quotient has positive dimension. Including (0) is legal because A is a domain and m is nonzero. Thus the required hypotheses are verified rather than inferred from an unspecified avoidance principle.

Step 3 uses lem-weil-pbc-dimension-quotient-nonzerodivisor for the local domain B/q, where f is nonzero and in the maximal ideal; its Mathlib source Regular.lean:181-194 and Stacks 00KW, lemma-one-equation, give the exact equality. It uses lem-weil-pbc-prime-contains-minimal-prime for the ideal q+fB below a supplied prime; its statement includes arbitrary ideals, not merely I=0. I read Tag 00E0, lemma-Zariski-topology (4). Finite dimension guarantees a chain attaining d-1, so choosing a minimal prime below its first term gives the desired component without another existence theorem. It also uses lem-weil-pbc-noetherian-height-quotient-bound with t=1 in B/q. The prime after quotienting by f is minimal and has height zero. This is precisely the bound needed to exclude two strict inclusions, and uses no catenarity of B.

Step 4 cites the same arbitrary-ideal minimal-prime existence statement three times. All other reasoning is an explicit prime-chain comparison using Steps 1-3: if another minimal component q_i lies below P, a prime minimal over q+q_i inside P has positive quotient dimension and is on the avoidance list. It lies strictly between q and P, contradicting the already proved height bound. I marked this elementary because the substantive finiteness, existence, avoidance and height inputs were already isolated and cited; it introduces no unproved standard lemma. This is neither a restatement node nor a circular argument: Step 3 establishes the height bound independently before Step 4 uses it.

Step 5 uses lem-weil-pbc-prime-contains-minimal-prime below the contraction p, lem-weil-pbc-local-completion-faithfully-flat for the flat map A to B, and lem-sc-flat-going-down with p_0 contained in p and the prime P over p. I read their statements and algebra.tex lemma-completion-faithfully-flat (00MC) and lemma-flat-going-down. The lifted smaller prime contains f, so minimality from Step 4 forces equality. It then uses lem-weil-pbc-local-completion-quotient, whose statement specifies the canonical completion map, its surjectivity and kernel pB. I read Tag 00MA, lemma-completion-tensor (2)-(3). This supplies the actual completion identification, and prime/quotient correspondence shows r=P/pB is minimal. No claim that contraction of a minimal prime is minimal for arbitrary maps is made.

Step 6 again uses the exact height-quotient bound, now in A at p, to get height one. Every other step is written out from the catenary hypothesis: concatenate the saturated chain 0<p with a longest chain above p, and compare it with a longest chain in A. Both end at m and start at 0. I read Tag 00NI, definition-catenary, and checked that no equidimensionality or universal-catenarity assumption is needed for this domain argument. Finite dimensions from Step 1 make the maxima and saturation assertions valid.

For B through E: no new-node format or unmatched Mathlib-leaf issue occurs; every non-elementary input is a cited existing statement with a verbatim quotation in citations.json; no proof of a cited node is used as an interface; no specialized duplicate is created; and no content is moved into a new node. All six steps are below 1,000 characters, so none reaches the long-step review threshold. I checked the proof order for circularity and will use the server checks for graph and route validation. There is no SGA reference.

Small cases checked: fields and DVRs cannot satisfy 1<d<N, so are excluded explicitly; d=2 gives a positive one-dimensional selected component and keeps the key intersection prime off the maximal ideal; N=d+1 gives 0<d-1<d=N-1; an empty intersection list still allows avoidance of q and zero; repeated contractions do not affect prime avoidance; nonreduced completions cause no difficulty because no reducedness is used. The proof would fail at d=1 (positive-dimensional intersections can no longer capture the offending prime), which is exactly why the parent has a separate induction base. The least-d assumption is available but unnecessary for this hyperplane step; it is used by the parent induction and was retained unchanged.

## Unfinished work

None in this one-level split. Existing dependencies retain their own statuses. Server dry-run and delivery results follow below.

The first server dry run exited successfully: `OK (not pushed)` at fd1056147c, including preflight, graph and split checks. The report citation count was corrected to match citations.json before the final dry run.
