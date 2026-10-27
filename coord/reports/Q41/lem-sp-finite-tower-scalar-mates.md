## Worker report

Files written:
- `dag/nodes/sec-smooth-purity/lem-sp-finite-tower-scalar-mates.json`: item, now split into five steps; no exact Mathlib match for the finite recursion.
- `citations.json`: verbatim statement excerpts for every node used by each proof step.
- `report.md`: this report and direct-delivery review.

New nodes: 0. New Mathlib leaves: 0. The proof reuses four existing Mathlib nodes: `def-weil-pbc-composite-adjunction`, `def-weil-pbc-adjunction-mate`, `lem-weil-pbc-mate-pasting`, and `lem-amb-mate-unit-counit`.

Attachments: none. I searched `lean/WeilConjectures/` for the exact blueprint tag, finite-tower/ordered-adjunction phrases and scalar/mate notions. The coefficient-square declarations found there do not state the finite recursion with every clause and the actual ordered counits. No project declaration was claimed as a finished proof.

WANTED: none.

The imported item had a statement and searches but no proof. I supplied the finite induction, including the complete substitution into binary mate pasting and the final cancellation. Its statement, statement dependencies, source, provenance and existing search records are retained. No statement dispute or route departure was found. In the zero-length sentence, the identity functors are the recursively defined composite left and right functors; the scalar functor T_0 is still arbitrary. Step 2 explicitly checks this more general base case.

I read the current main-20261015 exceptional-comparison statement and proof, the chapter and coefficient-comparison unit records, and the worker contract. The relevant source sentence is Charts, “the iterated projective-line integration”, followed by the displayed scalar counit equality and uniqueness of transposes. The categorical iteration is written by this agent, not attributed to an unavailable literature proof. For its formulas I read Stacks tag 0DV0, `lemma-compose-counits`, categories.tex lines 3575–3619, and Mathlib/CategoryTheory/Adjunction/Mates.lean, especially mateEquiv at lines 95–119, mateEquiv_counit at 123–125, and mateEquiv_hcomp at 209–224; I also read Adjunction/Basic.lean's comp_counit_app formula at 580. No SGA source or purity route is used.

DAG searches used statement-only inspection across all node directories, together with searches for mateEquiv_hcomp, mateEquiv_counit and Adjunction.comp matches. Whole-blueprint searches were `finite ordered tower`, `composite adjunction`, and `mate pasting`; the ancestor command confirms det-sp-reduction-exceptional. There is no blueprint node stating this finite ordered recursion in another form, so same_as remains empty. The existing generic mate-pasting and mate-counit nodes are used instead of manufacturing specialized duplicates. The adjacent geometric lem-sf-mate has six-functor hypotheses and does not replace the arbitrary-category finite-tower statement.

I ran all five Mathlib searches recorded in this sandbox's searches.jsonl, using the required msearch command: two semantic phrasings, the Loogle mateEquiv/Adjunction.comp pattern, source grep in CategoryTheory/Adjunction, and LeanSearch. All services answered. The results give binary pasting and composite counits, not the finite recursive statement; iterated_mateEquiv_conjugateEquiv iterates passage across four adjunctions in one square, not a length-d chain. The inherited searches remain intact, and the five actual new searches were appended with their returned log records. Nothing is recorded as unavailable or absent merely because of a failed service.

Unfinished mathematics: none. No Lean was written and no compiler, Lake or build command was run. All edits are confined to the sandbox. The direct-delivery dry run and push are run after this review.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to distinguish. All four categorical facts already have suitable Mathlib nodes, and are cited directly.

## Review by Q41

I reviewed the five steps against the four cited node statements and the source formulas, with attention to the two most likely direction errors: inverses on the left squares and the order of the actual composite counit.

Step 1 uses the statement of def-weil-pbc-composite-adjunction, which gives both the composite adjunction and its unit/counit, as well as the identity adjunction. Substituting F=L_{r,R}, G=W_{r,R}, H=F_{r,R}, I=G_{r,R} gives exactly the recursion in the item. Thus it proves compatibility with the actual chosen adjunctions, not merely with isomorphic functors. Stacks 0DV0 proves precisely this ordered counit formula. No property of schemes, coefficients or geometric functor identifications enters it.

Step 2 uses the identity-adjunction clause of that same definition and the explicit three-arrow mate formula of def-weil-pbc-adjunction-mate. That formula works for arbitrary G and H, so setting G=H=T_0 is legal. Each arrow is then an identity and the mate is the identity on T_0. I deliberately did not use clause (4) of mate-pasting here: its stated G,H are identity functors, a stronger restriction than the base case has. This is a concrete C4 check. The step is elementary substitution into the two definitions and proves d=0 even when T_0 is a nonidentity functor.

Step 3 is elementary and needs no extra lemma/node: applying a functor to the two inverse equations proves preservation of the chosen inverses; whiskering evaluates those equations at objects. The reversed product displayed there is checked by multiplication in both orders. The induction hypothesis supplies the inverse of B_r, and the assumptions supply the inverse of b_r and a_r. This establishes natural isomorphisms without the false general assertion that the mate of an invertible square must be invertible.

Step 4 uses exactly clause (2) of the statement of lem-weil-pbc-mate-pasting. I checked all six functor endpoints: its middle categories are C_{r,A}, C_{r,B}, its outer source categories are C_{r+1,A}, C_{r+1,B}, and its outer targets are C_{0,A}, C_{0,B}. Alpha=b_r^{-1} and beta=B_r^{-1} have the required directions. Their mates are a_r by the item's hypothesis and A_r by induction. The clause's pasted square equals the inverse formula of step 3, and its right square is W_{r,B}(A_r) composed after a_r G_{r,A}, precisely A_{r+1}. The clause specifies the same composite units/counits as step 1. It is a generic Mathlib leaf, so using it across units is allowed without replacing the unit's geometric route.

Step 5 uses the full displayed identity in the statement of lem-amb-mate-unit-counit. All its category/functor substitutions are written in the step; its object d is the item's object K of C_{0,A}. Its alpha is B_d^{-1}, never B_d. Its identity therefore has B_d^{-1}(G_{d,A}K) on the right. Precomposition with B_d(G_{d,A}K) cancels exactly this pair. No conservativity, invertibility of a mate in general, geometric compactification comparison or twisted-pullback comparison is assumed.

For the small cases I checked d=0 with arbitrary T_0 and d=1: the recursive B_1 and A_1 reduce to b_0 and a_0, and E_1=e_0, so the final formula is the one-step mate counit equation precomposed with b_0. At d=2 the left inverse square is (b_0^{-1} L_{1,A}) composed after L_{0,B}(b_1^{-1}), and its mate is W_{1,B}(a_0) composed after a_1 W_{0,A}; these agree with both recursions. The category may be empty; all component assertions are then vacuous, while the natural-transformation formulas still type-check. No new statement needs additional hypotheses. Every non-elementary step cites the node that states its input; no proof of a cited node is used as an unstated interface.

I checked B–E of delivery-errors: no unsplit children, duplicate children, hollow definitions, source tags used as meanings, circular dependencies or restated clauses were introduced. The induction has its claim, base, explicit successor and conclusion. All step texts are under 2000 characters. There was no previous delivery or return to repair; the corrections made during this work were choosing the unrestricted identity-adjunction base calculation and making the inverse/pasting substitutions explicit. citations.json contains a verbatim excerpt for each of the five step/node pairs. The report is my self-review for the authorized direct-delivery workflow, not a claim of independent second-worker review.
