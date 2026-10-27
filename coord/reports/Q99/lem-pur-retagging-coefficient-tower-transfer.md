# Stage-1 delivery: lem-pur-retagging-coefficient-tower-transfer

## Files written

- dag/nodes/sec-six-functors/lem-pur-retagging-coefficient-tower-transfer.json: statement, split into five proof steps; not a Mathlib leaf.
- citations.json: fourteen verbatim statement excerpts, one for every cited node in every proof step.
- searches.jsonl: actual Mathlib search-command log; retained as generated.

New nodes: 0. New Mathlib leaves: 0. No Lean was written or compiled. The repository and launcher were only read; the delivery commands perform their own authorized temporary-worktree operations.

## Attachments

None. Searching lean/WeilConjectures for the exact blueprint tag, retagging, coefficient-tower terminology and purity/orientation declarations found no finished declaration stating this comparison. The existing Orientation.nonempty gives an orientation from a purity existence result; it states neither this normalized retagging equality nor the strict-tower equality, so it is not an attachment.

## Wanted literature

None. All sources used for this split are present.

## Errors and changes

The imported item had no proof. Its statement and statement dependencies are preserved. I filled its proof, proof dependencies, agent proof origin, split report and Mathlib searches. Its blueprint ancestor/place and empty same_as remain appropriate after searching the whole imported blueprint for retagging, towers, coefficients and extension of coefficients. There is no statement dispute and no change of the unit or chapter route.

The source's transport sentence alone does not justify equality of arbitrary derived tower morphisms from equality of their levels. Step 4 supplies the missing argument for these specific orientations: conjugate by one orientation, remove the common shift and use the degree-zero fully faithful embedding before checking components of an actual strict tower morphism. This also avoids inventing a second node restating the tower clause.

The source blueprint's old wording for det-sp-tower-gamma clause (2) has an orientation-direction problem, already corrected in the live node. This delivery uses only its unambiguous clause (1), whose direction is from the shifted Tate line to the dualizing object; finite Pi has the inverse direction.

## Unfinished work

None in the one-level split. The existing cited nodes retain their own proof obligations. No new unsplit obligation is introduced.

## Not duplicates

No new nodes were created. In particular the finite-ring formula is already det-sp-finite-general-ring, coefficient transpose uniqueness is already det-sp-reduction-exceptional, and degree-zero full faithfulness is already lem-weil-pbc-derived-single-fully-faithful. A separate tower-detection lemma would merely package a few lines from these existing statements and the strict-tower definition, so it stays a proof step.

## Review by Q99

I read the worker contract, delivery-errors B--E in both copies, the three blueprint levels in SETUP, GOAL, and the six-functors chapter/unit records. The proof stays on the earlier smooth-purity coefficient/tower route used by the six-operations package. I read the ancestor's main-20261015 proof, especially Step 1 (purity square) and Step 5 (coefficient transports). The auxiliary statement is not literally proved in that text, so the expanded proof is honestly marked agent-written. No SGA source or trace route is used.

For Step 1 I read both the live statements and the main-20261015 source statements det-sp-reduction-direct-image and det-sp-reduction-exceptional. The live direct-image statement specifies the proper coefficient adjunction transpose followed by extension by zero; it is this specification, not naturality in an unspecified variable, that makes b unchanged when all the underlying maps, sites and coefficients are literally the same. The exceptional statement specifies the unique transpose of the displayed counit composite. Under the stipulated counit-preserving identifications the composite is identical, so uniqueness gives equality of c. The coefficient-independent compactification, separated finite-type scheme hypotheses, smooth pure dimension, finite rings and common power-of-ell annihilator are all in the item. The unit R_m,Y belongs to the required constructible finite-Tor category. I did not assume A flat over R_m.

For Step 2 I read det-sp-finite-general-ring and its source statement. Its first clause gives precisely the composite with inverse c; its second clause says it is the direct diagonal/DNC orientation, so this is a comparison of the specified normalization, not of arbitrarily selected isomorphisms. I read det-sp-scalar-extension-functor: its morphism action and Tate-line identifications justify applying scalar extension to an equality and retaining the displayed target. Both f and its retagging satisfy the same finite-field and smoothness hypotheses. This step invokes the existing theorem instead of creating a node for a clause of the item.

For Step 3 I read def-weil-l-adic-coefficient-extension, including its finite quotient-ring clause, and the full strict-tower definition sk-def-sp-coefficient-towers. Given ell = u varpi^e, choosing em >= n proves annihilation directly; it works at n=1, in ramified extensions, and at e=1. The equality of ideals (ell^r)=(varpi^(er)) proves that B_r is one of those finite quotients, without conflating the two index conventions. Different admissible annihilating exponents cause no choice of a different normalized orientation: Step 2 compares the fixed diagonal orientation with its formula for each admissible exponent.

For Step 4 I read det-sp-tower-gluing and det-sp-tower-gamma both as live statements and in their source files, and read the latter's source proof explaining degree-zero tower maps. Gluing clause (3) supplies finite evaluations compatible with units and counits; clause (2) supplies the counit-preserving identification. Gamma clause (1) gives both isomorphisms and identifies their finite levels as inverses of Pi. I read det-sp-coefficient-towers-abelian and its source: it makes the strict tower category abelian and evaluations exact, exactly what is needed for evaluation to commute with the single-complex construction. I read lem-weil-pbc-derived-single-fully-faithful, its Mathlib source FullyFaithful.lean (faithful instance at 37, full at 45), and Stacks Tag 06XS, derived.tex label lemma-negative-exts, part (2). Its statement applies to every abelian category, thus both the strict tower category and each finite module-sheaf category. Applying fullness first gives an actual tower map w; applying faithfulness at each level makes its components identities. Componentwise equality is then literally the strict-tower morphism definition. This is a short assembly argument, not an invocation of arbitrary derived evaluation faithfulness. It covers d=0 as well as nonzero d and needs no inverse-limit argument.

For Step 5 I reopened gluing clause (3) and the two finite coefficient-comparison statements. The transition is specifically f^! of the quotient map composed with c, so Step 1's same-transpose argument for B_r -> B_s compares it directly. The proof of Step 1 works for these finite ring maps as stated; it did not use anything special about the initial ring R_m. Thus equality retains the quotient transitions and does not merely assert equality of a family of disconnected finite orientations.

I checked C1 and C4 step by step: every substantive theorem is among these cited statements, and citations.json contains an exact excerpt for each use. All proof steps are under 2000 characters (819, 503, 433, 1221, 682 at preparation); none hides a further comparison lemma. I checked B's statement-only/new-node requirements (there are no new nodes), C's cycle and citation requirements, D's prohibition on relabelling a clause as a new node, and E's hypothesis and coefficient-category distinctions. The general finite-ring and tower tools are explicitly declared in split_report.tool_uses for review where needed across units. The full-faithfulness citation is already a Mathlib leaf.

I ran the prescribed logged searches for the item: grep found no purity/tower-retagging declaration; LeanSearch returned normalized field traces and restriction maps; Loogle returned generic adjunction/counit structures; the first LeanFinder phrasing returned real-vector-space orientations and base-change algebra, and the second returned general single-complex/Ext results. I read the returned types. The generic degree-zero material is already represented by the cited existing Mathlib leaf; none states the full item or makes it a one-line Mathlib specialization. The exact query text and actual results are retained in the node from searches.jsonl, alongside the item's existing searches.

The first dry run requested longer quotation witnesses for three citations. I replaced these with their full substantive clauses (and expanded tower-gluing witnesses to the exact evaluation/transition clause), without changing the proof. The preliminary server review_split passed.
