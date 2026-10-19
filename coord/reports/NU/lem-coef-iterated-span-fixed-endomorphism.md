## Files written

- dag/nodes/sec-six-functors/lem-coef-iterated-span-fixed-endomorphism.json: existing statement unchanged, now split into three elementary steps; no exact Mathlib match.
- citations.json: verbatim category statement for the one cited node in each step.
- report.md: this report. Existing search records were retained and fresh actual msearch.py records appended to the item. No new nodes and no Mathlib leaves.

## Attachments

None. Searched the read-only slopmaster2 WeilConjectures source for the exact blueprint tag and item id, iterated spans, span completions, fixed anchors and endomorphisms. The hits concerned other notions, not this declaration. No upstream master sorry was treated as a proof. No Lean was written and no build or compiler was run.

## WANTED

WANTED: Dwyer–Kan, Calculating simplicial localizations, Proposition 8.2(i) and following Proofs paragraph, printed p.29 (PDF p.13), for lem-coef-iterated-span-fixed-endomorphism. The paper is absent from the repository literature; I read the supplied Rochester PDF online, including the statement and the short Proofs paragraph. The node is correctly marked agent-written: the source motivates the completion argument but does not state this extracted finite-recursion assertion separately. No invented Stacks tag is claimed. The category convention was checked against literature/stacks-project/categories.tex, definition-category, Tag 0014, including the big-category remark.

## What was wrong or missing

The item had no proof. Its statement is true as written, including membership of e_0 in W even though this is not a separate hypothesis: e_0 q_0 = q_0 and q_0 in W imply it by the explicitly assumed two-out-of-three property. All objects and the square-completion rule are defined in the statement. In particular the rule is assumed to send a commuting triple to commuting output squares; no pushout universal property is required. No statement dispute or correction is needed.

The first reads raced with the shared refresh and saw the queue entry before its newly landed file. Once the file appeared I used the exact current repository copy, retaining its creation provenance, blueprint ancestry and existing Mathlib records. This was a transient read availability issue, not a reason to recreate or change the statement.

I read the chapter and unit records, and the current main-20261015 proof of prop-coef-integral-exceptional-adjoint. Its second paragraph contains the derived Hom / derived limit adjunction. The assigned item is already a technical descendant of that paragraph through the special-hammock square criterion. This split preserves that historical binding; it does not change the chapter, unit or route. No prohibited SGA source is used.

## What remains

Nothing remains for this one-level split. There are no new unsplit statements to deliver. The separate naturality node is not part of this item and is not used to prove it. The required dry run and push are performed with the standard delivery command.

## Not duplicates

The whole DAG and blueprint were searched for span completion, fixed endomorphism, iterated spans and fixed anchors. blueprint_refs.py search returned no blueprint match for span completion or fixed endomorphism; ancestor confirms prop-coef-integral-exceptional-adjoint. The existing square-criterion node uses this item, so citing it would be circular. The existing iterated-span-endomorphism-naturality node requires this item's specified sequence and asserts compatibility between two chains, so it is not an alternative proof or exact duplicate. No new node was created for elementary induction, span-map construction or two-out-of-three cancellation.

## Review by NU

I read the item, its immediate square-criterion use and separate naturality node, the category definition, chapter/unit records, the blueprint ancestor proof and Dwyer–Kan Proposition 8.2 with the Proofs paragraph. The item source gives functorial completions; the actual proof here supplies the elementary induction omitted in that brief source. I checked delivery-errors B–E against the written files. The statement was preserved verbatim, introduces every datum, writes its weak-subcategory and two-out-of-three meanings inline, and needs only the category definition as a statement dependency. No new node has a hidden proof, no new source/tag or Mathlib match was invented, and blueprint from.place and same_as remain filled. No step cites a definition for a theorem it does not state.

For Step 1, the only cited node is def-nagata-category, whose statement supplies objects, arrows and composition. The rest is exactly the item's own hypotheses: q_0 belongs to U, the output q_j belongs to U at every completion, U is contained in W, and two-out-of-three applied to the pair (q_0,e_0) yields e_0 in W. This also verifies that the next recursive input has the required U-leg. The proof does not confuse q_j with k_j or assume k_j lies in W.

For Step 2, the same category statement supplies the two identity equalities used for the input-span triple. The first input square is e_{j-1} q_{j-1} = q_{j-1} 1 and follows from the inductive invariant; the second is 1 h_j = h_j 1. The stipulated action of S therefore applies, with source and target both the exact same jth span, and produces an actual endomorphism of the already chosen D_j. Its output-square condition gives precisely e_j k_j = k_j e_{j-1} and e_j q_j = q_j. These are hypotheses defining the given rule, not an uncited functoriality theorem. Applying its specified arrow action makes the recursion specified without asserting uniqueness among all possible endomorphisms. No comparison between different chains is silently used here.

For Step 3, the category statement again fixes the composition convention. For the composable pair (q_j,e_j), both q_j and e_j q_j equal the same W-arrow; the third arrow e_j is consequently in W by the item's stated axiom. Finite induction proves the entire conclusion, with a stated base and successor. Each step is an elementary expansion of these hypotheses and identities, below 2000 characters, so there is no hidden non-elementary lemma requiring extraction. proof_deps is exactly the union of uses. The sole citation is a Mathlib category-definition leaf, so there is no off-unit theorem use or possible dependency cycle introduced.

Small cases were checked explicitly: n=0 leaves only the given e_0 and its cancellation proof; n=1 gives both output squares immediately; identity-only U forces each chosen q_j to be an identity and hence each fixing endomorphism to be an identity, consistently with the conclusion. For a noninvertible e_0, in sets take W=U=all maps, a one-point B_0, two-point D_0, q_0 the inclusion of one point, and e_0 the constant retraction onto it; a constant terminal output completion is functorial and propagates e_1=1 on the terminal set. Thus the proof does not accidentally require invertibility or normalization of S. An empty category admits no initial data B_0,D_0, so it creates no exceptional case. The same argument works in a one-object identity category. No hypotheses were strengthened.

I read the actual msearch.py results and tried two semantic phrasings. The first produced weak-equivalence cancellation and unrelated Guitart/model-category statements; the second produced small-object and cell-complex constructions. LeanSearch returned square/individual-span structures, Loogle returned zero hits, and grep returned linear-span terminology. I read the relevant signatures and source at ModelCategory/Instances.lean (two-out-of-three cancellation), CommSq.lean (square definition and map), Pullback/Cospan.lean (spanHomMk), and SmallObject/Construction.lean (chosen actual pushout construction). None gives this finite recursive assertion for an arbitrary rule S in one specialization. Cancellation supplies only one clause and would not justify a Mathlib-leaf classification of the whole item. The old search records are preserved; the appended records exactly match the saved commands' tool/query text and returned JSON, with no unavailable service misreported as a negative search.
