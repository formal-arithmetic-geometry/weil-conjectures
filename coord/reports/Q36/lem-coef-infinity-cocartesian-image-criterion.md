# Worker report: lem-coef-infinity-cocartesian-image-criterion

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-cocartesian-image-criterion.json`: existing statement node, now split in four steps; no Mathlib match. The statement is unchanged.
- `citations.json`: six entries, one for each step/node citation, checked against the current node statements verbatim.
- `report.md`: this report. `searches.jsonl` is the search command's own output; `prepare.py` is sandbox-only preparation code, not a delivery node.

New nodes: 0. Mathlib leaves: 0. No unit file changed.

## Attachments

None. I searched both supplied project source trees by the exact blueprint id and by cocartesian/image/criterion/mapping-square terminology. No project declaration states this coherent quasicategorical comparison. Ordinary fully faithful functor and six-functor results do not state it. Upstream master is reference material, not evidence of closure.

## WANTED

WANTED: Lurie, Higher Topos Theory, Proposition 2.4.4.3, printed pp. 131–132, for lem-coef-infinity-cocartesian-image-criterion (opposite dual and its natural mapping-square presentation). Read online at https://people.math.harvard.edu/~lurie/papers/HTT.pdf on 2026-10-17; no archival copy found in the supplied literature listing.

WANTED: Kerodon Corollary 8.3.5.8 (046J), Remark 8.3.5.9 (03PD), and Theorem 4.4.4.4 (01DK), for lem-coef-infinity-cocartesian-image-criterion. Read online at https://kerodon.net/tag/046J, https://kerodon.net/tag/03PD and https://kerodon.net/tag/01DK on 2026-10-17. These identifiers are Kerodon identifiers, not Stacks tags. No Stacks statement supplies this quasicategorical result. I did not download or modify literature.

## Corrections and route

The original node had a complete, true statement but an empty proof. Its source place described a proof obligation rather than a numbered source theorem. I supplied an agent argument, with proof_origin.by=agent, from existing DAG lemmas. I retained every hypothesis, including both inner fibrations, and the image-only conclusion. The new proof makes no assertion about tests at other vertices of F.

The central issue is coherence: the equality qT=p identifies the bottom rows and the actions on all simplices. Four equivalences of corner spaces, without a map of whole squares, would not establish the conclusion. Step 2 uses the existing fixed-edge prism statement to justify the comparison on the commutation witnesses as well as on faces. Thus no new node merely relabels a clause of the item.

I read the chapter record sec-six-functors, unit sk-prop-sf-biduality-general (its steps list is empty), and the ancestor prop-coef-integral-exceptional-adjoint in historical master and the separate main-20261015 proof file under sk-thm-sf-package. The inherited ancestry points to its second paragraph's derived Hom adjunction. This is generic coherent-category infrastructure beneath that calculation, not a replacement coefficient or geometric route. The item's from.place now identifies the actual current proof file and its particular image-test subclaim. All non-definition lemmas used are already in the item's unit, so no off-unit tool declaration is needed. No SGA source is used.

## Existing-node and Mathlib searches

No new node was required. The DAG already has the coherent Hom transformation, fixed-edge prism witness naturality, pointwise equivalence test, mapping-space cocartesian criterion and whole-square pullback recognition. I opened and read their statements rather than relying on their titles or proofs. Dependency traversal found that none reaches this item (the largest of the five traversals had 402 nodes), so citing them creates no cycle.

Whole-blueprint searches using tools/blueprint_refs.py for "cocartesian image criterion", "fully faithful functor mapping spaces cocartesian", "hom bifunctor" and "whole square" found no matching blueprint node. The hom-bifunctor search also returned a derived module-Hom definition, which does not state this comparison. Searches in both blueprint snapshots for the relevant notions likewise gave no duplicate. same_as remains empty.

I preserved the six Mathlib-search records inherited from Q63 and appended the actual Q36 searches from the command-generated log. The Q36 queries use two semantic phrasings, LeanSearch, Loogle and source grep. LeanFinder's IsCocartesian.map and IsStronglyCocartesian.map hits were read in Mathlib/CategoryTheory/FiberedCategory/Cocartesian.lean:44–103 and concern ordinary Hom-set factorizations. The alternate phrasing returned Square.IsPullback.of_equiv and iff_of_equiv, read in Mathlib/CategoryTheory/Limits/Preserves/Shapes/Square.lean:85–114: these compare strict squares of types. They do not compare coherent Kan-space squares. Mathlib/AlgebraicTopology/SimplicialNerve.lean:20–34 lists the locally Kan quasicategory theorem and the anima construction as projects, not this result. None is an exact match or a one-line specialization. The initial grep with a literal bracketed directory suffix was over-restrictive; its record explicitly says that it supplies no evidence of absence. Later meaningful grep queries and direct source reads supplied the check. Every added record is an actual logged command and retains its raw result; no service failure was presented as absence.

## Not duplicates

No new node was created, so there are no new/existing-node pairs to distinguish. The split adds only the proof of the existing item, citing the existing more general infrastructure.

## Review by Q36

I read HTT Proposition 2.4.4.3 and its proof on printed pp. 131–132 online. It gives the mapping-square criterion, and its discussion explicitly requires a coherent/strict presentation before asking for homotopy cartesianness. I also read the two Kerodon Hom-functoriality passages and the pointwise-isomorphism theorem online. My proof is the finite square specialization of the already recorded statements, rather than a claim that HTT separately numbers this item. There are no new nodes whose sources require review.

Step 1 uses exactly the statement of lem-coef-infinity-hom-bifunctor-functoriality: its Hom functors act by precomposition and its induced mapping maps form a coherent natural transformation. Restricting that transformation to the edge and the fixed target gives the top-row comparison. Smallness allows a fixed containing universe for all three quasicategories and their mapping spaces. Equality qT=p supplies the identical base objects and base edge. I checked every endpoint: the upper-left mapping space has source b, not a, and the common lower row runs from Map_B(p(b),p(z)) to Map_B(p(a),p(z)).

Step 2 uses lem-coef-infinity-fixed-edge-prism-coherence, whose statement gives actual triangle witnesses, the face equalities and naturality under any simplicial functor. All of p, q and T meet that hypothesis; it does not require them to be fibrations or essentially surjective. The strict identities T(t composed with v)=(Tt) composed with v and q(Tt)=pt are direct substitution on simplices. They apply to the displayed prism maps as well as faces. Thus the node's natural roof presentation gives compatibility of the entire square and its witnesses. No coherence theorem is being inferred from naturality merely on pi_0, and no new comparison lemma is hidden inline.

Step 3 uses the fully faithful definition in def-cbc-enhanced-diagrams-cones to obtain both upper-corner weak equivalences. Spaces are considered up to weak equivalence; the lower-corner maps are identities. The exact statement of lem-coef-infinity-pointwise-equivalences applies with the square nerve as its small K and the space quasicategory as target. Since step 2 already supplied the coherent transformation, its four vertex conditions suffice for an equivalence of whole diagrams. Pointwise equivalence alone is not used to manufacture the transformation.

Step 4 checks the full hypotheses of lem-coef-infinity-cocartesian-mapping-criterion: p is inner, E and B are quasicategories, and the given e is horn-p-cocartesian. It therefore supplies the square at this same z. The statement of lem-coef-kan-nerve-pullback-recognition includes both recognition with the specified commutation datum and preservation/reflection under equivalence of whole square diagrams. Those are exactly the two clauses needed to transfer the test to S_F. I did not take a general Yoneda or limit-invariance fact from a definition node.

I checked B a point (the absolute equivalence-edge case), T the identity, e a degenerate edge, and z=a or b. Empty mapping spaces remain allowed; no nonemptiness was used. If E is empty, the data e cannot be supplied, so there is no extra case to prove. To check the scope of the conclusion, let E=N([1]) with p=id, let F be the nerve of the category with arrows a→b and a→c and no b→c, and map a to 0 and b,c to 1 in B=N([1]). The full inclusion T of {a,b} meets the hypotheses, and e=a→b has the claimed tests at Ta,Tb. Its test at c fails: the upper-left corner is empty and the other three are points. This confirms that I have not silently asserted preservation of cocartesian edges against all vertices of F or added essential surjectivity.

I checked delivery-errors B–E: there are no new unsplit nodes, no self-containment or duplicate issues, no fabricated searches or Mathlib leaves, no source tags substituted for definitions, no use of an unproved clause of this item as a new node, and no hypothesis added. Every non-elementary ingredient is a cited statement (C1), and each verbatim quotation is present in the corresponding current statement (C4). proof_deps is exactly the union of the uses lists. All four steps are under 2000 characters (965, 1248, 682, 730); the simplex calculation in step 2 is a direct use of an existing naturality formula, not a new theorem with independent hypotheses. The item statement is unchanged and has no statement dispute.

## Unfinished work

None in the stage-1 split. The existing dependency nodes remain separate DAG work according to their own states. No Lean was written, compiled or built, and no live project or launcher file was edited.
