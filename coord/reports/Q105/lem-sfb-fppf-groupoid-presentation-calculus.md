# Worker report: lem-sfb-fppf-groupoid-presentation-calculus

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-fppf-groupoid-presentation-calculus.json: split into two steps using existing definitions and the existing general invariant-base-change theorem; not a Mathlib leaf.
- citations.json: one verbatim statement quotation for every step/dependency pair.
- searches.jsonl: four newly executed Mathlib searches, retained exactly as logged.
- report.md: this report.

No new nodes and no Mathlib leaves were created.

## Attachments

None. Searched lean/WeilConjectures for the exact item tag, quotient-stack terminology and stackification/base-change terminology. No declaration states the item. No compiler, Lake or build command was run.

## WANTED

None: the relevant Stacks source is available locally.

## Findings and corrections

The live item had an empty proof. Its source is correctly identified as Tag 0DTG, groupoids-quotients.tex, lemma-base-change-quotient-stack (confirmed against tags/tags). That theorem is more general than the item: neither finite local freeness of the source and target nor scheme representability of the groupoid is required. The item remains the same specialization with its original hypotheses; only doubled TeX backslashes were normalized.

The full DAG/tag search found the pre-existing lem-sfb-quotient-stack-invariant-base-change, which states precisely the general 0DTG theorem. I reused that node instead of creating a duplicate, including instead of extracting a new lemma that would restate this item. Its proof is currently empty: this delivery does not claim that the general node is finished; it supplies the item's legitimate dependency on it. The reviewed stackification/local-equivalence nodes were also inspected but are unnecessary once the existing general statement is reused.

Whole-blueprint searches using blueprint_refs.py for "quotient stack", "stackification" and "0DTG" returned no imported match. Read the latest blueprint unit and direct-images proof, especially paragraph (3). The inherited moduli/alteration prerequisite and unit route are retained. The ancestor command explicitly returns None on this existing creation chain, so the existing null blueprint.from.node and full via list are preserved; the precise from.place was already filled. This is a supporting node, not the unit's key statement: no unit realization fields were changed.

Mathlib searches were run through msearch.py with the exact queries in the appended records: LeanFinder for quotient-stack invariant base change; LeanSearch with a second formulation using fppf stackification and two fibre products; Loogle for Stack and pullback; grep for quotient-stack/stackification/fppf-groupoid terminology. All four services returned successfully. LeanSearch returned scheme morphism-property base-change stability and stack-condition definitions; LeanFinder returned ringed-space composition and scheme-module pseudofunctor coherence, plus stack-to-prestack implications. Their printed signatures do not construct quotient stacks or assert their base change. Loogle and grep returned zero hits. These are no-match results, not unavailable searches.

## Not duplicates

No new-node pairs exist. The item is a specialization of the already existing lem-sfb-quotient-stack-invariant-base-change (same Tag 0DTG): this is explicitly reused as the proof dependency. No duplicate node was introduced. Any eventual merging of these existing records belongs to the maintainer.

## Review by Q105

I read the complete proof of Tag 0DTG in groupoids-quotients.tex, from the statement through the inverse on descent data. The source treats arbitrary groupoids in algebraic spaces and arbitrary invariant maps, constructs the map by forgetting the extra base coordinate, and constructs its inverse by adjoining that coordinate to local objects and arrows. I compared this with the complete statement of lem-sfb-quotient-stack-invariant-base-change: it has exactly these hypotheses and asserts the required 2-cartesian square for fppf stackifications. Thus citing it does not require anything from its proof or an unstated descent assertion.

For step 1 I read def-trf-scheme-algebraic-space, including its actual representable fppf sheaf h_T rather than an unrelated space, and def-a1-scheme-groupoid-laws, which spells out the functorial object/arrow laws. The step retains exactly P(T), Q(T) and every groupoid operation under the scheme-to-space interpretation. Its base-change pairs have one common B' coordinate and the invariant map gives the equality needed for both endpoints; composition retains that coordinate. This is a direct check of the cited definitions and is marked elementary. There is no claim that the base-changed objects remain schemes.

For step 2 I reopened the general node and checked each substitution: S = Spec k, U = P, R = Q, X = B, X_1 = B'. P and Q are algebraic spaces by step 1; the given equality as = at is the required invariance; B and B' are algebraic spaces and g is an arbitrary morphism as required. The groupoid and quotient conventions agree on all test schemes. The cited square being 2-cartesian is exactly the equivalence in the item, including its canonical projections. The finite-locally-free hypothesis is retained in the item but is not required by the general theorem. This step is marked non-elementary because it invokes that theorem. It cites the theorem's statement, not any construction hidden in its proof.

For B1-B10 there are no new nodes to audit; the item is self-contained with its original definition dependencies, has no new notions, and its TeX was normalized. For C1-C8 every non-elementary fact is the existing general theorem, every cited statement was opened, and each step/node quotation was checked to be a literal substring. The general node has no proof dependencies, so the new proof edge cannot form a cycle through its proof; it belongs to the same unit. For D1-D5 the reuse is an existing genuinely more general result, not a newly manufactured restatement. The two steps have 812 and 757 characters, so no long step conceals a lemma.

For E1-E6 I checked the empty groupoid and the empty base change (the relevant fibres are empty), the identity groupoid Q = P (ordinary sheaf fibre product), and a finite group acting on a point (automorphisms are retained by the stack quotient). No argument identifies a quotient stack with its sheaf of isomorphism classes. The general source assumes neither an etale nor a flat change of base, so none was inserted. No statement dispute, source error, route change, or SGA source is involved. No mathematical work remains in this split beyond the independently queued general node. The required remote dry run and push follow this review.

## Unfinished work

None for this one-level split. The existing general theorem remains an independent stage-1 item.
