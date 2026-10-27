# Worker report: lem-sfb-adequate-moduli-universally-submersive

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-adequate-moduli-universally-submersive.json: statement, split; not in Mathlib as a complete adequate-moduli theorem. Three proof steps, no new nodes, no Mathlib leaves.
- citations.json: verbatim statement quotations for every step/node citation.
- report.md and searches.jsonl: report and actual search log.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag, adequate-moduli terminology and submersiveness found no project declaration stating the item. Smooth polynomial presentations and quotient maps of flat schemes are different results.

## Wanted literature

WANTED: literature/alper-adequate-moduli-spaces-arXiv-1005.2398.pdf, Alper, Adequate moduli spaces and geometrically reductive group schemes, arXiv:1005.2398v3, Theorem 5.3.1(1)--(3), Proposition 5.2.9(3), Lemma 5.2.11, for lem-sfb-adequate-moduli-universally-submersive. I read the primary text at https://arxiv.org/html/1005.2398v3; no PDF exists locally and none was downloaded. The local-literature rule therefore leaves proof_origin.by as agent.

## Findings and changes

The imported statement is correct and is unchanged. Arbitrary base change need not preserve adequate moduli spaces: Alper Proposition 5.2.9(3) gives an adequate map followed by an adequate homeomorphism, and Example 5.2.10 warns against assuming adequacy of the original base-changed map. The existing node lem-sfb-adequate-moduli-topological-images already states surjectivity and closedness for every algebraic-space base change, precisely the geometric input to Theorem 5.3.1(3). The existing lem-sfb-smooth-presentation-closed-subsets states continuity and base change of set-theoretic images. I reuse both statements instead of creating a base-change factorization or closed-substack factorization node. Neither currently depends on this item, and both belong to its unit.

The ancestor command reports None, as in the inherited blueprint.from.node; I retain the inherited ancestry and exact from.place. Blueprint searches for adequate moduli, universally submersive, 5.2.9 and closed substack returned zero imported-blueprint matches. The newest blueprint chapter and unit were read alongside the DAG chapter/unit records. This helper realizes the inherited direct-image alteration/GIT prerequisite and changes no chapter or unit route. The item is not a unit key node.

Five actual Mathlib searches were run through msearch.py: two LeanFinder phrasings, Loogle, source grep and LeanSearch. All services answered. Mathlib AlgebraicGeometry.Flat.isQuotientMap_of_surjective (Mathlib/AlgebraicGeometry/Morphisms/Flat.lean:124) requires a flat morphism of schemes, whereas our source is a stack and no flatness is given. Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed.lean:43--50 concerns schemes and assumes universal closedness. Topology.isQuotientMap_iff_isClosed is relevant only to the final elementary topology argument. None proves the item's geometric input. Earlier searches were retained; the five new entries use the exact logged queries.

## Not duplicates

No new nodes. I reuse lem-sfb-adequate-moduli-topological-images and lem-sfb-smooth-presentation-closed-subsets. I also read lem-sfb-adequate-moduli-universal-closed-topology (only scheme base changes) and lem-sfb-adequate-geometric-fibres-submersion (contains the item's conclusion plus geometric-point claims); the former is narrower in base-change objects, and using the latter would obscure the actual quotient-topology argument. Nothing is copied into a new node.

## Review by Q98

I read Alper Theorem 5.3.1 in the primary HTML, including its proof: surjectivity is obtained through Proposition 5.2.9(3), closed images through Lemma 5.2.11 and surjectivity, universal closedness through the base-change factorization, and submersiveness is the final elementary implication. I also read Proposition 5.2.9(3), Example 5.2.10 and Lemma 5.2.11. There are no new nodes needing independent source checks. For the reused topology node I read local Stacks stacks-properties.tex, Tag 04XH (lemma-points-cartesian) and Tag 04XL (lemma-topology-points), and verified that they give surjection onto the fibre product of point sets and continuity for stack morphisms. Spaces are regarded as discrete stacks, so these apply to the displayed square. Their topology is detected by scheme atlases as in the item.

Step 1 takes only original surjectivity from the exact statement of lem-sfb-adequate-moduli-topological-images. It uses the explicit image-base-change sentence of lem-sfb-smooth-presentation-closed-subsets to identify the image after T to Y with the inverse image of the original image. That same node explicitly states continuity and atlas independence; these are not inferred from a definition of adequacy. Every object in the cited square satisfies the stack/space hypotheses, and no flatness or finiteness of T is needed.

Step 2 uses exactly the universal closed-map sentence of lem-sfb-adequate-moduli-topological-images. Its quantifier is over algebraic spaces T, not just schemes, and its hypotheses are exactly the original adequate moduli map over a field. It is not applied to a new map claimed to be adequate. The unused intersection-of-images clause is not needed. Step 3 has no external geometric input: it uses continuity and the previous surjectivity and closedness, writes out h(h^{-1}(T minus V)) = T minus V, and takes complements. The elementary flag is justified by these set identities, not by a hidden algebraic-geometric theorem.

I checked B--E point by point with both cited node statements open. No new statement, definition, proof sketch inside an unsplit node, unchecked tag, unperformed search, cross-unit proof dependency, or circular citation was introduced. Each non-elementary step cites the precise statement it needs; citations.json contains literal substrings. The statement is not weakened, and no step exceeds 2000 characters. Small cases checked: empty T makes all assertions vacuous; identity maps recover the original topology; for V empty or all of T the complement identity is exact; a nonempty target cannot acquire an empty fibre after base change because the image-base-change theorem forces full image. Non-flat and non-Noetherian base changes are covered by the existing closedness quantifier, without adding hypotheses. The final inference fails without surjectivity, which is why Step 1 is established separately.

## Unfinished work

No work within this item's split remains. The two existing geometric inputs remain their own stage-1 items; they are cited as statements, without editing or claiming them. Delivery validation follows below.

## Validation

The first dry run required a longer verbatim quote for original surjectivity (minimum 40 characters). I included the immediately preceding convention sentence with that surjectivity sentence; no mathematical change was needed.
