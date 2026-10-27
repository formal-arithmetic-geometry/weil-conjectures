# Worker report: lem-sfb-field-specialization-trdeg-drop

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-field-specialization-trdeg-drop.json`: statement, split; five proof steps; no exact Mathlib match.
- `citations.json`: nine step/node pairs, with verbatim statements copied from the existing nodes.
- `searches.jsonl`: actual Mathlib search results logged by msearch.py.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The sandbox originally contained no item node or previous split. The live item was unsplit with an empty proof, and no stage-1 repair order exists.

## Attachments

None. Searched the project library for the exact blueprint tag and for the specialization/transcendence-degree assertion. No project declaration states the item. Existing affine residue-field declarations and finiteType_domain_ringKrullDim_eq_trdeg are ingredients, not attachments for the scheme-level specialization assertion.

## WANTED

None. All sources needed for this split are present.

## Findings and changes

The statement is correct as imported. Stacks morphisms.tex, Tag 06RU (lemma-dimension-fibre-specialization), assertion (3), gives precisely the claimed inequality for nontrivial specializations in a fibre. Over Spec k there is only one fibre. Its proof cites Algebra Tag 06RP (lemma-tr-deg-specialization); I read that statement and proof in algebra.tex. That proof compares dimensions of the two prime quotients by Tag 00P0 (lemma-dimension-prime-polynomial-ring). I expanded the finite-dimensional strict inequality into a lifted prime-chain argument instead of creating a node restating 06RP, an affine version of this very item.

Whole-DAG searches by tag and concept found the existing finite-type-domain dimension theorem and the affine-point/residue-field theorem. They are used directly. The prime-chain inequality and finite generation of quotients are elementary steps, not new nodes. Statement dependencies remain exactly those of the imported item; the proof dependencies are exactly the union of the five steps' uses.

Read the chapter and unit records, SETUP's three-level rule, and the current blueprint `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, especially paragraph (3). The inherited creation chain describes the lower alteration/moduli route supporting direct-image preservation. The current blueprint's paragraph itself is an assembly of direct-image inputs and does not literally mention those lower algebra lemmas. `blueprint_refs.py ancestor` returns None for this old creation chain; I retained its explicit inherited place and via list, without inventing a blueprint ancestor. Whole-blueprint searches for transcendence, specialization, stalk, prime and 06RP found no equivalent imported statement. The generic 00P0 theorem of unit sk-thm-p1 is declared in split_report.tool_uses; it implements the source's algebraic input and does not replace a step of the higher unit route.

Mathlib searches were run only with the required msearch.py command, with the scheme assertion and a second phrasing in terms of strict inclusion of primes. LeanFinder gave residue-field maps, Jacobson closed-point facts, non-strict transcendence inequalities and finite transcendence-degree results. LeanSearch gave surjective-algebra transcendence monotonicity, specialization composition, and stalk-specialization maps. Loogle returned no result mentioning both trdeg and Specializes. The grep searches found no scheme-level strict-drop declaration; the broader grep returned finite-transcendence-degree and transcendence-basis results. A further dimension/fraction-field phrasing gave rank and finiteness results rather than the required scheme statement. The actual queries, hit names and verdicts were appended to the item, preserving its inherited searches. None of the hits is an exact or one-line scheme-level specialization result.

## Unfinished work

None in the one-level split. The existing dimension theorem and affine residue-field theorem retain their own DAG proofs and are cited only through their statements. No Lean file was written and no compiler, Lake or build tool was run.

## Not duplicates

No new nodes were created. The existing `lem-weil-pbc-finite-type-domain-dimension-trdeg` is more general algebraic input, and `lem-weil-pbc-spec-field-point-residue-field` supplies the affine residue-field interpretation. Neither is a restatement of the scheme specialization assertion.

## Review by O3

I read delivery-errors B through E in full and checked the split against the opened source and node statements. The source for the item is 06RU (3); I also read its 06RP proof and the 00P0 statement and proof. For the residue identification I read the Local rings paragraph of algebra.tex identifying kappa(p) with Frac(A/p), and the scheme-points discussion before lemma-characterize-points (01J9) in schemes.tex. There are no new-node sources to review.

Step 1 uses the actual affine-cover definition in def-weil-finite-type-morphism: choosing a member of that cover ensures the coordinate ring is finite type. It does not incorrectly assume that arbitrary affine opens have finite-type coordinates from the definition alone. The statement of lem-weil-pbc-affine-open-spec-points supplies the open immersion with image U and the representing primes. The specialization condition forces x into the chosen neighbourhood of x prime, directly from closure. Distinct points give distinct primes through the open-subscheme isomorphism.

Step 2 uses def-weil-affine-spectrum's prime spectrum and Zariski topology and def-weil-pbc-finite-type-algebra's polynomial-generator definition. The text spells out closure(p)=V(p) and the quotient-generating family. The prime ideals are proper, so both quotients are nonzero domains. This needs neither reducedness of A nor irreducibility of X.

Step 3 cites clauses (1) and (2) of lem-weil-pbc-spec-field-point-residue-field. Its statement explicitly says that the affine residue field is a fraction field of the prime quotient and that the identification with the ambient scheme residue field respects the map from the coordinate ring. Thus it supplies exactly the identifications used, including compatibility with k by composition with k to A. def-weil-residue-field states the induced field-extension structure, and def-kun-transcendence-degree defines the invariant. A k-isomorphism preserves it because polynomial relations with k coefficients are preserved in both directions.

Step 4 cites the opened statement of lem-weil-pbc-finite-type-domain-dimension-trdeg: it explicitly asserts finiteness and equality for the dimension and fraction-field transcendence degree. The hypotheses are verified for each of A/p and A/q in step 2, over the original field k. No equidimensionality or maximality of p or q is assumed. No property from the proof of the cited node is used.

Step 5 uses def-weil-pbc-krull-dimension-ring's supremum of finite strict prime-chain lengths. I wrote why a maximal-length chain exists (the lengths form a nonempty bounded subset of the natural numbers), why inverse images under B to C are prime and distinct, and why the zero prime of B is strictly smaller than the first inverse image: that image contains the nonzero ideal q/p. This proves d at least e+1 and gives the direction of the desired inequality. It is the elementary chain argument left implicit in 06RP, rather than a hidden comparison lemma.

I tested the generic-to-closed specialization on A=k[t], giving 1>0, and the chain (0) inside (t) inside (t,u) in k[t,u], giving 2>1>0. A nonreduced chart k[t,epsilon]/(epsilon^2) has the same relevant prime quotients; the proof still applies. Empty schemes, zero affine rings, and zero-dimensional finite-type schemes cannot provide the distinct specialization pair. Disjoint unions with no global quasi-compactness and nonseparated schemes cause no problem, since one finite-type affine cover member containing the specialization is sufficient. The argument works over finite and imperfect fields. It uses no global dimension bound for X and no separation or reduction assumption.

For C1/C4 I compared every use with the cited statement and copied the whole relevant node statement verbatim into citations.json. For B/D I checked that no unnecessary definition, duplicate, affine restatement or elementary lemma was made into a new node. For E I checked all field, finite-type, nonzero-domain and strict-inclusion hypotheses as above. The five steps have respectively 514, 550, 530, 325 and 734 characters: no step exceeds the 2000-character review threshold. No statement dispute or source correction was necessary.
