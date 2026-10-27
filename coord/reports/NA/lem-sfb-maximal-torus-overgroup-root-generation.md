# Stage-1 report: lem-sfb-maximal-torus-overgroup-root-generation

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-maximal-torus-overgroup-root-generation.json`: item, statement; split following Milne 21.66 using existing nodes. Mathlib searches found no exact theorem or one-line specialization.
- No new nodes and no Mathlib leaves. `citations.json` contains the fourteen step-to-node quotations. `searches.jsonl` records the five actual new search calls, including the second semantic phrasing.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint id, maximal-torus terms and root-subgroup spellings. No matching declaration was found. No Lean was written or compiled.

## WANTED

None: Milne, Algebraic Groups (2017), is present locally.

## Findings and changes

The item was unsplit with no earlier sandbox copy or report and no released repair note. The mathematical statement is unchanged. Milne 21.66 allows a smooth connected subgroup normalized by T; our stronger hypothesis T contained in H makes the zero-weight term Lie(T), and avoids any need to prove smoothness of a general intersection with T. The root-containment clause of Milne 21.11(c) is not actually in the existing root-parametrization node's statement. Consequently I did not cite that node for containment: I derive containment from the existing positive-ray comparison plus the reduced, one-dimensional root decomposition.

The existing tangent-generation node explicitly quantifies over arbitrary closed containing subgroup schemes. Applying it to H intersect J proves the scheme-theoretic conclusion without assuming that J or its intersection is smooth. This is a proof, rather than transferring the item's clauses into newly named nodes. All cited statement nodes have the same unit as the item; no off-unit tool declaration is needed. The item is not the unit's key node, so no unit record was changed.

Whole-DAG searches for Milne 21.11, 21.66, 10.17 and root-generation/weight-decomposition terminology identified the existing positive-ray, rank-one, weight-decomposition, torus-smoothness and tangent-generation nodes. Whole imported-blueprint searches `root subgroup` and `maximal torus` returned zero matches. The ancestor command reports blueprint.from.node = None, consistently with the inherited record: its explicit from.place identifies the current latest blueprint's direct-images paragraph (3) and the supporting alteration/moduli/PGL chain. I preserve that ancestry and explain the current source place in split_report.blueprint.

## Unfinished work

None in this one-level split. Its existing cited prerequisites retain their own stage states.

## Not duplicates

No new nodes were created. Existing general inputs are reused instead of creating duplicates or extracting a clause of the item.

## Review by NA

I read Milne 21.66 on printed p.444, the theorem it cites (21.11(b),(c), pp.428--430), its positive-ray input (16.64, pp.348--349), and Corollary 10.17 with its proof on p.191. I also read 12.12 and 12.14 on pp.234--236 for character decomposition and smooth connected tori, and Stacks groupoids.tex, lemma-complete-reducibility-Gm (0EKK) and lemma-Gm-equivariant-module (0EKL), the references of the reused coherent-weight node. The current latest blueprint direct-images proof paragraph (3) supplies the inherited route; neither its unit nor chapter is altered.

For step 1 I opened def-sc-group-scheme-subgroup, def-sc-scheme-tangent-space, lem-sfb-affine-group-lie-tangent-calculus and def-weil-closed-immersion. The first gives subgroup closure on every algebra, the second defines the tangent map by composition with dual-number points, the third supplies its linearity and compositional compatibility, and the fourth gives the affine quotient description. Thus H is T-stable, its tangent space embeds equivariantly, and its affine coordinate ring is finitely generated; these are the hypotheses needed later. This step's elementary flag means a short consequence of these cited statements, not an uncited differentiability theorem.

For step 2 I opened lem-sfb-trivial-torus-coherent-weight-decomposition and lem-sfb-reductive-rank-one-reflections. The former actually states finite character-weight decomposition for coherent linearized modules; its application is on the Noetherian affine point Spec F and to a finite-dimensional representation. The latter actually states the zero-weight summand Lie(T), finite roots, one-dimensional root lines and the absence of proportional roots other than opposite pairs. Equivariance embeds each weight summand in its ambient weight space. Hence a nonzero H summand fills the ambient root line. No Lie-algebra eigenvalue or differential of a character is substituted for a torus character.

For step 3 I opened lem-sfb-torus-positive-ray-subgroup and lem-sfb-reductive-root-subgroup-parametrizations as well as the rank-one node. The positive-ray node explicitly states V_eta contained in Lie(K) implies U_eta contained in K for smooth connected stable closed K. The rank-one node makes that ray exactly the single root line. The parametrization node only identifies the resulting subgroup by its unique smooth connected stable root-line tangent space; it is not misused for a containment statement absent from its text. H meets every comparison hypothesis from the item and step 1. The converse is the injective tangent inclusion from step 1. This corrects the most tempting C4 error in this split.

For step 4 I reread def-weil-closed-immersion and def-sc-group-scheme-subgroup for the explicit sum-of-ideals intersection and its algebra points. I reread lem-sfb-multiplicative-type-largest-subtorus: it explicitly says every torus is smooth and connected. The root-parametrization node says the same for each root group, with its prescribed tangent space. Finally I reread lem-sfb-smooth-subgroup-tangent-generation: it applies to smooth connected affine finite-type ambient H and a finite family, and explicitly allows a containing subgroup K with neither smoothness nor connectedness. Step 2 verifies its spanning hypothesis. The ideals then give the factorization H into J, including nonreduced J. No descent from mere point-set containment is used.

For step 5 I checked that the family always includes T even if Phi_H is empty. If H=T, all root summands vanish and the argument returns H=T. If G=T, Phi is empty and the same argument applies; if the rank is zero there are no nonzero characters and the tangent-generation theorem still applies. A Borel in GL_2 illustrates a nonreductive H, with the positive root alone; G itself uses both signs. In characteristic p, weights remain characters (so e.g. alpha and p alpha are not identified by differentiating), and no characteristic-zero exponential argument appears. The argument never equates subgroups merely because tangent spaces agree: smoothness of the generators and the exact cited generation theorem supply that implication.

I checked B--E of delivery-errors.md against the actual files: no new statements or hollow definitions, no missing-source tags, every non-elementary use has an explicit existing-node citation, quotations are copied verbatim from statements, no proof-of-a-node substitution, no off-route edge and no dependency path from a cited input back to this item. Each non-elementary step has fewer than 2000 characters. The one-level proof retains the source's argument and its full hypotheses without restatement nodes or weakening. The honest searches returned abstract groups, root systems or Lie algebras, not the required algebraic subgroup-scheme theorem; all five services/calls succeeded and their results are recorded as no match.
