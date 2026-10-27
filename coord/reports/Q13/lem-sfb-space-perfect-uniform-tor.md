# Stage-1 report: lem-sfb-space-perfect-uniform-tor

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-perfect-uniform-tor.json: item, statement, split; no Mathlib match.
- citations.json: one verbatim statement quote for each step/node citation.
- searches.jsonl: actual msearch results, retained with this delivery.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. The exact blueprint tag has no declaration in lean/WeilConjectures. The concept search found no project declaration about perfect structure-module complexes on algebraic spaces; scheme and constant-coefficient statements do not prove this item.

## WANTED

None. All sources used are in literature/stacks-project/.

## Corrections and scope

The item was statement-only, not a completed earlier attempt. Its statement, statement dependencies, creation record and inherited blueprint provenance are retained. The proof now supplies the local cohomology argument, a finite subcover of the open images of etale model charts, and derived tensor restriction followed by a sheaf test. The endpoints include 0 so that the empty-space case does not require minima of empty sets. No quasi-separatedness or Noetherian hypothesis has entered.

The inherited provenance points to det-thm-sf-ctf-stability-direct-images. The current latest blueprint has this id in sk-thm-sf-ctf-stability-direct-images.proof.md; I read its clause (3) and the current unit section. The algebraic-space duality material is a supporting dependency in the inherited chain, not a replacement of the compactification/direct-image unit route. blueprint_refs.py ancestor reports None for this already-created chain; its existing from.node is accordingly retained as null, and its detailed from.place and via list are retained. Searches of the whole blueprint for perfect, Tor amplitude, uniform Tor, perfect quasi, 08JL and 08G8 found no imported node stating this algebraic-space conjunction. The analogous scheme facts and fixed-coefficient constructibility statements have different domains.

## Mathlib searches

Ran msearch.py for this item with leanfinder, loogle, grep and leansearch; the exact queries and actual hits are in the item and searches.jsonl. The second semantic phrasing asked about a locally bounded finite projective complex. LeanFinder returned derived-category cohomological support results; LeanSearch returned projective-dimension and bounded-support results. Those do not address the structure sheaf on a small etale algebraic-space site, its quasi-coherence, or globalization of local Tor intervals. Loogle and grep had no hits. No unsuccessful service call was recorded as mathematical absence.

## Not duplicates

No new nodes. Reused lem-sfb-space-qcoh-kernels-colimits for quasi-coherent kernels, images and cokernels; lem-sfb-split-perfect-dual-tor-window for the local tensor bounds; lem-a1-etale-scheme-map-open-image for openness; lem-weil-pbc-ringed-sheaf-slice-adjunction for exact slice restriction; lem-weil-pbc-ringed-topoi-derived-tensor-pullback for the derived tensor comparison; and lem-trf-space-fibre-products-etale-covers for the actual pulled-back coverings. In particular no node is created for a clause of the item, for a finite minimum/maximum, or for the sheaf separatedness argument.

## Review by Q13

I read spaces-perfect.tex Tag 08JL (lemma-pseudo-coherent), including its strictly-perfect computation, and Tag 09MB (lemma-ext-from-perfect-into-bounded-QCoh), whose proof chooses the global Tor interval of the perfect dual. I also read sites-cohomology.tex Tag 08G1 (lemma-tor-amplitude) and Tag 08G8 (lemma-perfect). The finite globalization used here is the finite-cover argument of spaces-properties.tex Tag 03H6 (lemma-quasi-compact-affine-cover), using etale images rather than asserting that an etale cover is an open cover by schemes. The source paragraph says “finite surjective morphism” at its end; that adjective is not needed or used here. All we retain is the finite selection of etale maps.

For Step 1 I opened def-trf-algebraic-space and def-weil-pbc-strict-perfect-coefficient-package. The first gives the etale scheme atlas and the covering convention. The second gives bounded representatives and the degreewise splittings after passing to a cover of that atlas. Thus the splitting maps are on each degree, not chain splittings into one free complex. No uniform interval or bound on ranks is assumed. This step is elementary unfolding of the two cited definitions.

For Step 2 I read every cited statement. The local-presentation definition makes finite free modules quasi-coherent and permits testing the property on a cover. The kernels-colimits node explicitly includes kernels, cokernels and images of arbitrary quasi-coherent module maps, without a Noetherian assumption, on any algebraic space. It applies to each scheme chart as an algebraic space. Its source is spaces-properties.tex Tag 03M1 (lemma-properties-quasi-coherent), which I read. I checked the retract argument explicitly: the fixed points of i*p are precisely the image of i, so no closure-under-arbitrary-subobjects assertion is being used. Kernels and images of the differentials and their quotient therefore give quasi-coherent homology. The ringed-sheaf-slice-adjunction statement explicitly gives exact module restriction; writing homology as a kernel modulo an image proves commutation with that restriction. The fibre-products-etale-covers statement explicitly supplies covering families after any base change; applying it to each site object V makes the local-presentation descent legitimate. No claim is taken from the proof of one of these nodes instead of its statement.

For Step 3 I opened lem-a1-etale-scheme-map-open-image and read spaces-properties.tex Tag 06NF (lemma-etale-image-open). It gives the actual open subspace whose point set is the image of each scheme chart. Thus the assumed topological quasi-compactness supplies a finite subcover of these open images. The conclusion is that finitely many etale maps are jointly surjective, not that they are open immersions or finite morphisms. Taking the minimum of the lower endpoints together with 0 and the maximum of the upper endpoints together with 0 is an elementary finite-integer calculation. It neither requires intersections to be affine nor the chosen charts to have uniformly bounded ranks.

For Step 4 I reopened the slice-adjunction and ringed-topoi-derived-tensor-pullback statements, and read sites-cohomology.tex Tags 0G7E (lemma-pullback-K-flat) and 07A4 (lemma-pullback-tensor-product). The localization has the restricted structure ring and identity structural ring map, so the exact module pullback is precisely restriction and the derived tensor comparison is an isomorphism in the derived category. The split-perfect-dual-tor-window statement has exactly the first Tor bound needed here for any sheaf M; its additional duality clauses are not used. Its hypotheses are the finite degreewise splittings and interval support already chosen in Step 1, not projectivity of global sections or global projectivity of sheaves. The test M is completely arbitrary, not only quasi-coherent. Finally the fibre-products-etale-covers statement supplies the covering of every V; a section restricting to zero on that cover is zero by the sheaf uniqueness axiom. This proves vanishing of the sheaf itself, including the empty cover, and completes the global assertion.

I checked delivery-errors B through E against the actual files: there are no new nodes requiring notions or duplicate disambiguation; statement sources are tags and labels; no unrun searches were added; the quoted citations are from the statements actually used; no step hides a standard non-elementary auxiliary claim; no item clause was merely renamed. All proof steps are shorter than 2000 characters. The off-unit citations are generic tools and are declared in split_report.tool_uses, not in the maintainer-owned tool_uses field. No source from SGA is used.

Small cases checked: the empty algebraic space (empty subcover and interval [0,0]); E=0; a shifted finite free structure module (the interval is enlarged if needed by 0, which still proves the statement); nontrivial finite projective retracts (kernel of 1-i*p); and noncoherent rings (kernel closure gives quasi-coherence, not finite generation of homology). Dropping quasi-compactness would allow infinitely many components with unbounded shifts; the finite-subcover step is exactly where the actual hypothesis is needed. No changed target statement or statement dispute is involved.

## Unfinished work

None for this stage-1 split. It reuses existing supporting DAG nodes, some of which remain open for later work; it makes no claim to have written or compiled Lean.
