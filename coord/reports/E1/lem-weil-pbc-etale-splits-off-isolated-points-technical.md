# Worker report: `lem-weil-pbc-etale-splits-off-isolated-points-technical`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-splits-off-isolated-points-technical.json`: statement node, split; no new nodes.
- `coord/reports/E1/lem-weil-pbc-etale-splits-off-isolated-points-technical.md`: this report.

## Attachments

None.

## Wanted

None. The proof source is Stacks Project, More on Morphisms, Lemma 02LN, available as `literature/stacks-project/more-morphisms.tex` in the project literature checkout and verified at lines 12093-12131.

## Findings

The statement agrees with Stacks 02LN hypothesis by hypothesis. The source writes the selected points as points of the fibre; the node equivalently writes their images in `X` using the homeomorphism of the scheme-theoretic fibre onto the set-theoretic fibre. The case `n = 0` is not separated in the source and is now explicit.

The empty imported proof was replaced by five steps: 02LL supplies the elementary etale neighbourhood and finite open pieces; separated base change and properness make each piece closed; the finitely many closed images of pairwise intersections are removed from the base; the complement gives the decomposition; and clause (iv), implicit in Stacks, is proved from the fibre-product point description because `kappa(s) -> kappa(u)` is an isomorphism.

No new nodes were required. Existing DAG searches found every non-elementary ingredient. The item's Mathlib search records cover LeanSearch, LeanFinder/Loogle, source grep, and local search; Mathlib has only `AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt`, explicitly documented there as weaker than Stacks 02LN.

The blueprint/item was incomplete only in having no proof. No statement error or route departure was found.

## Unfinished

Nothing.

## Review by E1

I read More on Morphisms Lemmas 02LN and 02LL, together with the cited finite/proper and fibre-product point statements. The item's locally finite type, separated, and pairwise distinct isolated-fibre-point hypotheses match 02LN. Step 1 uses exactly the 02LL elementary neighbourhood and finite open pieces; for $n=0$, $U=S$ and $W=X$ make every clause vacuous. Step 2 applies separated base change and proper-over-separated to show each finite open piece is closed. Step 3 uses properness to make the pairwise-intersection images closed and removes only sets missing $u$; the cited persistence node guarantees the restricted pieces retain their singleton fibres and residue maps. Step 4 takes the clopen complement. Step 5 uses the fibre-product point node and $\kappa(u)=\kappa(s)$ to show there is only one point above each pair $(x_i,u)$, excluding a second point in $W$. These cited node statements supply every non-elementary assertion; no source tag substitutes for a node. I checked $n=0$ and one isolated point as edge cases. No new node, duplicate, cycle, route departure, or statement change occurs. The delivery contains only item and report files in one commit; no correction was sent back.
