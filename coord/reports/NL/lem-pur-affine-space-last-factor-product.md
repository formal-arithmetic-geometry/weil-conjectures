## Worker report

1. Files written: `dag/nodes/sec-smooth-purity/lem-pur-affine-space-last-factor-product.json` (statement, split; not in Mathlib). No new nodes and no Mathlib leaves. `citations.json` records a verbatim statement passage for every citation in every proof step. Existing statement, statement dependencies, source, creation metadata and blueprint ancestry are retained. The item is not the unit's key node, so no unit record is changed.
2. Attachments: none. Searched `lean/WeilConjectures/` for the exact blueprint id and for last-factor/last-coordinate, affine-space product, Kunneth and projection-formula terminology. There is no project declaration stating this comparison.
3. WANTED: none.
4. The unsplit item already includes the concrete forward-product symmetry and the domain/invertibility hypotheses needed to finish it. Its distinction between a supplied binary construction and a theorem requiring an abstract six-functor datum must be respected. I used only the stipulated construction from `thm-sf-kunneth-relative`, not that theorem's conclusion under absent datum hypotheses. No statement error was found and no statement was changed.
5. Unfinished work: none in the assigned one-level split. Delivery validation is performed with the required server dry run.

## Proof and source reading

I read the `sk-prop-an` chapter and unit records, the current main-20261015 unit text, and the older detailed ancestor `prop-pur-affine-space-composition-law.md`, especially Proof Steps 3--4. The current unit's Step 6 is the ordered affine-line induction; this item supplies its binary-product identification before any integration map is evaluated. The detailed source's shorthand about even shifts is not a proof of equality of the two concrete products. The existing `lem-pur-finite-forward-product-symmetry` supplies exactly that missing non-elementary equality. I read its statement, including the displayed definition of Xi, the definition of S and the retained bounded-below etale-origin domain conditions.

I also read the actual binary inverse construction in the blueprint `thm-sf-kunneth-relative.md` and its current DAG statement, and the current main-20261015 `lem-sf-kunneth-coherence.proof.md` symmetry paragraph. The latter motivates the symmetry comparison, but I do not use its abbreviated proper reduction as a proved black box. I read Stacks `sites-cohomology.tex`, Tag 0E48, label `remark-compatible-with-diagram`, including the omitted-verification notice: it concerns the ordinary ringed-topos projection/base-change diagram, not literally this compact-support conclusion. No claim in this split attributes compact-support symmetry directly to that tag. No SGA source is used.

## Review by NL

I checked delivery-errors B--E against the node and the sources. There are no new statement-only nodes, definitions, search claims or Mathlib attachments to audit. The imported item is preserved verbatim. The proof has five steps and none exceeds 2000 characters; its elementary steps are explicit expansions and cancellation calculations, rather than concealed geometric or homological comparison lemmas.

Step 1 uses the statement of `prop-weil-twist-preserves`, which says the finite Tate twists are locally constant rank-one sheaves, and clause (ii) of `lem-sf-proetale-constructible-origin`, which supplies etale-origin models of bounded constructible complexes. A shift has one nonzero cohomology sheaf here; a rank-one sheaf over the finite ring A has finite stalks, so these inputs are bounded constructible. The field and finite coefficient hypotheses of both statements are precisely those of the item. I separately checked that all remaining tensor-domain hypotheses of the forward symmetry are assumptions of this item, not consequences I have silently inferred from finite Tor amplitude. The separated finite-type hypotheses are likewise given. The quotation for the site-comparison lemma is its full clause (ii), not merely its equivalence for individual sheaves.

Step 2 reads the explicit inverse construction in `thm-sf-kunneth-relative` and the explicit forward composite in `lem-pur-finite-forward-product-symmetry`. Reversing the former's factors gives exactly the latter's displayed Xi. This only identifies the stipulated map: it does not invoke the relative-product theorem with a missing abstract datum. All four specified PF maps, both exchanges and the composition comparisons are invertible by the item's hypotheses. The two quoted statement passages actually give these constructions.

Step 3 uses the conclusion Xi = S Xi_swapped sigma in the existing forward-product symmetry, with precisely the objects checked in Step 1. The same underlying pullback with its legs interchanged can be chosen as the swapped pullback: its universal property exchanges the two equations and nothing else. Therefore the scheme part of S is the identity on this model, while its tensor part remains the signed symmetry. The identity-normalization clause in `thm-sf-comp-composition` removes identity composition comparisons. This use does not assert that an affine-space purity comparison is permutation invariant.

Step 4 substitutes the entire forward composite of the same symmetry node, with f and g exchanged. I checked each factor's type: E is Lp*U to Rq!R; C is W tensor M to Rq!(R tensor Q); P_U starts at V_m tensor U. The naturality in `thm-sf-comp-composition` is exactly what moves R(pq)!(sigma) across alpha. The remaining identity is signed symmetry naturality for E, written explicitly. Double symmetry is checked by multiplying the two Koszul signs; it is not the false claim that a single symmetry on an arbitrary derived tensor is the identity.

Step 5 calculates both inverse pairs for B and Pi. In particular the first factor of B is Rq!(sigma_R,Q), so its inverse is Rq!(sigma_Q,R), with the correct order. `lem-weil-derived-tensor-functorial` states that tensor carries identities and composites to identities and composites, which is precisely what is needed to tensor the inverse pair E,E^-1. Ordinary direct-image functors have the same functorial inverse-pair calculation. Reversing the four final factors gives the exact formula in the item. No naturality of projection formulas, coefficient-passage comparison, exceptional adjunction, trace normalization or purity theorem is used implicitly.

I tested the common-pullback construction for m=1, for an empty base Y, and for disconnected bases. The calculation uses no chosen basis or division and still consists of inverse pairs in those cases. It keeps the signs rather than using a parity argument, so it introduces no failure at ell=2. Invertibility is only used where explicitly assumed. Every non-elementary dependency is cited by its statement; citations.json was checked by substring membership before writing. There are no cycles introduced through new statements or through the parent trace-factorization node, which is not a proof dependency.

## Searches and reuse

The original item's five search records were read and retained. New logged searches asked specifically for the inverse compact-support product through the other projection, with a second semantic phrasing. Loogle `"Kunneth"` and the recorded AlgebraicGeometry grep found no hits. LeanFinder returned topological products, continuous alternating maps, condensed internal-Hom and ordinary sheaf pullback comparisons; LeanSearch returned pullback symmetry projection identities. Their returned signatures do not state a compact-support derived-sheaf product comparison. All new queries are exactly those in searches.jsonl; none is invented or marked unavailable when it succeeded.

Whole-DAG and blueprint searches for Kunneth, last-coordinate, product symmetry, forward products and opposite projections found the existing generic forward-product symmetry and construction, which are reused. No blueprint node states this exact last-factor inverse formula. No new node or same-tag duplicate is introduced.

## Tool uses

`thm-sf-kunneth-relative` is referenced solely for the construction specified by the item, with no invocation of its abstract-datum theorem. `lem-sf-proetale-constructible-origin` and `lem-weil-derived-tensor-functorial` supply generic site-comparison and tensor-functor tools. These uses are declared in split_report.tool_uses. They leave the affine-space unit's ordered-integration route intact.

## Not duplicates

No new nodes.
