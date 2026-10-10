# Stage-1 repair report: lem-sc-hom-etale-locus-translation

1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-hom-etale-locus-translation.json`: generalized statement and repaired proof.
- `lem-sc-etale-base-change-geometric.json`: statement-only node for pointwise etale base change.
- `lem-sc-etale-locus-open.json`: statement-only node for openness of the etale locus.
- `citations.json`: verbatim statement quotes for every proof citation.

2. Attachments: none.

3. WANTED: `literature/stacks-project/groupoids.tex`, Tag 0BFH proof of translation invariance, because the checkout contains only citation metadata and not the source file.

4. The returned version incorrectly narrowed the theorem to an algebraically closed field. The item is now over an arbitrary field; step 2 base changes to an algebraic closure and uses pointwise descent, openness, and Jacobson density. The former transport node was elementary and has been removed; its composition argument is folded into step 1.

5. I could not attach a Lean declaration: no project declaration carries the item tag or states this result.

## Not duplicates

lem-sc-etale-transport-by-isomorphism vs lem-sc-mult-n-etale-kernel: the new node is a general pointwise scheme lemma for any morphism and any commuting pair of isomorphisms, whereas the existing node is the abelian-variety multiplication-by-d statement and only cites translation invariance as one proof step.

## Review by E1

I searched both project source checkouts for the item tag and translation terminology and found no closed declaration. I read the multiplication-by-n proof and `lem-sc-translation-automorphism`. Step 1 uses only the cited translation definition and theorem; the commuting square and transport of etaleness through isomorphisms are elementary, so the deleted transport node is not needed. Step 2 cites the new geometric base-change node, the existing closed-point definition and Jacobson-density leaf, and the new etale-locus-openness node; each statement supplies exactly the fact used. I checked that after base change to kbar, closed points are kbar-points and translations are transitive on them, while descent returns the conclusion to k. Mathlib searches were run for both new nodes with LeanFinder, Loogle, and grep, with unavailable or nonmatching results recorded in their JSON.

## Repair review by E1

- Item statement: restored arbitrary-field hypotheses, as required by the consumer `lem-sc-mult-n-etale-kernel`.
- Step 1: folded the elementary isomorphism-transport calculation into the step and removed `lem-sc-etale-transport-by-isomorphism`.
- Step 2: added the algebraic-closure reduction and citations for pointwise base change, etale-locus openness, closed-point identification, and Jacobson density.
- The return's four points are repaired: no narrowing, no uncited openness or density, explicit closed-point interpretation, and no separate elementary node.

## Not duplicates

lem-sc-etale-base-change-geometric vs def-sbc-smooth-morphisms: the existing node defines smooth and etale morphisms via formal smoothness; it does not state pointwise preservation/reflection under field extension.
lem-sc-etale-base-change-geometric vs sbc-lem-affine-space-smooth: the existing node concerns smoothness of affine space, not pointwise etaleness after base change.
lem-sc-etale-base-change-geometric vs sbc-lem-smooth-criterion: the existing node is a smoothness criterion, not etale descent over a field extension.
lem-sc-etale-base-change-geometric vs lem-pc-proper-base-change: proper base change is unrelated to pointwise etale descent.
lem-sc-etale-base-change-geometric vs lem-weil-pbc-smooth-ring-map-iff-smooth-affine: the existing node treats affine smooth ring maps, not scheme etale points under algebraic closure.
lem-sc-etale-base-change-geometric vs lem-weil-pbc-smooth-zero-differentials-affine-open-etale: the existing node is an affine differential criterion, not arbitrary pointwise field-extension reflection.
lem-sc-etale-base-change-geometric vs lem-weil-pbc-etale-smooth-zero-dimensional-fibres: the existing node characterizes etale morphisms by smooth fibres, not base-change equivalence at points.
lem-sc-etale-base-change-geometric vs lem-weil-pbc-smooth-locally-standard-smooth: the existing node concerns local standard smooth presentations, not pointwise etale descent.
lem-sc-etale-base-change-geometric vs lem-weil-pbc-smooth-restrict-open-subschemes: restriction to opens differs from field-extension base change.
lem-sc-etale-base-change-geometric vs lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension: differential rank criteria differ from pointwise base-change reflection.
lem-sc-etale-base-change-geometric vs lem-weil-pbc-smooth-coproduct: coproduct smoothness does not state etale base-change reflection.
lem-sc-etale-locus-open vs lem-weil-pbc-etale-base-change-finite-limits: finite limits of etale sites do not state openness of the etale locus.
lem-sc-etale-locus-open vs lem-weil-pbc-etale-composition-cancellation: etale composition/cancellation differs from openness of the locus where a morphism is etale.

## Second reading by E1

- Item statement: checked against the blueprint consumer and Stacks Tag 0BFH's translation argument; arbitrary-field hypotheses and the group-homomorphism formulation are retained.
- Step 1: checked against `lem-sc-translation-automorphism` and the translation definition; the commuting-square transport is elementary and explicitly given by composition with inverse translations.
- Step 2: checked against the pointwise field-extension statement and the residue-field algebraic-closure argument; every point is reduced to the identity without assuming local finite presentation, openness, or Jacobson density.
- `lem-sc-etale-base-change-geometric`: checked against Stacks Tags 02H5 and 02H6; self-contained pointwise preservation and reflection statement, with searches recorded.
- Removed `lem-sc-etale-locus-open`: its local-finite-presentation hypothesis was not available for an arbitrary target group scheme, and the repaired proof no longer needs it.
- Citations: removed the obsolete closed-point, openness, and Jacobson-density citations; the remaining quotes match the cited node statements verbatim.

Changes made: replaced the invalid openness/density reduction by a residue-field algebraic-closure and translation argument, deleted the unused openness node, and repaired `citations.json` to match the proof.
