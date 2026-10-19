# Stage-1 worker report

1. Files written:

- `dag/nodes/sec-purity-real-sheaves/lem-a1-quasi-affine-target-locality.json`: statement split, no new node; Mathlib searches retained from the imported target and all report no exact relative quasi-affine locality theorem.
- `citations.json`: verbatim statement excerpts for every cited node in every proof step.
- `report.md`: this report.

2. Attachments: none. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, its title, Tag 01SM, and the likely quasi-affine declarations; no sorry-free declaration states this item exactly.

3. WANTED: none.

4. I kept the imported statement and hypotheses exactly. The source is Stacks, Morphisms Tag 01SM. I checked the source proof and expanded its (1)⇒(2), (2)⇒(4), and (3)⇒(1) arguments. The proof uses no SGA source. The split creates no node: every auxiliary fact already has a DAG statement.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Review by Q14

I read the item, the `sk-p-real-rankin` unit, its chapter, the ancestor `lem-a1-affine-hc0`, and the Tag 01SM source proof. I also read the complete statements of every cited node. Step 1 is exactly the definition of a quasi-affine morphism. In step 2, the canonical-embedding node supplies quasi-compactness and quasi-separatedness of each local quasi-affine scheme; the qcqs permanence node supplies the restricted morphism properties; the affine-scheme node supplies quasi-separatedness of each affine target; and the target-local quasi-compactness node is applied first to `h` and then to its diagonal. I explicitly checked that the opens `Z_a ×_{S_a} Z_a` cover `Z ×_S Z` and that the restricted diagonal is the diagonal of `h|_{Z_a}`; the quasi-separated definition then gives global quasi-separatedness. The empty-cover case is stated separately.

In step 3, I checked that the already-established qcqs hypotheses are exactly those required by pushforward quasi-coherence, and that the relative-spectrum node supplies the affine morphism, algebra isomorphism, and affine chart identifications. In step 4, the affine-algebra local-maps node is used with `α⁻¹`, its overlap agreement is exactly its statement, and the scheme-morphism gluing node supplies the global map. On each affine chart the induced section map is `α_a⁻¹ α_a = id`, so the morphism-into-affine node identifies it with the canonical quasi-affine embedding. In step 5, that canonical embedding is an open immersion; the local-source criterion applies after checking pointwise injectivity, and the affine-target qcqs statements plus target-local quasi-compactness give that the global open immersion is quasi-compact. Step 6 then checks each affine target open using the relative-spectrum affine chart and the definition of quasi-affineness.

I checked small cases: an empty base (forcing an empty source), a one-member affine cover, and an identity morphism of an affine scheme. No statement or dependency was changed, no new node was introduced, and no cycle is present.
