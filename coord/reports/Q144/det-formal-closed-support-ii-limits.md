# Worker report

1. Files written: `dag/nodes/sec-six-functors-basics/det-formal-closed-support-ii-limits.json` (statement, split proof; no new nodes); `citations.json`; this report. The item uses the existing Mathlib search record and has no new Mathlib leaves.
2. Attachments: none. No sorry-free declaration under `WeilConjectures/` states this item exactly; the source search found only the closed-immersion support declarations, so this is not an attachment.
3. WANTED: none.
4. The imported item already contained the reviewed eight-step proof and the corrected Roos-triangle formulation, but its status remained `unsplit`. I retained its statement, dependencies, proof, blueprint metadata, tool-use declarations, and reviewed record, and changed only the stage-1 status to `split`. The proof follows the blueprint route: coefficient compatibility and immersion inverse images; the sheaf-level kernel support construction; K-injective products for right derived functors; triangulatedness and fibers; finite locally free tensor exactness and derived-tensor identification; the local finite-coordinate product calculation; derived products; and the explicit Roos shift calculation. No node was created because every cited lemma already exists in the DAG. The existing reviewed correction adds `lem-sfb-derived-monoidal` in step 5 so the stated derived tensor is identified with the K-flat model. The item’s reviewed note also records the correction from an unjustified canonical derived-limit map to preservation of Roos triangles and invertibility of completing comparisons.

## Review by Q144

I read the item node, its source blueprint statement and proof at `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-formal-closed-support-ii/`, the unit `sk-lem-formal-closed-support-ii`, and the chapter record. I also opened the statement of every cited node and recorded a verbatim quote for each use in `citations.json`; thus each proof step relies only on what its cited node states.

Step 1 uses the Cartesian coefficient-isomorphism proposition, the pro-étale immersion inverse-image limit lemma, exact-functor derived triangulatedness, and the termwise derived-product result. Their hypotheses apply to the three immersions and the fixed coefficient system, and they give additivity, triangulatedness, products, and limits for `j^*`, `u^*`, and `i^*`.

Step 2 uses the module upper/lower adjunction, right-adjoints-preserve-limits, the closed-support construction, and sectionwise module limits. I checked that `j_*` is the right adjoint in the cited statement, that the unit is the one defining `G`, and that the product kernel and finite-limit argument use only the sectionwise kernel statement plus exactness of `i^*`.

Step 3 uses existence of K-injective resolutions, sectionwise products, products of K-injectives, the definition of the total right derived functor, and the termwise derived-product node. I checked the argument for arbitrary small families, including the empty product, and that the K-injective product represents the source product before applying `Rj_*` or `RG`.

Step 4 uses K-injective existence, triangulatedness of total right derived functors, and the closed-support identification. I checked that the composite with `u^*` inherits products and fibers and that the support functor is exactly `RG`, rather than an unmentioned alternate construction.

Step 5 uses finite-free tensor exactness, the tensor-Hom adjunction, left-adjoint finite-colimit preservation, exact-functor derived triangulatedness, the K-flat definition, tensor descent, the stated derived-tensor definition, and `lem-sfb-derived-monoidal`. I checked the finite locally free hypothesis, the K-flat replacement, and the additional monoidal node that identifies the statement’s bifunctor with the exact termwise tensor functor.

Step 6 uses the localized ringed-site definition, sectionwise limits, and the sheaf tensor definition. I checked the local trivialization calculation for rank zero, rank one, varying finite ranks, empty families, and overlap gluing; it proves the product comparison without assuming a uniform rank or global freeness.

Step 7 uses the termwise derived-product statement. The tensor comparison is induced by the same projections, so it gives all small derived products after step 5 and the local calculation.

Step 8 uses derived products, Roos-triangle existence, the derived-limit definition, triangulated-category axioms, and the triangle-morphism isomorphism criterion. I checked the convention `pr_n s = t_n pr_{n+1}`, the coordinatewise shift identity, the induced `1-s` map, and the TR3 comparison; the conclusion is preservation of Roos triangles and invertibility of every completing comparison, without claiming a canonical cone choice.

I checked the edge cases recorded by the prior review: empty products, rank zero and zero tensors, empty support/open complement, identity immersions, empty schemes, zero towers, and arbitrary unbounded complexes. No hypotheses were added or dropped, no SGA source is used, and no new node duplicates an existing DAG statement. The source search in both the slopmaster2 project and the upstream reference found no exact finished declaration for this item.
