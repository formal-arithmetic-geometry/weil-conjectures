Files written:
- `dag/nodes/sec-six-functors/det-proper-image-localizing-open.json` — existing statement node, completed as a five-step split; no new nodes and no Mathlib leaves.
- `citations.json` — verbatim statement quotes for every proof-step citation.

Attachments: none.  The slopmaster2 source has
`AlgebraicGeometry.Etale.constructibleTorAmplitudeIn_rightDerivedLowerShriek` (OpenImmersion.lean:175), but it treats only a finite coefficient ring and a bounded finite-Tor object, so it does not state this item's all-coefficient localizing conclusion.

WANTED: none.

The imported proof had omitted the standing scheme and ambient module-object conventions and had an unsupported assertion identifying all integral stages with bounded constructible complexes.  The split records the standing separated finite-type setting explicitly, works in the ordinary unbounded module-object derived categories, and proves the Tor interval uniformly by the projection formula and exact inverse image.  No target statement was changed.

## Review by Q125

I read the item and its source proof at `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-lem-sf-open-ctf/sk-prop-proper-image-localizing-open.md` and its accompanying `.proof.md`, together with the unit record `dag/units/sk-lem-sf-open-ctf.json`.  I also read the relevant source declarations in `WeilConjectures/SixFunctors/Etale/Derived/Stability/OpenImmersion.lean` and `.../Derived/Finiteness/DirectImage.lean`.  The latter confirms the exact finite-coefficient open-immersion preservation theorem, while the former's theorem is narrower than this item; therefore I did not attach it.

Step 1 uses `sk-def-sfb-module-lower-shriek` for exactness and the sheaf-level adjunction, and `lem-sf-exact-functor-derived-triangulated` for passage to the unbounded derived functor.  I checked that the cited statements provide exactly those operations.  The displayed cohomology calculation then uses only exactness, kernels, images, and quotients, so it applies to unbounded complexes and preserves the vanishing interval.

Step 2 uses `sk-def-sfb-sheaf-tensor` for the strong monoidal sheafification and colimit preservation, `def-weil-pbc-internal-abelian-sheaf-module-equivalence` and `lem-weil-pbc-ring-sheaves-grothendieck` for the two module categories' Grothendieck structure, `lem-kun-grothendieck-derived-coproducts` for termwise coproducts in the unbounded derived categories, `sk-def-sfb-module-lower-shriek` for the adjunction, and `lem-weil-pbc-left-adjoint-preserves-colimits` for arbitrary coproduct preservation.  I checked the empty-index case and that no boundedness or constructibility hypothesis is used here.

Step 3 uses `sk-def-sfb-constructible` and `lem-sfb-dc-open-lower-shriek-preserves`.  I verified that the standing separated finite-type hypotheses match the cited preservation theorem and that the conclusion is bounded constructibility for the same coefficient ring.

Step 4 uses `sk-def-sfb-constructible` for the Tor interval, `sk-prop-sfb-cartesian-coefficients` for exact inverse image of the arbitrary test module, and `det-lem-int-tensor-projection` for the open-immersion projection formula.  I checked the specialization with closed part `id_X`, the identification of the identity direct and inverse images, and that the arbitrary test module is legitimately pulled back to U.  Exactness from step 1 then gives the same interval.  This is why the proof does not rely on the unsupported integral equality from the imported sketch.

Step 5 uses `det-proper-image-localizing-principle` and `sk-def-localizing-closure`.  I verified all hypotheses: the ambient categories have small sums (step 2), the derived extension functor is exact (step 1), it preserves sums (step 2), and it sends the constructible subcategory into the target constructible subcategory (steps 3–4).  The resulting restriction is therefore exact and sum-preserving on the stated full localizing closures.

I checked every cited node's statement against the corresponding step and recorded a verbatim quote for each citation in `citations.json`.  The item has no new statement node, so there are no duplicate or new-node Mathlib checks to add.  I tested the formulation against empty opens, identity opens, zero complexes, and finite coefficient rings; these agree with the stated conclusions.
