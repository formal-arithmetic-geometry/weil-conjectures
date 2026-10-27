## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-countable-finite-coordinate-images.json: existing statement, split in seven steps; not a Mathlib leaf. Statement and statement dependencies unchanged.
- citations.json: one verbatim statement quotation for each node used by each proof step.
- searches.jsonl: actual msearch.py searches and results, retained in the sandbox and incorporated into the item's mathlib_searches.

New nodes: 0. New Mathlib leaves: 0. The proof reuses two existing Mathlib leaves, lem-weil-pbc-continuous-image-quasi-compact and lem-sfb-compact-countable-separating-metrizable. No unit record is changed because this auxiliary is not the unit's key node.

## Attachments

None. Searched lean/WeilConjectures for the exact item tag and for metrizable/metrizability, diagonal image, profinite image and finite coordinate terminology. No declaration states the complete item. Mathlib constructors Profinite.pi, ProfiniteGrp.pi, and ProfiniteGrp.ofClosedSubgroup are useful individual ingredients, not a declaration of this complete diagonal-image construction with its specified normal kernels. The existing compact countably separating maps leaf supplies metrizability.

## WANTED

WANTED: an external human-written reference for the complete diagonal-image auxiliary lemma, for lem-sfb-countable-finite-coordinate-images. The inherited source already requests this. No document was downloaded. The delivery does not pretend the blueprint contains this proof: proof_origin.by is agent, the elementary arguments are written out, and the non-elementary facts use existing sourced nodes.

## What was wrong or incomplete

The original node had a complete correct statement but no proof. The latest blueprint's Paragraph (3) motivates ordinary direct-image preservation but contains no scalar tame-kernel topological proof. I read literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/{_section.md,sk-thm-sf-ctf-stability-direct-images.proof.md}, the recorded chapter and unit, and the parent lem-sfb-profinite-metric-function-quotients. This work supplies the topology needed by its diagonal-image step without changing the unit route or any target statement.

The existing ancestry chain is broken at lem-sfb-admissible-direct-image.created.item = Sheaf.SixFunctors.CtfStabilityDirectImages (a module name). tools/blueprint_refs.py ancestor reports None. I retained blueprint.from.node = null and the existing via chain, made the place precise and searched same_as. I did not invent a different created history. The recorded unit has chapter sec-six-functors and historical text, whereas this node and the current blueprint lie in sec-six-functors-basics; those maintainer-owned records are unchanged.

No mathematical statement dispute was found. In particular finite-coordinate surjectivity is not used. The node's source still refers to its original dated blueprint; each proof step and proof_origin identify the current reading or the precise elementary/Mathlib source.

## Unfinished work

None in this one-level split. No new unsplit node is introduced. The exact external reference requested above remains wanted; it does not leave a mathematical gap in the written agent proof.

## Not duplicates

No new nodes were created. Whole-DAG statement searches and tools/blueprint_refs.py searches for metrizable and profinite found the existing compact-separating-map, closed-finite-product-subgroup, profinite-clopen-basis and open-normal-subgroup results. The latter three do not state the complete item, and are unnecessary because the proof gives the finite-coordinate calculations directly. This avoids manufacturing nodes for elementary facts or clauses of the item.

## Review by Q139

I read delivery-errors.md B through E in full, including the mirrored copy, and checked the actual seven steps against those errors. I read the Stacks topology.tex opening induced-topology and Hausdorff conventions (Tag 004E), the product basis in section-limits (Tag 08ZS, opening paragraph), lemma-image-quasi-compact (Tag 04Z9, assertion (1) and its open-cover proof), and definition-topological-group (Tag 0B1Z), together with the nearby coordinate-product discussion. I read the pinned Mathlib Topology/Compactness/Compact.lean:974-975 and Topology/MetricSpace/PiNat.lean:1012,1063-1097. The latter's Encodable index, metric-target, compact-domain, continuity and point-separation hypotheses are exactly those checked in step 4. The actual online results were read: the discrete-space metrizable instance was also confirmed in pinned Topology/Metrizable/Basic.lean:205-208. No Lean was written or compiled.

Step 1 uses def-kun-subspace-topology, whose statement explicitly says opens are ambient opens intersected with the subset. Pulling these back gives the claimed continuity of corestrictions, while pulling basic product opens back gives finite intersections of coordinate-map preimages. Surjectivity is only onto the image. Step 2 uses lem-weil-pbc-continuous-image-quasi-compact, which explicitly states compactness of the image in the induced topology for a continuous map from a quasi-compact space. The source spaces are compact by the item, and step 1 has established continuity; the node does not need Hausdorffness or surjectivity, so no missing hypothesis is inserted.

Step 3 again uses precisely the subspace-topology definition. I checked the cylinder argument at each point: finitely many singleton-coordinate conditions refine an arbitrary product basic neighbourhood, each is clopen, and a coordinate on which two tuples differ gives disjoint neighbourhoods. The connected-subset consequence is justified by the cylinder/complement separation. These facts are direct consequences of the product and subspace definitions, not a hidden compact-space separation theorem. Step 4 uses lem-sfb-compact-countable-separating-metrizable, whose statement was opened and copied verbatim into citations.json. Compactness comes from step 2; the projections are continuous and separate points by step 3. The discrete metric is given explicitly with its triangle inequality, so no uncited metric-existence result is assumed. The lemma permits empty spaces and targets. I did not use the finite-index-only metrizableSpace_pi instance for a countable product.

Step 5 cites no lemma: the image is a subgroup because the original coordinate maps preserve identity, multiplication and inverse, and those identities are written down. I checked continuity on each singleton-coordinate cylinder using the explicit union of open rectangles for multiplication and the explicit singleton inverse image for inversion. Since these cylinders generate the topology already established in step 3, this is a complete elementary proof on the actual image topology, not an appeal to an unproved quotient-group topology theorem. Step 6 is also elementary: subgroup closure and conjugation are calculated coordinatewise, including the reverse conjugation inclusion, and the cylinder basis at identity is exactly the family K_F. General identity neighbourhoods contain an open neighbourhood by definition; no normal-basis theorem is silently invoked.

Step 7 uses def-weil-size-convention only for the already chosen ambient universes. It makes no stronger smallness claim than that convention. Equality is equality of tuples, so the fibre characterizations follow pointwise. I checked S empty, an empty A_n (forcing S empty), all singleton factors, constant and non-surjective coordinate maps, repeated coordinates and F empty. G and every finite group factor contain their identity, so the group image cannot be empty. None of the compactness, Hausdorff or metric arguments requires a chosen point of S_0. All seven steps are below 1000 characters, and none contains a hidden independent comparison lemma. Every non-elementary invocation is a cited existing node; citations.json contains its verbatim statement. There are no new-node source, hypothesis or duplication issues and no unreported corrections to the statement.
