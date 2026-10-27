# Q08: lem-sfb-space-acyclic-affinization-geometry

## Files written

All node paths are under dag/nodes/sec-six-functors-basics/ in this sandbox.

- lem-sfb-space-acyclic-affinization-geometry.json: statement; split into seven steps following Stacks 07V4 and 07V5. Mathematical statement retained; corrected doubled TeX escapes in the inherited statement.
- lem-sfb-space-affine-target-global-functions.json: statement-only, unsplit; no Mathlib match for algebraic spaces (05Z1).
- lem-sfb-space-h1-vanishing-affine-base-change.json: statement-only, unsplit; no Mathlib match for algebraic-space quasi-coherent cohomology (07V0, 073B).
- lem-sfb-space-h1-separate-disjoint-closed.json: statement-only, unsplit; no Mathlib match (07V1).
- lem-sfb-space-integral-universally-closed.json: statement-only, unsplit; no Mathlib match for arbitrary algebraic spaces (0415).

The sandbox also contains citations.json, the original searches.jsonl, search-results.json and integral-search-results.json. Existing searches and their results were retained and read on resumption. Four new nodes, zero Mathlib leaves.

## Attachments

None. Searched the live read clone lean/WeilConjectures/ for the exact blueprint tag and affinization, vanishing/separatedness and algebraic-space terminology. The hits about derived global sections concern schemes and do not state this item. The algebraic-space statements have no completed project declaration found by these searches. No Lean was written or compiled.

## Literature

No WANTED documents. Read literature/stacks-project/spaces-cohomology.tex, Situation 07UY and Lemmas 07V0, 07V1, 07V4, 07V5, including their proofs. For the four new nodes read spaces-properties.tex 05Z1; spaces-cohomology.tex 07V0 and 07V1; spaces-morphisms.tex 073B and 0415. Also read spaces-morphisms.tex 05Z2, especially the absolute separation clause (2) and its diagonal argument. Verified the tag-to-label mappings in tags/tags.

The new-node arguments, reserved for their later splits, are the source arguments: 05Z1 descends compatible scheme morphisms along a presentation; 07V0 uses affine higher-direct-image vanishing and Leray, then the computation of global sections of a tensor module; 07V1 uses the quasi-coherent kernel of the surjection to the two disjoint reduced closed subspaces and lifts (0,1); 0415 tests the integral/affine/universally-closed conditions on affine scheme charts. These arguments are recorded here, not inside the statement-only node files.

## Corrections and scope

The imported mathematical assertion agrees with 07V4 and 07V5. No STATEMENT-DISPUTED issue was found. The only statement edit removes doubled backslashes, without changing its hypotheses or conclusion. There are no new target statements or Lean edits.

On resumption the earlier sandbox had an overlapping relative integral-surjection separation lemma. Removed it in favor of the existing absolute lemma lem-sfb-space-uc-surjection-separation and the missing input 0415. The item now deduces the relative diagonal directly by a Cartesian-square argument on scheme tests. Refreshed the citation of lem-sfb-space-change-base-to-integers against its current, expanded statement. All other previous proof arguments and search evidence were retained.

Read the chapter and unit records, SETUP's three levels, and the latest blueprint's sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). This downstream geometric prerequisite follows the recorded Serre-affineness branch of the existing alteration reduction; it changes no chapter or unit route. The inherited ancestor chain has blueprint.from.node = null, as confirmed by tools/blueprint_refs.py ancestor; retained that provenance and its exact latest-blueprint proof place instead of inventing an imported ancestor. The item is not the unit's key statement, so no unit realization fields are changed.

## Not duplicates

lem-sfb-space-affine-target-global-functions vs lem-sfb-space-acyclic-affinization-geometry: the new node is the full Hom-to-affine/global-ring-map bijection for arbitrary algebraic spaces and arbitrary affine targets, with no qcqs or cohomological assumptions. The item needs its identity-map specialization to construct p; the nontrivial geometry of p is proved in subsequent steps.

lem-sfb-space-h1-vanishing-affine-base-change vs lem-sfb-space-acyclic-affinization-geometry: 07V0 transports H1 vanishing along arbitrary affine maps and computes functions under every affine scalar extension. It asserts neither separatedness nor universal injectivity of p, the conclusions proved here.

lem-sfb-space-h1-vanishing-affine-base-change vs lem-sfb-space-serre-affineness: the latter is the upstream goal that a cohomologically acyclic space is affine and depends on this item; citing it would be circular. The new node is the independent preliminary 07V0, used in the source's proof before affineness is established.

lem-sfb-space-h1-vanishing-affine-base-change vs lem-sfb-space-qcqs-source-products: the existing node gives quasi-separatedness and qcqs fibre products, not preservation of H1 vanishing or the prescribed global ring after nonflat scalar extension.

lem-sfb-space-h1-vanishing-affine-base-change vs lem-sfb-space-integral-qcqs-permanence: the existing node gives integral-map and qcqs permanence, with no cohomological or global-function computation; the new lemma concerns arbitrary affine maps, not just integral ones.

lem-sfb-space-h1-vanishing-affine-base-change vs lem-sfb-fp-etale-presentation-criterion: the latter characterizes finite presentation using a scheme atlas and relation, without any H1 or global-ring conclusion.

lem-sfb-space-h1-vanishing-affine-base-change vs lem-sfb-qcqs-space-fibre-product: the latter only gives qcqs permanence of fibre products; it does not compute their sections or cohomology.

lem-sfb-space-h1-vanishing-affine-base-change vs lem-sfb-space-qcqs-permanence: the latter gives quasi-compactness and quasi-separatedness of maps, without the new cohomological computation.

lem-sfb-space-h1-separate-disjoint-closed vs lem-sfb-space-acyclic-affinization-geometry: the new node separates arbitrary disjoint closed subsets by values 0 and 1; it does not state any conclusion about p. The item applies it to two closed rational points and supplies the contradiction using the identified K-algebra of functions.

lem-sfb-space-h1-separate-disjoint-closed vs lem-sfb-space-serre-affineness: 07V1 is a preliminary closed-subset separation lemma in the proof of the upstream Serre theorem; the affineness goal cannot be cited downward without a cycle.

lem-sfb-space-integral-universally-closed vs lem-sfb-integral-stack-closed-point-topology: the existing node assumes a finite-type stack over a field with quasi-compact separated diagonal, and gives closedness of that one map and closedness above closed points. It does not give arbitrary algebraic-space base change of an integral map over an arbitrary base.

lem-sfb-space-integral-universally-closed vs lem-sfb-finite-space-morphism-topology: the existing node assumes finiteness and concludes finite fibres and local quasi-finiteness. Here the integral scheme cover need not be finite; arbitrary integral maps have the universal closedness supplied by 0415.

The blueprint tag searches 05Z1, 07V0, 07V1, 05Z2 and 0415 found no imported matching node. Concept searches also distinguished the scheme-only pqf-lem-integral-univclosed (01WM), which cannot be specialized to arbitrary algebraic spaces. The existing lem-sfb-space-uc-surjection-separation is reused, not recreated; the discarded relative variant is absent from the delivery.

## Review by Q08

I checked the item against the proofs of 07V4 and 07V5, and each new node against the source listed above. I opened every node cited by a proof step and read its statement. The argument uses those statements, not constructions hidden in their proofs.

Step 1 uses the current change-of-base node's explicit identification of small etale ringed sites. This preserves the module category, global sections and H1 hypothesis; the same charts preserve the point topology. The affine-target node states the entire bijection needed for existence and uniqueness, and its source specifically works over the integers. The homomorphism used is the identity of A.

Step 2 uses both clauses of the new affine-base-change node: affine pullback preserves H1 vanishing, and the structural ring map identifies functions with the given algebra. Its added qcqs/relative-diagonal permanence is the 073B permanence input accompanying 07V0. No flatness of A to K is assumed or used. In step 3 the rational-point node explicitly requires only a quasi-compact diagonal over K, supplied by step 2, and explicitly gives both closedness and injectivity of rational-point images. The 07V1 node gives the function taking values 0 and 1 on the two closed singletons. Evaluation is a K-algebra map K to K, hence the identity, so these values contradict one another. The stack universal-injectivity criterion is used only in its algebraically closed field formulation: algebraic spaces have discrete groupoids, and the equality just proved supplies its required lift of the identity isomorphism. This yields every algebraic-space base change in the item's conclusion, not merely injectivity on one field's points. This is the same field-point route as 07V4, avoiding a redundant large-field-surjectivity lemma.

Step 4's existing scheme-cover node asserts surjective integral, without requiring finite type or a Noetherian base. The integral-permanence node asserts affineness and qcqs of the source. Clause (1) of 07V0 then supplies exactly the etale H1 vanishing on Y. Step 5 uses the Zariski/etale quasi-coherent equivalence to put each Zariski ideal into the correct module category, then the explicitly stated degree-one cohomology comparison. The scheme Serre node requires only quasi-compactness and vanishing for quasi-coherent ideals; both have been checked. No separatedness of Y is assumed before applying that criterion.

Step 6 applies the existing affine-source separatedness theorem to Y over Spec Z. New 0415 supplies universal closedness of the integral surjection, and the existing 05Z2 node explicitly descends the absolute closed diagonal under that surjection. Step 7 is elementary: the relative diagonal is a base change of the absolute diagonal, and after composing any scheme test with the map of products its defining closed-immersion test is identical. Thus no general relative separation-descent node, immersion criterion or unproved closed-image inference is hidden there.

I tested the new statements on X empty (A the zero ring), A' the zero ring, arbitrary nonflat field maps A to K, coinciding or distinct rational points, and empty closed subsets. For 07V1 the empty-side cases admit the constant functions 0 or 1; for both empty there is no restriction. Integral maps include nonfinite affine integral maps, so no finite-fibre or finite-presentation conclusion was added. Surjectivity is required exactly at the separation-descent application, not in 0415. No lemma here assumes reducedness, finite type, excellence or a Noetherian base.

The saved semantic searches were read in full for the relevant candidates, and their results remain recorded verbatim. Read the Mathlib ΓSpec adjunctions in GammaSpecAdjunction.lean:333 and :399: their domains are locally ringed spaces and schemes, not fppf algebraic-space sheaves. Integral.of_comp at Integral.lean:86 and IsSeparated.of_comp at Separated.lean:256 cancel the first factor of a composite, and do not descend separatedness of its target. The integral universally-closed search likewise returns scheme declarations, not an atlas-topology assertion for algebraic spaces. None is an exact match or one-line specialization. No unrun search is recorded as evidence.

Checked B through E of delivery-errors against these files: new nodes have only statements and empty proofs; all objects and notions are introduced; citations.json copies actual statement text for all fifteen step/node pairs; no clause is merely renamed as a new node; the argument follows the source and retains every original conclusion. No step is longer than 2000 characters. Off-unit generic comparison and scheme-affineness tools are declared in split_report.tool_uses and do not replace the unit route. The required server checks and final delivery command are the remaining mechanical gates.

## Unfinished work

None within the one-level stage-1 split. The four unsplit inputs deliberately remain statement-only for future workers.
