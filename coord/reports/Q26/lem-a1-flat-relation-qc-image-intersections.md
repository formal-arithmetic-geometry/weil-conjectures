# Worker report: lem-a1-flat-relation-qc-image-intersections

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-flat-relation-qc-image-intersections.json: statement node, split, no exact Mathlib match. The five-step proof has 2933 characters and uses existing nodes only.
- citations.json: one verbatim statement quotation for every node used by every proof step.
- searches.jsonl: actual msearch.py results; preserved as the search audit.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None for the complete item. Searched the whole project WeilConjectures tree for the exact blueprint tag and for flat relation/image/intersection terminology. There is no project declaration stating every clause. The existing Topology.generalizations_isCompact_sInter_isCompactOpen in lean/WeilConjectures/Topology/SpectralGeneralizations.lean is an input belonging to lem-weil-pbc-spectral-generalizations-of-quasi-compact, not an attachment for this item. Its complete statement and proof were read, without compiling.

## WANTED

None.

## Findings and changes

The live item was unsplit, with no saved sandbox node, report, or search log on continuation. No earlier deliver.py process for Q26 and this item was active. No released repair note or return entry for this item was found. Copied the live item into the authorized sandbox, kept its entire statement, source, statement dependencies, blueprint provenance and old search records, and added the proof and actual fresh searches.

Stacks groupoids.tex Tag 0APA, lemma-first-observation, assumes a groupoid, but its displayed proof uses only the underlying maps. Its proof establishes all the additional intermediate clauses recorded in the item. Flatness of s and quasi-compactness of t are retained as hypotheses, although this argument only needs quasi-compactness of s and flatness of t. This is faithful to the source and does not strengthen its hypotheses. The conclusion is not that the image is open: no finite-presentation hypothesis is assumed.

Searched the full DAG and imported blueprint by quasi-compact opens, generalization, flatness and 0APA. The existing compact-image, flat-generalization-lifting, affine-basis, affine-qcqs, affine-cover quasi-separatedness, qcqs-spectral and spectral-generalization nodes suffice. No auxiliary claim was turned into a new node. The unit sk-p-real-rankin and chapter records were read; their key statements and routes are not edited. This node inherits the established chain from the Gabber descent argument below lem-a1-affine-hc0; its split simply expands the 0APA ingredient already on that route.

Mathlib searches ran with msearch.py: LeanFinder for the full relation-image assertion, LeanSearch for compact generalization-stable subsets, Loogle for QuasiCompact and IsCompact, grep for compact preimages/generalizing maps/interpolation, and a second LeanFinder phrasing for the general topological intersection assertion. All services answered. Read the hits and relevant source: QuasiCompact.isCompact_preimage is the preimage ingredient, Flat.generalizingMap is the lifting ingredient, PrespectralSpace.exists_isCompact_and_isOpen_between gives interpolation, and stableUnderGeneralization_iff_exists_sInter_eq gives arbitrary open intersections. They do not give the complete item by one-line specialization. The already-existing spectral theorem is reused rather than recreated.

## Not duplicates

No new nodes were created. In particular, the more general spectral-generalizations theorem already exists and is cited, not restated as a new node. The separate qc-open-intersection-spectral-presentation node treats the inverse-limit presentation of a given family, not the flat-image construction needed here, and is not needed by this proof.

## Review by Q26

I read groupoids.tex Tag 0APA (lemma-first-observation) in full, including its proof, and the cited topology.tex Tag 0A31 (lemma-make-spectral-space) and morphisms.tex Tag 03HV (lemma-generalizations-lift-flat). I also read schemes.tex Tag 01IT (lemma-basis-affine-opens), Tag 01KO (lemma-characterize-quasi-separated), properties.tex (lemma-quasi-compact-quasi-separated-spectral), and topology.tex Tag 04Z9 (lemma-image-quasi-compact). These match the item without requiring any groupoid identities. There are no new-node statements to compare with sources.

Step 1 uses lem-weil-pbc-affine-opens-basis for affine opens contained in H, def-weil-finite-type-morphism for the quasi-compact inverse image of each affine open, and lem-weil-pbc-continuous-image-quasi-compact for the image of the restricted continuous map. Each quoted statement was opened and read. The affine-only definition is sufficient: the proof explicitly takes a finite affine cover of H and combines finite subcovers of its inverse images. Thus it does not silently use a stronger definition of quasi-compact morphism or a further unrecorded lemma. The topology on A is the subspace topology, as required by the continuous-image node. Continuity of scheme maps is part of their definition.

Step 2 cites lem-weil-pbc-flat-generalizations-lift for exactly the lifting of the generalization y-prime of t(r) to a generalization r-prime of r. I checked the direction against the closure condition in the item and against Flat.generalizingMap. Flatness is available for t. The rest is written out using the definition of closure: an open neighbourhood A of r meets the singleton of r-prime. No claim about arbitrary flat maps being open is made.

Step 3 uses the affine-basis node and the quasi-compactness clause of lem-weil-pbc-affine-scheme-qcqs. It is marked elementary because, after those supplied statements, the only work is a finite subcover of E and the written-out finite-union argument. No separate containing-neighbourhood lemma is hidden. The empty family is permitted when E is empty, yielding the empty open.

Step 4 uses the affine-basis node to cover the arbitrary chosen H_2. Its affine opens are also affine opens of V with the identical restricted structure sheaf. Both implications of lem-weil-pbc-quasi-separated-affine-cover-criterion are present in that node's statement: apply the first to V and the second to the affine cover of H_2. Thus quasi-separatedness of H_2 is proved, not assumed. Lem-weil-pbc-qcqs-scheme-spectral then applies with both quasi-compactness and quasi-separatedness available. Restricting the ambient space from V to H_2 leaves the induced topology on E unchanged, so its compactness hypothesis is satisfied.

Step 5 uses the full intersection clause of lem-weil-pbc-spectral-generalizations-of-quasi-compact. The node states exactly the set W defined by closure meeting E, and its equality with the intersection of all compact opens containing E. The proof verifies W=E in H_2 from step 2, instead of assuming the desired intersection statement. I checked the relative closure implication to closure in V and the equality of induced topologies. The family is a set of subsets and contains H_2; therefore the ambient intersection in V contains no extraneous points outside H_2. Each relative open is open in V, and quasi-compactness is intrinsic to its subspace topology. This covers every clause of the item.

Hypotheses and small cases checked: H empty and R empty both give E empty; choose H_2 empty or any compact open, and the family then contains the empty open, so its intersection is empty. If V is not quasi-compact, only H_2 is made spectral; V is never incorrectly assumed spectral. When H_2 is empty, it is still a qcqs scheme and the family has its single empty member. In a two-point valuation spectrum, the generalization direction lifts from a closed point towards the generic point, consistent with the item's closure formula. Non-separated quasi-separated schemes cause no issue: no intersection of affine opens is asserted affine. No equivalence, reflexivity, transitivity, symmetry or invariant-open property of s,t is used.

I checked B–E against the actual files. There are no new-node form or duplicate problems (B1–B9), no attachment closing the complete item (B10), and no hidden citation or proof-only access to a node (C1/C3/C4). Every uses entry has an exact statement quotation in citations.json. The only off-unit non-Mathlib topological theorem is explicitly declared in split_report.tool_uses as a generic tool, rather than changing the unit route. All five steps are below 2000 characters; the assembly is below 3000 characters. No clause was moved to a new node (D1/D2). Nothing in the statement required correction or a STATEMENT-DISPUTED marker. The finite-affine cover argument and relative/ambient intersection bookkeeping are the concrete details added during this review.

## Unfinished work

No mathematical gap remains in this stage-1 split. New nodes, Lean work and compilation are outside this delivery. The required delivery dry run and final push follow this report; their terminal outcomes are reported by the delivery command.
