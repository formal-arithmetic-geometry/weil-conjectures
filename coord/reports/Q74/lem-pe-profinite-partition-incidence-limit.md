# Q74: lem-pe-profinite-partition-incidence-limit

## Files written

- `dag/nodes/sec-proetale-coefficients/lem-pe-profinite-partition-incidence-limit.json`: statement, now split in seven steps; original statement, source, provenance and five inherited Mathlib searches retained. Five actual searches under Q74 added. No full Mathlib match.
- `citations.json`: six step/node pairs with verbatim statement quotations.
- `report.md`: this report.
- `searches.jsonl`: the required search command's own log.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves reused: the clopen-basis lemma and the compact closed finite-intersection lemma, together with the existing subspace-topology definition.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, clopen partitions, incidence limits, profinite limits, `DiscreteQuotient`, and `asLimitCone`, including the topology, category-theory and pro-etale directories. The clopen-idempotent and representation-theoretic partition results found do not state this topological pullback theorem. No claim is made that an upstream sorry declaration is a finished proof.

## WANTED

None. The blueprint proof and the Stacks sources needed here are present locally.

## Audit and changes

The item was a statement-only node, without an existing sandbox attempt. Its statement is correct and unchanged. In particular, the limit index is nonempty even when S is empty; in that case its one partition has no parts and its incidence space is empty. No statement dispute is needed.

Read `GOAL.md`, the stage-1 brief, the three levels in `SETUP.md`, the worker role, the stage-1 document, delivery-errors B–E, the chapter record and unit `sk-thm-pe-wc-cover`. The unit's second step explicitly uses finite quotients, image restrictions and their inverse limit to realize the component pullback. This split supplies exactly the topology argument in that step and changes neither the unit nor the chapter.

The source is `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-thm-pe-wc-cover/det-pe-wc-cover-second-stage.proof.md`, paragraph *2.*, read in full with its Preliminaries and surrounding paragraphs. Also read Stacks `proetale.tex`, Tag 097D, `lemma-construct-profinite` (lines 881 onward): it constructs the image spaces Z_i and says that their limit is T and that their pullbacks limit to the pullback. For the general topology used to expand that argument, read `topology.tex`, Tag 005D, `lemma-intersection-closed-in-quasi-compact` (lines 1724 onward), and Tags 08ZY, `lemma-profinite`, and 08ZZ, `lemma-profinite-refine-open-covering` (lines 4134 and 4207 onward). The blueprint is agent-written; `proof_origin.by` is accordingly `agent`.

The blueprint's continuity paragraph alone does not establish the full homeomorphism for arbitrary X. The split supplies both directions using basic open cylinders, without assuming X Hausdorff or compact. Its other expansions specify the common x coordinate, both finite-intersection hypotheses including the empty finite family, the closedness of the fibers, and both inverse identities. No localization, spectrum or algebraic facts are used for this topological item.

## Mathlib and duplicate searches

The required search command ran five times: LeanFinder on the incidence pullback, Loogle on `"DiscreteQuotient", "limit"`, grep on `incidence|isoAsLimitConeLift|asLimitCone` under `Topology/Category/Profinite`, LeanSearch on partition reconstruction of a pullback, and a second LeanFinder phrasing on the intersection of images and coordinate topology. All services returned results, recorded in `searches.jsonl`; no unavailable search was misreported. The appended `mathlib_searches` queries are exactly those run. The original Q96 search records were retained and read, not invented afresh.

Read the returned `Mathlib/Topology/Category/Profinite/AsLimit.lean`, lines 45–102. `Profinite.isoAsLimitConeLift` and `Profinite.asLimit` reconstruct S from its discrete quotients. They do not directly give the image incidence spaces over arbitrary X or the equality of the intersections of the images f(A). The Product and Nobeling hits concern finite-coordinate compact-product realizations. None is a one-line specialization giving every clause of this item.

Searched the whole DAG by clopen-basis, compact closed finite-intersection, profinite partition and incidence terminology. Ran `tools/blueprint_refs.py ancestor lem-pe-profinite-partition-incidence-limit`, giving `det-pe-wc-cover-second-stage`; also ran whole-blueprint searches for `clopen`, `partition` and `incidence`. No other blueprint node states this arbitrary-X image-incidence theorem. The parent itself uses this item and cannot be cited back without a cycle. `lem-sfb-finite-quotient-fiber-product` was opened: it uses simultaneous finite quotients of three profinite spaces, whereas X here is arbitrary, so it was not substituted for this item.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. The two needed general topological lemmas already exist and are cited directly, not re-created or specialized into redundant nodes.

## Review by Q74

I checked the original statement against the source's paragraph *2.* with S and P profinite and X arbitrary. Neither the statement nor the proof uses surjectivity of f, nonempty fibers globally, or a separation condition on X. The small cases include empty S, empty X, singleton S, empty P (which forces empty S and X), constant f, and a two-point discrete S with f taking two different values. In the two-point case the discrete partition immediately distinguishes the two possible s coordinates; if f is constant, both parts can be incident to the same x and are still distinguished by the part coordinate. These checks agree with the asserted pullback and the intersection-of-images clause.

For every cited node I opened and read its statement, rather than using its proof. The full statements quoted in `citations.json` contain exactly what the corresponding steps use.

1. Step 1 is a finite-set and definition argument: nonempty pairwise intersections give the common refinement, containment gives uniqueness and composition, and incidence is preserved by image containment. Empty S is treated before trying to choose a part, including vacuity of compatible choices and its unique topology; empty X gives the empty homeomorphism but does not end the proof of the independent assertions about S. Only S is assumed nonempty in the later steps. Nonempty I is proved explicitly in both cases. It uses no non-elementary theorem and cites no node.
2. Step 2 cites `lem-weil-pbc-profinite-clopen-basis`. Its statement explicitly gives a clopen neighborhood inside every prescribed open neighborhood for a compact Hausdorff totally disconnected S. These are precisely the hypotheses here. The remaining argument is written out: coordinate preimages are unions of parts, and each nontrivial clopen is a fiber of a two-part partition. Hausdorff separation proves that the complement of a singleton is open, so that the cited basis separates two distinct points. This step is marked non-elementary because the clopen-basis theorem is its input.
3. Step 3 cites `lem-sfb-compact-closed-finite-intersection`. It states nonempty intersection for an arbitrarily indexed closed family in a compact space, including the empty finite intersection. Here the ambient space is S, each part is closed and nonempty, and a common refinement supplies a nonempty subset of each finite intersection. For the empty finite family the intersection is S, already known nonempty after step 1. Uniqueness then uses the separation just established in step 2, with no further theorem. This proves the compatible-parts clause directly rather than moving it into a new node.
4. Step 4 cites the same compactness node, now for the closed subsets f^{-1}({p}) intersect A_Q of S. The arbitrary candidate p is in every image, so each such set is nonempty. Hausdorff P and continuity of f give closedness; this uses no separation of X. The common-refinement argument again verifies every finite intersection and the empty one. The resulting point must be the unique s from step 3, proving f(s)=p. This is the substantive image-intersection argument of the source, carried in the item itself.
5. Step 5 has no external citation because its conclusions follow explicitly from steps 1, 3 and 4 and the definition of incidence. A common refinement forces equality of all x coordinates. The displayed constructions of Phi and Psi then satisfy both inverse identities coordinate by coordinate. No claim about the topology is inferred from bijectivity.
6. Step 6 cites `def-kun-subspace-topology`, whose statement defines subspace opens as intersections with ambient opens. The proof checks inverse images of product rectangles for transition maps and Phi_Q, then finite-coordinate basic opens for the product. This is a definition-level continuity argument, marked elementary; the coordinate continuity used here was already established in step 2. No general limit-existence or limit-preservation theorem is implicitly invoked.
7. Step 7 cites that same subspace definition and the clopen-basis lemma. For the x coordinate it specifies the open cylinder at the coarse partition {S}; this is legal because empty S was handled first. For the s coordinate it specifies the cylinder at {V,S minus V}, using that partition only when both parts are nonempty, and treats V empty or S separately. Arbitrary opens of S are unions of those basis elements by the cited statement. Finally, the inverse image of a product rectangle intersected with the pullback is the intersection of the two coordinate inverse images. This proves continuity of Psi and the homeomorphism for arbitrary X. The step is marked non-elementary for its explicit basis citation.

I checked B1–B9: there are no new unsplit nodes, no statement objects left undefined, no new source tags or Mathlib leaves lacking metadata, and no fabricated searches; the item's complete blueprint reference and `same_as` search are present. C1–C8 were checked against the three cited node files: there is no use of a cited node's proof, no absent non-elementary input, and no off-route non-Mathlib statement tool use. Both general topological statements are already Mathlib leaves, so no route exception is required. The parent is not a dependency. D1–D5 were checked by keeping the reconstruction, image-intersection and topological arguments in the item's own steps, with no new clause-restating nodes. E1–E7 were checked through the finite-intersection hypotheses, the Hausdorff condition precisely where singleton closedness is used, the genuinely arbitrary X, the empty cases and explicit coordinate compatibility. No non-elementary step exceeds 2000 characters (the longest is 1012), and no comparison or identification is hidden behind 'standard' or 'transport'.

## Repair of return L (2026-10-22)

The returned entry names delivery head `83283702c61`: the independent reader approved the mathematics, but the landing gate refused a side completion that had not been promoted to the live DAG. The required initial dry run was run before editing and exited successfully with `OK (not pushed)` at `69f1c4be94b`. This was diagnostic validation of the retained attempt, not a new delivery.

I compared the retained delivered split with the current shared read clone. The current item is `unsplit`, with empty proof, proof dependencies and proof origin; its statement, source, statement dependencies, chapter, unit and blueprint reference agree with the retained version. The live node has the five inherited Q96 searches; the sandbox additionally retains the five searches actually run by Q74 and their log. None were rerun or invented. There is no released repair note for this item. The delivery command fetches and constructs its commit on the current `origin/sheaf-dag`, preserving the current maintainer fields, so this repair does not carry forward the old side-completion metadata.

I reopened all three current cited nodes, not just their identifiers. `lem-weil-pbc-profinite-clopen-basis` still states the pointwise clopen-basis assertion for compact Hausdorff totally disconnected S, and is a Mathlib leaf. `lem-sfb-compact-closed-finite-intersection` still allows an arbitrary set-indexed closed family in a compact space, explicitly including the empty finite intersection, and is a Mathlib leaf. `def-kun-subspace-topology` still gives opens as intersections with ambient opens. Thus steps 2 and 7 can still use the basis statement, steps 3 and 4 can still use the finite-intersection statement, and steps 6 and 7 can still use the subspace definition. I checked all six existing quotations against these current statements; none needed replacement. No cited hypothesis or route changed.

I also repaired a small incompleteness in the retained step 1: treating empty X proves the homeomorphism but does not discharge the separate assertions about compatible parts of a nonempty S. Step 1 now assumes only S nonempty thereafter, so steps 2–4 prove those assertions even for empty X. For empty S it explicitly checks that compatible choices of parts do not exist and that the partition coordinates generate its unique topology. This preserves the statement and all seven proof steps while making the empty-case proof complete. The largest non-elementary step remains below 2000 characters. Re-reading the blueprint paragraph *2.* and Stacks Tags 097D, 005D, 08ZY and 08ZZ confirms the same compactness and clopen-coordinate route; no new node or different source is needed.

The repair is therefore a refreshed delivery on the current DAG with a concrete proof correction and a current citation review, rather than an unchanged re-push. The final dry run and direct push are performed after this report is saved.

## Unfinished work

None in the requested one-level split. This stage writes no Lean and runs no compiler. The report and split are ready for the required server dry run and direct delivery; their final status is recorded by the delivery command.
