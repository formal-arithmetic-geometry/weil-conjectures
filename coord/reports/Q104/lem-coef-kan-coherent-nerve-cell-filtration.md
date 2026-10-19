# Stage-1 worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-kan-coherent-nerve-cell-filtration.json`: unchanged statement, split into seven proof steps; zero new nodes and zero Mathlib leaves.
- `citations.json`: a verbatim statement passage for each step/node pair, with additional definition passages where both constructions are used.
- `searches.jsonl`: actual Mathlib search records. `prepare_split.py` and `check_combinatorics.py` are sandbox-only preparation and finite combinatorial verification scripts; they are not project files to deliver.

## Attachments

None. Searches under the read-only slopmaster2 `WeilConjectures/` and `Comparator/` trees for the item id, coherent nerve, locally Kan, coherent realization and simplicial thickening found no project declaration stating the item. Upstream master was used only as read-only reference material; no sorry declaration there is treated as finished.

## WANTED

WANTED: archival copies of Kerodon Proposition 2.4.5.8 (00LR), Proposition 2.4.5.9 (00LS), Corollary 2.4.5.10 (00LT), Corollary 2.4.5.12 (00LV), and Lemma 3.1.2.12 (00TH), for this item. I read all five pages online. These are Kerodon identifiers, not Stacks tags; no Stacks theorem supplies this enriched simplicial calculation. The proof is marked agent-origin because these pages are not in `literature/` and its combinatorial and universal-property details are expanded here.

## What was wrong in the imported node and what changed

The imported support node was statement-only. Its statement is true and remains byte-for-byte unchanged. The parent uses actual finite enriched horn pushouts, so merely proving an anodyne lifting property or a retract of a transfinite cell complex would not suffice. The split now gives the finite construction explicitly.

I first drafted a helper asserting the endpoint hollow-cube filtration. On self-review, this moved too much of the item into a new node (D1/D2). I removed that uncommitted helper and searched more broadly. The existing `lem-coef-infinity-right-prism-boundary` states exactly the finite standard-prism filtration needed. It is now cited in step 5, and no new node remains. The support-map calculation, finite base-chain filtration, and enriched pushout argument are carried by the item's own steps. No statement dispute, route change, or maintainer metadata repair is proposed.

The chapter and unit records and the main-20261015 proof of `prop-coef-integral-exceptional-adjoint` were read. This is a foundational child along the existing coherent-adjunction ancestry, not a unit key node, so no `realized` field changes. Its historical unit and blueprint ancestry are retained, with `same_as: []` after whole-blueprint searches. The current blueprint ancestor's second proof paragraph is the derived coefficient-adjunction calculation; the ancestry identifies which coherent foundations this child serves, not a claim that the ancestor text itself contains a cube proof.

## Not duplicates

No new nodes are delivered. Whole-DAG statement/source searches and `tools/blueprint_refs.py search` were made for coherent realization, enriched horns, hollow cube, subset chains, finite cylinder and prism. The exact relevant existing node is `lem-coef-infinity-right-prism-boundary`, whose complete statement and proof were read and reused. `lem-coef-marked-endpoint-prism-generation` concerns a marked weakly saturated class; `lem-coef-infinity-right-anodyne-product` concerns membership in a class allowing retracts and transfinite compositions; neither alone supplies the finite enriched filtration. `lem-coef-rigidification-boundary-cube` treats the full boundary, `lem-coef-pinched-cube-latching` treats a pinched quotient, and `lem-coef-coherent-fixed-vertex-cofibrations` gives a cofibration property. None is substituted for a clause it does not state. The broader coherent-nerve comparison is not cited.

## Review by Q104

I read the worker contract, stage-1 instructions, all of delivery-errors B–E, the three blueprint levels in SETUP, GOAL and dag-sync. I compared the item with Kerodon 00LR, 00LS, 00LT and 00LV and checked the reused prism statement against 00TH. The source uses complementary coordinates in its path convention; the item's proof derives its own inclusion-poset coordinates and obtains the correct box, with the distinguished coordinate constantly 1 as the retained endpoint. No unproved identification of coefficient categories occurs in this purely combinatorial support lemma. No SGA source is used.

For step 1 I read `def-cbc-enhanced-diagrams-cones` and `def-coef-infinity-category-of-spaces`. They give the ordinary nerve as chains and the subset-poset mapping objects with union as composition. Intersecting a chain with the intervals between successive elements of its first subset gives its unique word in indecomposable chains. This proves the freeness being used; no free-category theorem is silently imported. Identities are the empty words, and reverse mapping sets are empty.

For step 2 I read those two statements and `def-weil-pbc-category-colimit`. The step proves the particular colimit by mapping out, rather than assuming mapping objects preserve enriched colimits. Every simplex factors through its image face, and every generator appears in its smallest support face. Thus assignments on the face diagram agree exactly on shared generators and extend uniquely to words. Deletion/repetition followed by the already proved unique factorization gives the simplicial operators and makes the universal property an enriched one. All the diagrams are small (the face poset is finite). These are explicit elementary construction checks, not an appeal to an unrecorded general enriched-colimit theorem.

For step 3 I checked the same two definition statements. The horn convention is exactly omission of a vertex different from i. A proper interval omits 0 or n, which are both different from the inner vertex i. For the endpoint chain, a nontrivial word is allowed because every factor lies in a proper interval; an indecomposable word is allowed precisely when its final support is a horn face. This yields the formula J_0 nonempty or D minus {i} not contained in J_r. The normal form proves both injectivity and the image description, not merely surjectivity.

For step 4 I checked the horn/nerve/product definition. A weak chain has a coordinate constantly 1 exactly when that coordinate occurs in its minimum, and a coordinate constantly 0 exactly when it is absent from its maximum. The resulting box is ({1} times B) union (interval times boundary B). A nondegenerate simplex of the base is a strict chain in a finite poset. Ordering these by dimension ensures that each new embedded simplex meets the previous union in its whole boundary; different simplices of the same dimension cannot contain one another. This directly verifies each base pushout.

For step 5 I read the full statement of `lem-coef-infinity-right-prism-boundary`, not just its proof: it supplies exactly k+1 pushouts of the positive-dimensional horns Lambda_{q+1}^{k+1} for the prism over a k-simplex, including k=0. Its source 00TH was read online. The preimage/intersection formula in this step verifies the hypothesis for pushing each prism filtration into our box. The colimit-definition quote supplies the gluing universal property; the maps are glued degreewise and commute with operators. The base has finitely many strict chains, and each prism has finitely many steps, so this gives an actual finite filtration without a retract or an infinite cell construction. The prism node is in the same unit and its dependency closure does not contain this item; no tool-use declaration is needed.

For step 6 I checked the simplicial-category and union-composition formula in the spaces definition. Every nonidentity composition with changed output passes through an interior vertex; its endpoint chain has that vertex in every subset and hence lies in the original box. A changed endpoint mapping simplex can otherwise compose only with identities. Thus every intermediate endpoint subset gives a genuine enriched subcategory with inherited associativity and units.

For step 7 I checked the same definition and the colimit universal property. A functor from U(Delta^m) specifies its two objects and just one forward simplicial map. The simplicial horn pushout yields the unique extended endpoint map. The proof enumerates every composition case: a changed map as an input has only an identity next to it; a changed output from old inputs lands in the original box. Hence the map is an enriched functor. This proves the pushout against arbitrary target categories, including coincident images F0=Fn, and preserves the objects throughout. A singleton is a finite coproduct, as required by the item. No Kan hypothesis or uniqueness of Kan fillers is assumed.

The source and Lean searches found no exact Mathlib or project attachment. I retained all inherited item search records, read their actual results in the earlier parent's search log, and appended only four fresh queries recorded by msearch in this sandbox. Additional exploratory prism searches in `searches.jsonl` found `SSet.prodStdSimplex.strongAnodyneExtensions_unionProd_ι`; I read PushoutProduct.lean:57–64, Basic.lean:123–171, and RelativeCellComplex.lean:41–140. The result gives a regular pairing/strong-anodyne property for a standard horn–boundary product; obtaining this item's coherent-category finite filtration still requires the mapping calculation, the finite-base argument, and the enriched pushout checks. It is not a one-line Mathlib specialization of the item. SimplicialNerve.lean:12–39 and its thickening definitions were also read; they do not assert this filtration. No search that was not run is added; no Mathlib leaf is claimed.

Small cases were checked by the sandbox Python enumeration in `check_combinatorics.py`, not Lean. In cube dimensions 1 through 5, for every distinguished face, the endpoint support predicate agreed with the indecomposable-word test, every proposed simplex met the current stage in exactly its attaching horn, and the final stage exhausted the cube. The counts of horn attachments were 1, 2, 8, 44, 308, respectively. The checks included all strict chains and all their faces (2163 strict chains in dimension 5); repeating vertices accounts for degeneracies in the general proof. In particular n=2 gives a vertex into an interval, n=3 gives three edges into a square, and the base B of dimension zero has empty boundary and one prism attachment. Empty reverse mapping sets and identity endomorphisms were checked explicitly. These finite checks support the argument; the general proof uses finite subset-poset chains and the existing prism theorem.

I verified citations.json by checking each quote as an exact substring of the corresponding current node statement. proof_deps is the union of all step uses. No new node, cycle, weakened statement or altered unit route remains. No Lean was written and no compiler, Lake, or library build was run. All final project artifacts are in the assigned sandbox; nothing is delivered or pushed by this worker.

## What could not be finished

No mathematical part of this stage-1 split remains open. The online Kerodon sources still need archival copies. Required dry-run diagnostics and their repairs are recorded below.

## Validation

The initial server check_dag run completed successfully. It was queued while the draft was still being refined; the final deliver.py --no-push run below is the authoritative check of the completed files.

## Second reading by Q104

- Item statement: checked against Kerodon Proposition 2.4.5.8 (00LR), Proposition 2.4.5.9 (00LS), Corollary 2.4.5.10 (00LT), Corollary 2.4.5.12 (00LV), and the finite prism input Lemma 3.1.2.12 (00TH); the seven clauses, object set, horn dimensions, and identity-on-objects transitions agree.
- Step 1: checked against the subset-poset and nerve clauses of `def-cbc-enhanced-diagrams-cones` and `def-coef-infinity-category-of-spaces`; the interval factorization is unique and elementary.
- Step 2: checked against those definitions and the colimit universal property of `def-weil-pbc-category-colimit`; the nondegenerate-face reduction and mapping-out argument supply the enriched colimit, with no unstated preservation theorem.
- Step 3: checked against 00LR and the two definition nodes, including the reversal of 00LR's decreasing chains into the project's increasing convention; the support predicate and the exceptional endpoint mapping set agree.
- Step 4: checked against 00LV's hollow-cube box and the finite nerve of the subset poset; the boundary filtration handles the empty zero-dimensional boundary and all proper faces.
- Step 5: checked against the full statement of `lem-coef-infinity-right-prism-boundary` (00TH) and the colimit definition; the preimage is the stated prism boundary, and finite base simplices give finitely many horn pushouts, including the `k=0` one-dimensional horns.
- Step 6: checked against the full composition and endpoint-mapping clauses of `def-coef-infinity-category-of-spaces` and 00LS; the intermediate endpoint mapping sets are enriched subcategories and the interior-vertex compositions lie in the original box.
- Step 7: checked against 00LS and the colimit universal property; maps out of each `U`-horn pushout are exactly endpoint simplicial maps agreeing on the horn, and every changed composition case is covered, including coincident target objects.
- New nodes: none; the only auxiliary fact is the existing `lem-coef-infinity-right-prism-boundary`, whose statement was read in full. No Mathlib leaf is needed, and whole-DAG searches found no duplicate for the item.
- Edge cases checked: `n=2` and `n=3`, the zero-dimensional base `B=\Delta^0`, empty reverse mapping sets, identity endomorphisms, and the `m=1` horn attachments all agree with the statements. No statement dispute or source error was found.
- Changes made: none to the item, citations, or searches; this second-reading record is the only modification.
