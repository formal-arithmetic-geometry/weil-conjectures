## Worker report

Files written: `dag/nodes/sec-proetale-coefficients/det-pe-stonean-projective.json` (statement, split; full statement unchanged), `citations.json`, and `report.md`. There are zero new nodes and zero new Mathlib leaves. Four existing Mathlib leaves supply only supporting facts: products are compact, closed subspaces are compact, Zorn's lemma for subset families, and compact-to-Hausdorff continuous bijections are homeomorphisms. Scratch scripts, the retained returned-node snapshot, and the search log stay in the sandbox and are not delivery files.

Attachments: none. A fresh read-only search of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item tag, Gleason, Stonean and the projectivity equivalence found only component-space uses in `RingTheory/ProEtale/WContractible.lean`, not a project declaration stating all three equivalent conditions and the profinite conclusion. Mathlib declarations and upstream declarations with sorry are not project attachments.

WANTED: none.

What was wrong: the returned split's Step 6 cited `lem-weil-pbc-extremally-disconnected-component-section` for the entire substantive implication 1 ⇒ 3. The original reports claimed that having the same route inside that theorem's proof satisfied the blueprint requirement. That claim was wrong: the split itself must realize the minimal closed surjective source argument. This repair removes the citation entirely and writes that argument in Steps 6–12. The prior worker and second-reader reports are superseded by this report; their endorsements of the shortcut must not be relied on.

The current shared item remains `imported` and has no `chapter` or `unit` field; the corresponding chapter/unit JSON records are absent. Its statement is identical to the returned sandbox statement, and there is no `blueprint_update`. I compared its imported proof with the returned sandbox proof (retained as `repair-returned-node.json`) and the current main-20261015 blueprint. No maintainer metadata is changed. The required delivery tool rebases the repaired fields onto its fetched current main in its temporary worktree. The parent Stonean proposition also includes the existence of covers, so this item is not its whole key statement and no unit realization record is edited.

Nothing mathematical remains unfinished. Stage 1 alone is authorized: no Lean was written, no compiler/Lake/build command was run, and no live project/launcher file was written. No direct git command was run in the shared repository. This worker runs only the required `--no-push` delivery validation and leaves delivery to a fresh second reader.

## Repair of the return

The return identifies one fault, violating stages/1-dag.md §6 and delivery-errors C7/C8: Step 6 substitutes an exact theorem from another unit for the blueprint's minimal closed surjective subspace route. It is repaired by replacing that step with seven explicit steps:

- Step 6 verifies that intersections of chains of closed surjective subsets still surject, using closed fibres and a finite-open-subcover contradiction, and handles the empty chain separately.
- Step 7 passes to complements to apply the existing **upper-bound** formulation of Zorn, then obtains a minimal closed compact Hausdorff source. Closed subsets of this source are closed in the original source, so its minimality has the required relative form.
- Step 8 proves the restricted map is closed by Hausdorff neighbourhoods and a finite subcover. It cites only the existing closed-subspace compactness leaf.
- Steps 9–11 develop the opens V-star, their nonemptiness from minimality, density at image points, and the extremal-disconnectedness contradiction that forces injectivity.
- Step 12 applies the supporting compact-to-Hausdorff bijection leaf and constructs the section as inverse followed by inclusion.

No mathematical error in the blueprint is alleged, and no route exception is requested. These steps are the source's original argument. Mathlib leaves are used for supporting generic facts only; the complete section theorem is no longer a dependency. `proof_deps`, `proof_origin`, `split_report.blueprint`, citations, the final profinite step's step numbers, and this report all reflect the repair. This is a substantive proof change, not an unchanged re-push or a rebase alone.

## Searches and reuse

The retained `mathlib_searches` are the searches already performed by the first worker and second reader with `msearch.py Q59 det-pe-stonean-projective`; their actual query log is retained in `searches.jsonl`. They include LeanFinder, Loogle, LeanSearch and grep, with multiple phrasings for the complete item and its section criterion. They find Gleason's equivalence and supporting facts, but not a project attachment of the complete statement. The complete item includes the section/lifting equivalence and profinite realization, which are written out rather than identified with a single Gleason declaration.

Before choosing dependencies, I searched the current DAG's titles and full statements for minimal closed/compact subsets, finite intersection properties, Zorn, closed maps and continuous closed images. I ran the whole-blueprint search for `minimal closed` and `Zorn`; both returned zero blueprint-node matches. `tools/blueprint_refs.py ancestor det-pe-stonean-projective` confirms this imported node is its own nearest blueprint ancestor. The retained broader searches had already checked extremal disconnectedness, compact Hausdorff spaces, fibre products, total disconnectedness and products. No new node is created, so no new-node duplicate or Mathlib-search obligation arises.

I opened the full statements of all four actual cited nodes, not the removed section theorem alone. I also read their Mathlib source declarations: `zorn_subset`, `Order/Zorn.lean:143`; `IsClosed.isCompact`, `Topology/Compactness/Compact.lean:865`; `Pi.compactSpace`, that file at line 1183; and `isHomeomorph_iff_continuous_bijective`, `Topology/Homeomorph/Lemmas.lean:540`. Zorn is for upper bounds, including the empty chain; the complement construction in Step 7 is necessary and explicit. The bijection statement allows subspaces, so Step 12 takes the original source P with subset P0 and the target S with whole subset S. `citations.json` copies each used node's entire statement verbatim, once for every step that cites it.

## Review by Q59

I read the current main-20261015 `det-pe-stonean-projective.md` and its full proof, the parent `sk-prop-pe-stonean` statement/proof, and the chapter section text. The parent proof explicitly names the minimal closed surjective source route, which the repaired Steps 6–12 now realize. I read Stacks `topology.tex` Tag 08YN (`proposition-projective-in-category-hausdorff-qc`), together with its actual supporting proofs: 08YM (`lemma-find-compact-subset`), 08YJ (`lemma-image-open-technical`), 08YK (`lemma-intersection-empty`), 08YL (`lemma-isomorphism`), 08YD (`lemma-closed-map`), and 08YE (`lemma-bijective-map`). For the final clauses I read 08YI (`definition-extremally-disconnected` and the following paragraph) and the proof of 08ZY (`lemma-profinite`). I verified the tag/label mappings in `stacks-project/tags/tags`. Source numbering interchanges the item's conditions 2 and 3; the actual hypotheses and conclusions agree. No statement correction or dispute is needed, and there are no new statements needing separate sources.

Step 1 uses the assumed lifting property with the identity map; its equation is exactly the section equation. It is elementary and cites no external fact.

Step 2 takes precisely product quasi-compactness from `lem-weil-pbc-tychonoff-product-quasi-compact` and closed-subspace quasi-compactness from `lem-weil-pbc-closed-in-quasi-compact`. Hausdorffness of the product and subspace and closedness of the coincidence locus are proved by separating neighbourhoods. The hypotheses on X, S and Y are all used where required, especially Hausdorffness of Y for the closed locus.

Step 3 proves surjectivity of the pullback projection pointwise from that of p and invokes the assumed condition 3 on the admissible source from Step 2. The second projection gives the lift and its equation by membership in the fibre product. This is elementary and takes no unrecorded lifting theorem.

Step 4 uses the closed-subspace node for exactly the two closed subsets, the closure of U and its complement. It supplies the two-finite-subcovers proof of compactness of their disjoint union, and the separating-neighbourhood proof of its Hausdorffness. The inclusions give the required continuous surjection, so the assumed condition 3 applies. Step 5 proves both inclusions in the equality between the clopen inverse image and the closure, including boundary points where the disjoint-union fibre has two points. It is elementary.

Step 6 follows the actual chain/fibre argument of 08YM. The collection of closed subsets is a set. A singleton is closed by Hausdorff separation, and continuity gives closed fibres. The finite-intersection step is not imported as an uncited theorem: if the total intersection is empty, complements give an open cover and compactness gives the contradictory finite subcover. A finite nonempty chain has a least member by pairwise comparison. The empty chain uses P; the empty finite subfamily is valid because a fixed s has a preimage. This is the elementary open-cover argument, without a hidden limit-existence lemma.

Step 7 cites `lem-weil-pbc-zorn-lemma` for exactly its stated upper-bound conclusion for subset families. I checked the order reversal explicitly: a chain of complements corresponds to a chain of closed sources, and the complement of its intersection contains every chain member. The maximal complement gives a minimal closed source. The empty chain has upper bound the empty complement because P surjects. `lem-weil-pbc-closed-in-quasi-compact` supplies compactness of P0, and Hausdorffness restricts. A relatively closed F in closed P0 is closed in P, so minimality rules out every proper relatively closed surjective subset; this essential hypothesis is not omitted.

Step 8 cites `lem-weil-pbc-closed-in-quasi-compact` only to make a closed F in P0 compact. For s outside its image, finitely many neighbourhoods U_x cover F after inverse image; intersecting their paired neighbourhoods of s avoids the whole image. This proves closedness from definitions. The empty F uses S as the neighbourhood. There is no uncited invocation of continuous images being compact or compact subsets being closed, and no claim of universal closedness is needed.

Step 9 uses the proved closedness of q0 to make V-star open. Surjectivity says every fibre is nonempty, so V-star is contained in the image of V. Minimality says it is nonempty for nonempty V; monotonicity follows from containment of fibres. These are the actual elementary consequences of the displayed definition, not the conclusion of the removed section node.

Step 10 follows 08YJ in the blueprint's notation. For a neighbourhood N of the image of a, A intersect inverse image N is nonempty open. Its star is nonempty by Step 9, lies in A-star by monotonicity, and lies in N because it lies in the image of that intersection. Hence every N meets A-star. No surjectivity of the restriction to A is presumed.

Step 11 uses Hausdorffness of P0 to obtain disjoint A and B. Surjectivity excludes a fibre inside their empty intersection, so their stars are disjoint. Step 10 puts s in both closures. Extremal disconnectedness makes the first closure open, so it meets the other star; that star is open and avoids the first set and therefore its closure. The contradiction is fully written out. This is the same substantive injectivity argument as 08YL and the blueprint, not a citation of its conclusion.

Step 12 now uses `lem-weil-pbc-compact-hausdorff-bijection` for exactly the homeomorphism conclusion, after compactness, continuity, surjectivity and injectivity have all been proved. Composing its inverse with the subspace inclusion gives the section and the equation is computed explicitly. Only this supporting homeomorphism fact is supplied externally.

Step 13 proves clopen separation from disjoint Hausdorff neighbourhoods and extremal disconnectedness, then shows a connected subset cannot contain two separated points. Step 14 follows the finite-clopen-partition proof of 08ZY, using Step 13 directly for injectivity. Common refinements give a cofiltered set-indexed diagram. Compatibility supplies nonempty finite intersections of the selected closed blocks; the open-complement finite-subcover argument supplies a common point. Continuity and Hausdorffness of the inverse limit are proved by coordinate neighbourhoods. The sole cited node is the compact-to-Hausdorff bijection node, applied to the whole spaces to get a homeomorphism. The empty S has its separate one-object empty finite-space diagram. Thus no uncited inverse-limit compactness or connected-component characterization is used.

Small cases checked: S empty forces P empty for every map to S, and the minimal source construction still gives P0 empty; chain surjectivity is then vacuous and the complement-Zorn empty chain still has its upper bound. For singleton S and a two-point surjection, minimality chooses a singleton source and the constructed section behaves correctly. The fibre finite-intersection argument explicitly handles the empty chain, and the closed-image argument handles empty F. For U empty or U equal to S, Steps 4–5 still hold. Boundary points of a proper U need the closedness argument and are not assigned a unique lift. If V is empty its star is empty (including empty S); nonemptiness is claimed only for nonempty V. No extremal disconnectedness of P or X is assumed. The p-adic integers are not incorrectly asserted to satisfy condition 1 merely because they are profinite.

Against delivery-errors B–E: no new nodes, duplicate statements, hollow definitions or clause restatements occur. Every non-elementary external input has its actual cited statement, and its hypotheses are verified above. Finite-intersection, closed-image and closure arguments are explicitly supplied rather than hidden under source tags. C7/C8 are repaired by following the original route, not by recording a questionable exception; no maintainer-owned `tool_uses` is written. Source tags in elementary argument source fields identify the arguments read and do not replace node citations. The full item statement and current blueprint fields/import flag remain intact. No banned SGA source is used.

## Validation

The required no-push dry run is run after this repaired report and the regenerated citations. A fresh second reader must independently review the repaired proof and deliver it; the returned version's second-reading endorsement does not certify these new steps.

First repaired dry run: preflight ran and refused an unrelated delivered-tree finding: `dag/nodes/sec-smooth-purity/def-cbc-enhanced-diagrams-cones.json` did not parse (`Extra data: line 187 column 2 (char 30018)`). That file is outside this item's permitted repair scope. No node/citation finding on this item was reported. The same required no-push command is retried against freshly fetched main; the foreign node is not edited or delivered.

## Second reading by Q59

I independently opened the item node, the cited DAG nodes, the Stacks source tags, and the current blueprint proof. The verdict for every proof step is recorded below.

- Step 1: checked against Stacks 08YN and the definition of a section; identity lifting is elementary and correct.
- Step 2: checked against 08YN and the product/closed-subspace nodes; compactness, Hausdorffness, and closedness of the pullback are all justified under the stated hypotheses.
- Step 3: checked against 08YN; pointwise surjectivity and the projection section equation are elementary and correct.
- Step 4: checked against 08YN and 005C; the disjoint-union compact Hausdorff surjection is constructed with both finite-subcover arguments.
- Step 5: checked against 08YN; both inclusions identifying the clopen inverse image with the closure are explicit, including boundary points.
- Step 6: checked against 08YM; chain intersections preserve surjectivity by the fibre finite-intersection/open-cover argument, including empty chains.
- Step 7: checked against 08YM and the exact upper-bound statement of `lem-weil-pbc-zorn-lemma`; complement order reversal and minimality are correct, and compact Hausdorff hypotheses on the restriction are supplied.
- Step 8: checked against 08YL/08YD and the closed-subspace node; the finite-neighbourhood proof establishes closedness of the restricted map, including the empty closed set.
- Step 9: checked against 08YJ; the definition and elementary properties of (V^*) use only the established closedness, surjectivity, and minimality.
- Step 10: checked against 08YJ; the neighbourhood argument proves density at an image point without assuming a restricted surjection.
- Step 11: checked against 08YK/08YL and extremal disconnectedness; disjoint stars and the closure contradiction prove injectivity with all separation steps written.
- Step 12: checked against 08YN and the exact compact-to-Hausdorff bijection node; the inverse and inclusion give a continuous section with the equation computed.
- Step 13: checked against 08YI; clopen separation and total disconnectedness follow directly from Hausdorffness and extremal disconnectedness.
- Step 14: checked against 08ZY; finite clopen partitions, common refinements, finite-intersection compactness, and the homeomorphism to the inverse limit are all spelled out, with the empty-space case handled separately.
- New nodes: none; no B1–B7 review is applicable. The four cited supporting nodes are existing DAG Mathlib leaves, and their statements were read verbatim in `citations.json`.

Changes made during this second reading: no further mathematical or statement changes were needed. I verified that the prior repair removes the cross-unit section-theorem shortcut, that all citations quote the exact supporting statements, and that the required dry run passes preflight. The only earlier reported malformed foreign node was outside this item's delivery scope and is absent from the successful current validation.
