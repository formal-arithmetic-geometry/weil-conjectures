# Stage-1 delivery: lem-a1-sections-intersection-structure-colimit

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-a1-sections-intersection-structure-colimit.json: statement item, now split into eight proof steps; no Mathlib match for the full statement.
- citations.json: exact statement quotations for all 17 step-to-node citations.
- report.md: this report and the signed self-review below.
- searches.jsonl: unmodified output log produced by the required msearch.py commands. The two sandbox-only write scripts prepare the JSON and report citations; they are not project tools or deliverable DAG files.

New nodes: 0. New Mathlib leaves: 0. The statement, its four statement dependencies, chapter, unit and inherited blueprint ancestry are unchanged. The source place now identifies the unnamed equation precisely, before Tag 0API, rather than only its later use in Tag 0APJ.

## Attachments

None. Searched the project under /home/ubuntu/weil-src-slopmaster2/WeilConjectures by the exact blueprint id and by intersection/sections and neighbourhood-colimit phrases. The project hits concern Cech intersections, affine-transition limits, or unrelated fibre-product pairings. None proves the entire present statement. The upstream master is not used as evidence of a finished proof.

## WANTED

None. All proof sources are present locally in literature/stacks-project/.

## Findings and changes

The imported node had no proof. Its statement agrees with the equation in more-groupoids.tex, section-ind-quasi-affine, equation-sections-of-intersection, and its use in Tag 0APJ (lemma-affine-base-change). The formula there holds even for any sheaf; we retain this item's structure-sheaf specialization, its concrete clauses, three value categories and naturality. No STATEMENT-DISPUTED or statement correction was necessary.

I read the fixed chapter and sk-p-real-rankin unit as well as the current main-20261015 ancestor lem-a1-affine-hc0. The imported unit/ancestor is the distant vanishing application; the inherited from.place and via chain specify the Gabber fpqc descent input it serves. This delivery does not edit those bindings or any unit. It follows the source's qcqs-to-spectral and sheaf-continuity route; using the existing fixed-sheaf Tag 0A32 statement avoids an unnecessary colimit of a constant sheaf system in the more general Tag 0A33 statement.

The section formula does not require the intersection to be an open subscheme, affine, or nonempty. In particular Mathlib's affine-transition limit theorem is not a leaf for this item: arbitrary quasi-compact open inclusions need not be affine, and the subspace with inverse-image sheaf has not been assumed to be a scheme.

Whole-DAG and blueprint searches used tools/blueprint_refs.py ancestor and searches for sections intersection, spectral, and quasi-separated, with text searches by section-equation, tags 0A31/0A32/0A33/094L and inverse-image/underlying-set/filtered-colimit notions. They located existing nodes that cover every non-elementary tool. The same_as list remains empty: no imported blueprint node states this section formula in another form.

Retained the existing item's search record and read its reported hits before searching with two broader phrasings using the required msearch.py. The six new logged searches are two LeanFinder queries, one LeanSearch query, one Loogle query, and two Mathlib grep queries. All services responded successfully; no unavailable service was turned into a negative result. The affine-transition results, finite-union sheaf formulas, stalk and skyscraper results do not state the item. I opened Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean at exists_appTop_π_eq_of_isLimit (842) and nonempty_isColimit_Γ_mapCocone (961): both require affine transition maps and an actual scheme limit. Search queries in the JSON are exactly those logged; inherited queries remain inherited.

## Not duplicates

No new nodes. The existing lem-weil-pbc-spectral-limit-pullback-sections is deliberately reused as the general tool. The existing lem-weil-pbc-spectral-limit-sheaf-sections is the more general abelian sheaf-system variant; no second copy or specialization is introduced.

## Review by Q18

I read more-groupoids.tex from section-ind-quasi-affine through equation-sections-of-intersection and the Tag 0APJ argument; topology.tex Tag 0A31 (lemma-make-spectral-space); sheaves.tex Tags 0A32/0A33 (lemma-compute-pullback-to-limit and lemma-descend-opens), 0087 (lemma-sheafify-presheaf-structures) and the inverse-image sections; properties.tex Tag 094L (lemma-quasi-compact-quasi-separated-spectral); schemes.tex Tag 01KO (lemma-characterize-quasi-separated); and categories.tex 04AX with its explicit filtered-set-colimit equivalence relation. I opened and read the statement of every cited node. There are no new-node sources to review. In particular I did not cite the etale-site-only ring sheafification node for a statement about topological spaces; the existing topological-space version explicitly includes the required underlying-set and unit assertion.

Step 1 uses both directions of lem-weil-pbc-quasi-separated-affine-cover-criterion: affine opens of U_i are affine opens of X, so clause (1) gives their compact intersections and clause (2) proves U_i quasi-separated. Its quasi-compactness is an original hypothesis, so lem-weil-pbc-qcqs-scheme-spectral applies exactly. Finite-intersection refinement uses finite affine covers of the original compact opens and the very same affine-intersection clause, not the false assertion that their overlaps are affine. The bounded family J is a set of actual distinct opens, rather than an unproved small category or a possibly large collection.

Step 2 uses the definition def-weil-spectral-space only for compactness of the intersection of two compact opens inside the compact spectral ambient Y. A compact open of an open subspace is a compact open in Y, because the topologies and covers agree. The rest is an elementary verification of the limit: common refinements force equality of compatible coordinates, and the projection to Y determines the initial topology. This does not presume compactness of the original X or a scheme structure on E.

Step 3 uses def-weil-pbc-topological-inverse-image for the actual presheaf formula and sheafification unit; lem-pc-filtered-colimit-commrings-elementwise gives both representative existence and equality at a common stage for that ring colimit. Its hypotheses are met because the open neighbourhoods of h(W) form a set, contain Z, and are closed under finite intersection. lem-weil-pbc-filtered-colimit-sets-elementwise gives exactly the same representative/equality test for the set colimit. The canonical map is consequently bijective; it agrees with all coprojections and restrictions. The last sentence of lem-weil-pbc-ring-sheafification-space-underlying-abelian explicitly gives underlying-set sheafification with theta. These facts justify the passage from the actual ring inverse image to the sets theorem including its unit. This is a short composition of cited statements, not a new unsupported inverse-image theorem.

Step 4 uses the inverse-image formula: an open W of an open subspace is open in the ambient space and is the terminal neighbourhood index. Therefore its presheaf inverse image is restriction and is already a sheaf. The sheafification definition gives the unique resulting isomorphism. The cited lem-weil-pbc-sets-inverse-image-composition states the unit equation, not just existence of some composition isomorphism. That equation identifies the maps from sections on V_j with precisely rho_j and the transitions with restrictions; Step 3 identifies these with the underlying ring maps. Thus neither an arbitrary comparison map nor an unproved scalar-forgetting compatibility is substituted.

Step 5 instantiates the exact statement of lem-weil-pbc-spectral-limit-pullback-sections, not its proof. J is nonempty, small and directed, each V_j is spectral, the transitions are spectral by Step 2, and the limit has both the required points and the required initial topology. The fixed stage and compact open are Y itself. Clause (b) is exactly the local-to-stage lifting needed for (a), after Step 4's unit identifications. Step 6 separately chooses Y=U_i for the given two sections; clause (c) then gives equality at a smaller original open. Its index and maps match, so no unproved cofinality theorem is being used to infer (b).

Step 7 cites the exact elementwise colimit-of-sets criterion and writes out why two representatives at different stages can first be brought to one stage and then made equal. The algebraic universal properties are proved directly: a compatible cocone defines a map on sections by representatives, eventual equality proves independence, and a common stage proves addition and multiplication compatibility by the displayed formulas. The universal property in def-weil-pbc-category-colimit then gives the canonical isomorphisms in each category. This step is elementary relative to the already proved (a),(b), and hides no algebraic forgetful-functor theorem.

Step 8 checks the square on each open-neighbourhood representative before sheafifying, then uses uniqueness in the sheafification and colimit universal properties. This is the naturality of the specified rho-induced map, not merely the existence of some natural bijection. The cited definitions provide exactly these maps and uniqueness. The same equation on the original ring-valued representatives proves all three naturality claims.

For E empty, the topological continuity lemma still applies and gives eventual vanishing of differences; the section ring is the zero ring. If one U_i is empty this is immediate at that stage. The singleton and repeated-open families reduce to restriction and identity without altering clauses (a),(b). For a non-quasi-compact X, all spectral uses are confined to the chosen Y. Constant families, the zero ring, finite-intersection refinement and the original index labels were checked as well. All eight steps are below 2000 characters. I checked B1-B10, C1-C8, D1-D5 and E1-E7: no new nodes, no hidden lemma exported as a restatement, no missing smallness hypothesis, no unsupported assertion that affine overlaps are affine, no cycle through a user of the item, and no SGA citation. During self-review I made the source place precise, ensured all inverse-image identifications retained the canonical units, specified nonempty finite intersections when refining a family in a non-quasi-compact ambient scheme, and corrected the report to count its 17 citations accurately.

Two generic off-unit tools are declared in split_report.tool_uses: the fixed-sheaf spectral continuity theorem and set inverse-image composition. They are used as general topological tools for the source's equation, not as replacements for any unit's argument. Every other cited tool is already a Mathlib leaf. citations.json copies the exact relevant node statements (including all 17 step-to-node pairs) so the independent reviewer can check this signature against the files.

## Validation

The server review_split check passed with 0 new nodes. The first full deliver.py --no-push passed at ed45090468; a final dry run checks the small exposition and citation-count corrections before direct delivery. The local quote-only verification found all 17 quotation strings verbatim in the current cited statements; this was not a local invocation of any server-only check.

## Unfinished work

None in this one-level split. No Lean files, compiler commands, local validation tools or live project files were written or run. The dry run and direct delivery are performed with the authorized launcher tools after this report is written; their exit status determines the final answer.
