# Q81 stage-1 split: lem-coef-pattern-generator-product-cells

## Files written

- `dag/nodes/sec-six-functors/lem-coef-pattern-generator-product-cells.json`: item, statement unchanged, split into fourteen proof steps covering the fourteen generator/cofibration-generator cases, the two slice orientations and sharp left-anodyne maps.
- `dag/nodes/sec-six-functors/lem-coef-pattern-marking-cancellation.json`: statement, unsplit; no Mathlib match. The two auxiliary marking inclusions are HA B.1.11 and B.1.12, with their seven generating families written out so that this node does not depend on its own ancestor.
- `dag/nodes/sec-six-functors/lem-coef-relative-join-prism-comparison.json`: statement, unsplit; no Mathlib match. An unmarked relative join-prism comparison, with a specified intermediate subcomplex and final pushout, used by both cone generator cases.
- `dag/nodes/sec-six-functors/lem-coef-inner-horn-cell-generation.json`: statement, Mathlib leaf. Exact declaration `SSet.innerAnodyneExtensions_eq_retracts_transfiniteCompositions`, `Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Inner/Basic.lean:89` (read lines 35-100).
- `citations.json`: verbatim statement quotations for every proof-step citation.
- `searches.jsonl` and the search result text files: real msearch requests and results. The searches were run only through the required launcher command; successful services and zero-hit requests are recorded honestly.
- `small-prisms.txt` and `check_small_prisms.py`: 54 finite nerve examples checking the new join comparison's pushout union/intersection and finding explicit inner horn filtrations. These are finite combinatorial checks, not Lean files or compiler runs.

## Attachments

None. Searches for the exact blueprint tag and for categorical-pattern, pattern-anodyne and marked-anodyne terminology under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` found no project declaration of the item or either auxiliary assertion. The existing Mathlib unmarked pushout-product declaration is used through its existing DAG leaf; it is not reported as a project attachment. The upstream master checkout was consulted only as read-only reference material.

## WANTED

WANTED: Lurie, *Higher Algebra*, September 18, 2017, Definition B.1.1, Proposition B.1.9 and Lemmas B.1.11-B.1.13, printed pp.1470-1481, for the item and lem-coef-pattern-marking-cancellation and lem-coef-relative-join-prism-comparison. The PDF is not archived in the named literature directory. I read it online at https://people.math.harvard.edu/~lurie/papers/HA.pdf using the web reader; no source was downloaded into the project or sandbox. Consequently the item's proof is marked agent-written. The join comparison is explicitly an agent formulation of the relative filtration used by the two cone-product cases, not a falsely attributed numbered proposition.

## Problems found and corrected

The item arrived with a complete statement and searches but no proof, no Lean audit attachment and no split. There was no earlier sandbox node or report to reuse. The statement is faithful to HA's fully scaled point-pattern specialization and did not require correction. There is no STATEMENT-DISPUTED.

A proof by citing the existing pattern-anodyne lifting-products theorem would be circular: that theorem depends on this item. Likewise I did not appeal to the categorical-pattern model structure or its trivial-cofibration assertions. The proof constructs the cells.

The existing unmarked inner pushout-product node defines inner anodyne by lifting against inner fibrations; a closure-of-horns argument needs a separate equivalence. I added the exact Mathlib leaf for this equivalence, rather than silently changing the meaning of inner anodyne.

For the initial-horn product I use the already existing initial prism filtration with the explicit marked first edge. This avoids relying on the very abbreviated retract comparison printed in the C0-prime case. The nontrivial join-prism comparison was extracted instead of being hidden in the long cone-product steps. The extra marking inclusions are also separate statements; none of the new nodes asserts a generator product or sharp left-anodyne clause of the item.

The product with the point pattern has the original pattern's cones and no additional cones; no finite cone approximation, small-index-category substitution or change of coefficients is made. The blueprint ancestry and its entire via chain are retained. The current ancestor proof's displayed finite-coefficient adjunction is the same technical location specified in the inherited blueprint field. Chapter and unit records are unchanged.

## Not duplicates

lem-coef-pattern-marking-cancellation vs lem-coef-pattern-anodyne-lifting-products: the existing ancestor gives product stability and mapping-space lifting, but does not state either of these marking-only cancellation inclusions; citing it would also create a cycle.

lem-coef-pattern-marking-cancellation vs lem-coef-infinity-cocartesian-composition-initiality: the existing node proves cancellation for cocartesian edges of a quasicategorical inner fibration; the new node asserts membership of explicit marked maps in a syntactically generated weakly saturated class, without a model structure or a given fibration.

lem-coef-relative-join-prism-comparison vs lem-coef-infinity-pushout-join-saturation: the existing node only supplies separate-variable saturation for join pushout products; it does not compare the specified join with a Cartesian prism or give this final pushout square.

lem-coef-relative-join-prism-comparison vs lem-coef-infinity-right-prism-boundary: the existing node is the interval-times-simplex shuffle filtration with no join factor; the new comparison is for arbitrary A subset B and arbitrary K, has an inner-anodyne first stage, and a separate final join attachment.

lem-coef-inner-horn-cell-generation vs lem-coef-infinity-pushout-join-saturation: that statement defines inner anodyne using weak saturation but does not identify it with the lifting class used in the existing inner pushout-product leaf. The new Mathlib leaf supplies exactly this missing equivalence.

lem-coef-inner-horn-cell-generation vs lem-coef-inner-anodyne-pushout-product: the existing leaf is a Cartesian product theorem and does not give a horn-cell presentation of its lifting-class conclusion.

Whole-blueprint searches for `anodyne`, `pattern generator products sharp left-anodyne`, `marking cancellation`, `join product` and `inner horn generation` returned no equivalent blueprint node. Whole-DAG statement/key-word searches and the source searches were inspected before writing the new nodes. No Stacks tag states these marked simplicial or infinity-categorical facts; the source places explicitly say so instead of inventing tags.

## Review by Q81

I read the worker brief, delivery-errors B-E in full, stage-1 rules, the three levels of SETUP, GOAL, dag-sync, the chapter and unit, and the main-20261015 ancestor proof. The unit's route is not replaced. The only off-unit tool is `lem-cbc-initial-prism-horn-filtration`; `split_report.tool_uses` explains that it is an explicit generic horn filtration unavailable as a statement in this unit.

For sources, I read HA Definition B.1.1 (all seven generating families), Definition B.1.8 (product pattern), the complete fourteen-case proof of B.1.9, the statements and proofs of B.1.11 and B.1.12, and B.1.13 including its n=1 and n=2 exceptions. The new marking node states exactly B.1.11 and B.1.12 under full scaling, with all target marked edges mapping into S. For the new join node I checked the actual subcomplex descriptions and the final join attachments in the two cone cases; I made the relative boundary explicit and tested both the intersection and union claims in the small examples. For the new Mathlib node I read the declaration at lines 89-92 and the lifting-class definition at line 43; it is the exact cell-class equality, not a claim inferred from the semantic search hits. The two non-leaf new nodes have no proof or proof dependencies and do not hide sketches inside their statements.

I opened and read the full statement of each cited node, not merely its title. Step 1 takes the boundary-cell pushouts from `lem-coef-infinity-monomorphism-boundary-cells`, and the marking/product conventions from `lem-coef-marked-point-cartesian-model`. It spells out how markings are added and how quotient relations persist under products. Step 2 uses the precise lifting-to-cell equality of the new Mathlib leaf; flat marking then preserves the displayed constructions by their universal properties. No model-structure assertion is needed.

Step 3 explicitly marks each missing cross edge with one A0 triangle; its structural triangle is a degeneracy of a marked edge. Step 4 uses only clause (i) of the new marking node after an explicit A0 triangle. Step 5 uses only clause (ii), after marking the cone diagonals by A0; the specified final subcone really is p_alpha, even when K_alpha is empty. Step 6 checks all marked target edges occur in the source for each C-family; the n>=1 assumption in C2 is essential here. Step 7 uses that every vertex is in the boundary for m>0; m=0 was separated first. These arguments use only the given generator definitions.

I additionally read Kerodon 00TH and 01DN online, including their proofs: the former gives the precise interval shuffle pushouts, and the latter explicitly fixes the first two vertices in every initial-horn cell. Step 8 uses the exact pushout and simplex formula of `lem-coef-infinity-right-prism-boundary`, after reversing both factors. The new horn index is m-q, so only the last cell is initial; its vertical marked edge is over vertex 0. Step 9 uses the actual pushout statement and endpoint condition of `lem-cbc-initial-prism-horn-filtration`, with n>=2, exactly the hypothesis of the C0 generator. Its initial edges map into S; every target marked edge was already in the source. Step 10 uses precisely the product assertion of `lem-coef-inner-anodyne-pushout-product`, and step 2 converts its lifting convention. There is no unnoticed fibrancy assumption.

Step 11 cites both substantive clauses of the new join comparison: the inner-anodyne D-to-Z inclusion and the explicit final pushout. The substitutions are (A,B)=(empty,Delta^0) for B1 and (boundary Delta^n,Delta^n) for C2. Step 12 uses only the explicit boundary-cell theorem; the final-vertex argument is written out: surjectivity of each monotone coordinate forces the final corner, with d>=1 since m>0. Its subcone is already present and marked, and maps to p_alpha. Joining the relative cells preserves their degreewise pushout presentation; I spell out the leading/final-block reason. Hence the final attachments are genuinely C2 maps, rather than an unexplained use of product stability.

Step 13 explicitly checks the base maps for the opposite slice orientation. For a flat boundary factor of u, marked edges and the first edges of initial horns are constant over C. For a marking factor they project to its marked base edge. All the five h-families, including A1 and C0 in dimension 2, are accounted for. It does not assert pullback stability of W_0. Step 14 checks n>2, n=2 inner, n=2 initial and n=1 separately; the cancellation citation states the extra edge-marking inclusion used in the initial triangle. Sharp marking then preserves the actual colimit and retract constructions. Every such citation has a verbatim entry in citations.json.

I checked small and empty cases for every new statement. The marking node's empty family gives only the triangle assertion; its empty cone gives the required interval-marking assertion, reflecting the terminal-object cone condition rather than deleting it. Degenerate base edges are allowed and remain in S. The join node permits empty A,B,K and m=0: for K empty its first stage is an identity and the final pushout is the ordinary relative product; for B empty D=T; for m=0 Z=D and the last square is the identity attachment. The 54 finite-nerve examples cover B=Delta^0,Delta^1,Delta^2, K empty/Delta^0/Delta^1, m=0,1,2, and A empty or boundary. Every example satisfies the asserted pushout union/intersection and admits the computed inner horn cell sequence. These are checks, not a substitute for splitting the new non-elementary statement later. The inner-horn leaf has no extra fibrancy, connectedness or nonemptiness hypothesis.

No proof step exceeds 2000 characters. The join comparison and marking completion were extracted because they have independent hypotheses and conclusions; the remaining relative-cell and base-map calculations are routine explicit uses of their cited statements. I checked B-E for self-contained statements, correct sources, exact Mathlib leaf matching and genuine logged searches, correct blueprint ancestry, no circular proof dependencies, no clause relabelling and no unstated non-elementary input.

## Unfinished work

The two new non-Mathlib nodes are intentionally unsplit, as required for a one-level split. Their mathematical proofs are future items. No Lean was written, no compiler or Lake command ran, no git command ran in the shared repository, and nothing was pushed. The accepted sandbox is to be read and delivered by the fresh second worker.

## Dry run

The required command is `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q81 lem-coef-pattern-generator-product-cells --no-push`. The final READY handoff is made only after that command prints OK. No push is authorized or requested.

## Second reading by Q81

- Statement: checked HA Definition B.1.1, Proposition B.1.8 and Proposition B.1.9 against every generator, scaling, base-map and empty-cone clause; verdict faithful, including C0's marked 01 edge condition and the fully scaled 2-simplex condition.
- Step 1: checked against `lem-coef-infinity-monomorphism-boundary-cells` and `lem-coef-marked-point-cartesian-model`; the boundary-cell and marking-only filtration and pushout-product closure are explicit; verdict correct and elementary.
- Step 2: checked the exact Mathlib leaf and both lifting/cell directions; flat marking and weak saturation are used as stated; verdict correct and elementary.
- Step 3: checked HA B.1.9 (A0),(A1) against the coordinatewise product marking; the degeneracy triangle has an allowed base; verdict correct and elementary.
- Step 4: checked HA B.1.9 (B0) and B.1.11; the two triangle attachments and their marked base edges are accounted for; verdict correct.
- Step 5: checked HA B.1.9 (B1) and B.1.12, including empty $K_\alpha$; the cone map restricts to $p_\alpha$ and all required edges lie in $S$; verdict correct.
- Step 6: checked the three C cases directly from their marked subobjects and $n\geq1$; the underlying map is an isomorphism; verdict correct and elementary.
- Step 7: checked the $m=0$ and $m>0$ A cases against the product marking; all vertices of a positive boundary are present; verdict correct and elementary.
- Step 8: checked HA B.1.10 and `lem-coef-infinity-right-prism-boundary`; repaired the marking explanation so each shuffle's nondegenerate marked edge is already in its horn, while only the final cell uses C0; verdict correct after repair.
- Step 9: checked `lem-cbc-initial-prism-horn-filtration` statement, its endpoint condition, and the C0 product source; the first marked edge is the specified 01 edge and all target marked edges are already present; verdict correct.
- Step 10: checked `lem-coef-inner-anodyne-pushout-product` and the Mathlib lifting convention; the flat product is exactly its pushout product; verdict correct.
- Step 11: checked both clauses of the relative join comparison under $(A,B)=(\varnothing,\Delta^0)$ and $(\partial\Delta^n,\Delta^n)$; all product-marked edges lie in $D$ because every vertex of $\Delta^m$ is in its boundary; verdict correct after making that point explicit.
- Step 12: checked the boundary-cell decomposition and the final-corner argument for both cone cases; each attachment is a C2 cell with the final subcone already marked; verdict correct.
- Step 13: checked HA B.1.8's point-pattern specialization and both coordinate orientations; all five cone-free families and their base-map conditions are covered; verdict correct.
- Step 14: checked HA B.1.13 for $n>2$, both $n=2$ horns and $n=1$; sharp marking preserves the stated colimit/retract constructions; verdict correct.
- `lem-coef-pattern-marking-cancellation`: checked HA B.1.11 and B.1.12 clause by clause, including full scaling and empty cones; verdict is a necessary unsplit auxiliary statement, no duplicate found.
- `lem-coef-relative-join-prism-comparison`: checked its degreewise join definitions, $D\subseteq Z$, canonical map and pushout on 54 finite nerve cases; verdict is a necessary unsplit auxiliary statement, no Mathlib or blueprint match.
- `lem-coef-inner-horn-cell-generation`: checked the declaration and definitions at Mathlib `Inner/Basic.lean` lines 43 and 89–92; verdict exact Mathlib leaf.

Changes made: repaired Step 8's prism-marking sentence (the marked shuffle edge lies in the attaching horn rather than always in the initial boundary), made Step 11's boundary-vertex marking justification explicit, refreshed the corresponding citation record, and retained the declared initial-prism tool use. No statement, node status, dependency, source, or blueprint field was changed. The finite-prism check still passes all 54 examples. No Lean, compiler, Lake, or git command was run.
