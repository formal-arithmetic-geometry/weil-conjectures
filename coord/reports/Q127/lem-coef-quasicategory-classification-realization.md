## Files written

- `dag/nodes/sec-six-functors/lem-coef-quasicategory-classification-realization.json`: existing statement node, now split into six proof steps; no exact Mathlib match.
- `citations.json`: one verbatim statement quotation for each of the fourteen step/node citations.

## New nodes

None. No new Mathlib leaves. The existing Mathlib leaf `lem-coef-inner-anodyne-pushout-product` is reused.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `Comparator` by the exact blueprint id found no declaration. Searches for quasicategory, classification, and realization found no declaration stating all clauses of this item. The upstream master checkout is reference material only and is not used as an attachment.

## Sources and wanted documents

WANTED: André Joyal and Myles Tierney, *Quasi-categories vs Segal spaces*, Proposition 1.16, Lemma 1.21, Propositions 4.9–4.10, printed pp. 283–284 and 301, for `lem-coef-quasicategory-classification-realization`. Read online at https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/joyal-tierney.pdf; not archived under literature/.

WANTED: Jacob Lurie, *Higher Topos Theory*, Remark 3.1.3.1 and Proposition 3.1.2.3, for the marked mapping-core interpretation used by `lem-coef-quasicategory-classification-realization`. Read online at https://www.math.ias.edu/~lurie/papers/HTT.pdf; not archived under literature/.

I did not download files or modify literature. The proof is marked `proof_origin.by = agent` because it expands the online reference through existing DAG interfaces, especially the explicit boundary-parameter lifting problem and induction comparing strict with path-model pullbacks. No Stacks tag states this quasicategorical theorem; no Stacks tag or SGA source is claimed or used.

## Findings and changes

The imported statement is correct and is unchanged, as are its statement dependencies. Its empty proof was the work to supply. In particular its evaluation-map clause asserts only a natural simplicial map, and I have not used the parent's later evaluation weak-equivalence argument to prove anything here.

The nearest blueprint ancestor is `prop-coef-integral-exceptional-adjoint`; I read its main-20261015 proof paragraph 2 and the recorded chapter and `sk-prop-sf-biduality-general` unit. The item retains the historical unit/ancestry of its parent chain. The classification-space foundation implements that chain and does not replace a geometric unit step. Whole-blueprint searches for classification, Segal, core, and the combined classification-diagram phrase found no matching blueprint node; `blueprint.same_as` remains empty and its existing precise `from.place` is retained.

I initially considered extracting a generic core-fibration lemma. Opening `lem-coef-marked-anodyne-lifting-calculus` showed that its statement already gives exactly the required restriction fibration, so I created nothing. I also avoided citing the complete-Segal/quasicategory equivalence as a substitute for the actual argument. The proof instead writes the Segal restriction lifting problem and the strict-to-homotopy comparison out.

## Mathlib searches

The six new records appended to the item are actual `msearch.py Q127 lem-coef-quasicategory-classification-realization` runs: two LeanFinder phrasings, Loogle, two grep searches (one scoped to AlgebraicTopology/Quasicategory), and LeanSearch. Full outputs are preserved in `search-results.json` and the command's own `searches.jsonl`. Every service succeeded; none is recorded unavailable.

The hits are strict Segal structures of a single simplicial set, nerves of ordinary categories, and the definitions/instances for quasicategories and Kan complexes. I read `Mathlib/AlgebraicTopology/SimplicialSet/StrictSegal.lean` lines 40–62 and `Mathlib/AlgebraicTopology/Quasicategory/Basic.lean` lines 35–61. They do not state the bisimplicial classification-space theorem. I also read the existing pushout-product Mathlib declaration `SSet.innerAnodyneExtensions_pushoutObjObjι'`, `Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Inner/PushoutProduct.lean` lines 103–109; it is the generic fact already carried by `lem-coef-inner-anodyne-pushout-product`, not an attachment of this item.

## Tool uses

`lem-cbc-spine-inner-anodyne` belongs to another unit and is declared in `split_report.tool_uses`: it supplies the generic combinatorial spine theorem used by the explicit pushout-product argument. The item's unit has no theorem stating it. Definitions are notions and the pushout-product theorem is already a Mathlib leaf; the other cited lemmas are in the item's unit. No maintainer-owned top-level `tool_uses` was added.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs to justify. I searched the whole DAG for core restriction fibrations, strict mapping fibers, spines, classification diagrams and complete Segal spaces. I opened the marked lifting calculus, spine theorem, pushout-product leaf, complete-Segal/quasicategory comparison, isofibration-exponentiation node, endpoint-arrow lemmas, fixed-vertex composition-spine node, and the two Kan pullback nodes. The stronger comparison node is not an exact duplicate of the item: it states an equivalence of infinity categories and homotopy mapping fibers, whereas the item specifies a concrete bisimplicial object, strict endpoint fibration/fiber and a diagonal map.

## Review by Q127

I read delivery-errors B–E whole and checked the item against them with each used node's statement open. There are no new statement-only or definition nodes, so B1–B8's new-node concerns and new-statement small-case tests do not arise. The existing statement introduces Q, all simplicial parameters and the strict fiber; its two statement dependencies really define its notions. TeX is written once. All original provenance, created and blueprint fields are retained. The item has no own slopmaster2 audit/declaration record, and the project-source searches found no exact attachment. Every newly recorded Mathlib query actually ran through the prescribed command, including a second phrasing before the absence verdict.

Step 1 uses `def-cbc-enhanced-diagrams-cones` for simplicial operators, products and inverse-triangle equivalence witnesses. I checked that precomposition at a new vertex uses the old vertex alpha(i'), and that postcomposition sends the actual inverse witnesses to inverse witnesses. This is elementary and is marked so. It gives the bisimplicial structure before any fibrancy assertion is used.

Step 2 uses that definition and `lem-coef-marked-anodyne-lifting-calculus`. The latter's statement explicitly defines the coordinatewise product marking and Map-flat/Map-sharp, states that Map-sharp is the Kan core of Map-flat, and states that restriction along a degreewise injection is a Kan fibration. Thus it says precisely what this step takes from it (C4). For X=K-flat, Map-flat has no nonautomatic marking restrictions; Map-sharp marks exactly the parameter edges at each fixed vertex. This is an equality of actual simplicial subsets, not only an equivalence of homotopy types. The hypothesis C quasicategory holds for Q, and the endpoint inclusions and the individual endpoint inclusions are all degreewise injections. This proves columns Kan, the core equalities and both endpoint fibrations without an uncited general statement that cores preserve fibrations.

Step 3 uses the definition, `lem-cbc-spine-inner-anodyne`, `lem-coef-inner-anodyne-pushout-product` and `lem-coef-kan-quillen-right-proper`. I checked the spine statement's inclusion and its lifting-class convention, the pushout-product statement's two hypotheses (inner-anodyne spine and degreewise injective boundary), and that Q to a point is an inner fibration by Q's own definition. The domain of the lift is written exactly as the union of spine times parameter simplex and full simplex times parameter boundary. Every horizontal vertex is in the spine, so every required vertical-equivalence edge is fixed before extension; no theorem about extensions preserving equivalences is smuggled in. At parameter dimension zero the boundary is empty and the same argument works. The Kan-model statement explicitly identifies boundary lifting, including dimension zero, with trivial fibrations. This proves the actual consecutive-edge Segal restriction, not a replacement map or merely a fiberwise abstract equivalence.

Step 4 uses `lem-coef-kan-pullback-path-comparison`, `lem-coef-kan-homotopy-pullback-invariance`, `lem-coef-kan-quillen-right-proper`, and the homotopy-Segal definition in `lem-coef-segal-dk-diagonal-equivalence`. I read all four statements: the first supplies exactly the constant-path comparison for Kan inputs when one leg is a Kan fibration; the second supplies invariance for strict commuting squares with all three comparison maps weak equivalences. The induction starts with E, keeps the last-edge endpoint strictly, and in each step uses the source fibration proved in step 2. Kan-ness of the strict pullback is checked by horn lifting in the base followed by horn lifting against that source map; Kan-ness of the path pullback is in the cited statement. The induction's invariance squares strictly commute because the previous comparison retains the last edge, not merely its homotopy class. Thus the resulting map inserts precisely the constant paths required in the homotopy-Segal node; it does not use the Dwyer–Kan conclusion of that node.

Step 5 uses only the definition and the exact path-comparison statement. I checked that a simplex of the fiber has entire endpoint faces constant, rather than merely their vertices equal to x,y. Such faces have degenerate equivalence edges, so every simplex in the displayed un-cored arrow fiber belongs to the column core; this proves equality in every degree. The endpoint map is a Kan fibration by step 2, both source and base are Kan, and the chosen pair of vertices gives a map from the Kan point. These are precisely the path-comparison hypotheses. The comparison is the canonical constant-path map to the homotopy fiber; no right-pinched/arrow-space equivalence is needed.

Step 6 is elementary using the simplicial definition: I wrote the equation intertwining the two diagonals with every monotone alpha and checked that postcomposition commutes with restriction. This proves the precise e_Q of the statement and its naturality. Its being a weak equivalence is neither assumed nor asserted by the item.

For E1–E6 I tested the empty Q, the point, a discrete two-object category, N([1]), and a one-object groupoid with a nontrivial automorphism. For empty Q all columns are empty and every existing lifting problem is vacuous; there is no false dimension-zero nonemptiness assumption. At the point all maps and fibers are points. For N([1]), U(0,1) is a point and U(1,0) is empty: endpoint Kan fibration does not mean surjective on vertices. In the groupoid the vertical equivalences include nonidentity edges, so step 2 must use minimal marking on the shape and full marking only on the parameter; it does. These tests also confirm that the fiber equality needs constant endpoint simplices and that the Segal products match target to source in order. I found no statement dispute, missing hypothesis, unproved transport compatibility, or source error. The only off-unit statement is the explicitly declared generic spine tool. A direct dependency traversal found no path from any new proof dependency back to this item; the server check remains the required graph authority.

The main correction during self-review was to keep the strict Segal product separate from its path-model version and write the induction and the strictly commuting last-endpoint squares out. I also replaced a potential duplicate core-fibration child with the existing marked calculus. Each step's uses union is exactly proof_deps, and `citations.json` contains a quotation verified as a substring of each cited node's statement. No fact is borrowed from a cited node's proof instead of its statement. No Lean was written and no compiler or build command was run.

## Unfinished work

No mathematical clause remains. Remote check_dag passed with no finding introduced by the sandbox or on its nodes. Remote review_split returned PASS with 0 new nodes and the declared spine tool use. The required deliver.py --no-push dry run printed OK (not pushed), preflight passed, at 129d661434. The report records that successful run; the same no-push command is repeated after this report-only update to validate the final sandbox. The second reader is responsible for independent review and actual delivery.

## Second reading by Q127

- Step 1: checked the bisimplicial operators and naturality against `def-cbc-enhanced-diagrams-cones`; verdict PASS, with the equivalence-witness argument explicit.
- Step 2: checked the marked mapping-core identification, Kan columns, and endpoint fibrations against `def-cbc-enhanced-diagrams-cones` and `lem-coef-marked-anodyne-lifting-calculus`; verdict PASS.
- Step 3: checked the spine restriction, pushout-product lifting problem, dimension-zero boundary case, and trivial-fibration conclusion against `lem-cbc-spine-inner-anodyne`, `lem-coef-inner-anodyne-pushout-product`, `lem-coef-kan-quillen-right-proper`, and the definitions; verdict PASS.
- Step 4: checked the strict-to-homotopy pullback induction and its strictly commuting endpoint maps against `lem-coef-kan-pullback-path-comparison`, `lem-coef-kan-homotopy-pullback-invariance`, and `lem-coef-segal-dk-diagonal-equivalence`; verdict PASS after replacing an overbroad citation of weak-equivalence composition by the direct realization argument.
- Step 5: checked the strict endpoint fiber equality and homotopy-fiber comparison against `def-cbc-enhanced-diagrams-cones` and `lem-coef-kan-pullback-path-comparison`; verdict PASS.
- Step 6: checked diagonal restriction and naturality directly from simplicial operators and `def-cbc-enhanced-diagrams-cones`; verdict PASS.
- New nodes: none; no B1–B8 new-node review applies, and no Mathlib leaf was added.
- Changes made: corrected the item node's stale `created.item` and `created.group` metadata to this delivery; removed the step-4 citation claiming that `lem-coef-kan-quillen-right-proper` states composition closure; added the direct realization proof of closure; updated `citations.json` accordingly.
- Small cases checked: empty quasicategory, point, discrete two-object category, nerve of `[1]`, and a one-object groupoid with nontrivial automorphism; no statement dispute found.
