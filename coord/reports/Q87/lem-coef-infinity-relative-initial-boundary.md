# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-relative-initial-boundary.json`: statement, split; no Mathlib match. The statement is unchanged. Six proof steps use only existing nodes.
- `citations.json`: one verbatim statement excerpt for every citation in every proof step.
- `report.md`: this report and the signed self-review below.
- `searches.jsonl` is the search command's own log; `write_split.py` is sandbox-only preparation code, not a delivery file.

## New nodes

None. There are zero new nodes and zero new Mathlib leaves.

## Attachments

None. The exact blueprint id and the notions `relative.initial`, `relative.final` and `RelativeInitial` have no matching declaration under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`. A broader source search for initial objects and slice/overcategory fibrations found ordinary category results and six-functor applications, not this quasicategorical boundary criterion. No master sorry declaration is counted as a proof.

## WANTED

WANTED: archival copy of Kerodon Corollary 7.1.5.17 (02WS) and Proposition 7.1.5.16 (02WR), for the item. Read online at https://kerodon.net/tag/02WS and https://kerodon.net/tag/02WR.

WANTED: archival copies of Kerodon Corollary 4.3.6.9 (01C0), Proposition 4.3.6.1 (018F), Proposition 4.6.5.10 (01L5), Corollary 4.4.3.8 (01NV), Proposition 3.3.7.6 (00ZP), and Proposition 4.4.2.14 (01NU), for the existing generic inputs and the expanded proof. Their tags are Kerodon identifiers, not Stacks tags. Stacks has no corresponding quasicategorical relative-initial theorem. The trivial Kan fibration definition is available in `literature/stacks-project/simplicial.tex`, label `definition-trivial-kan`, Stacks tag 08NL, lines 5533-5545.

## Corrections and route

No statement dispute and no statement correction. The item had no proof. Its definition of relative initiality, its hypotheses (inner fibration, both categories quasicategories), its exact lifting equations, and its exclusion of dimension zero agree with Kerodon 02WS after the natural pinched/unpinched comparison in 01L5. No isofibration hypothesis is added.

The proof is an agent-expanded version of the relative-slice argument. It works first with the final/right-slice case, where the strict fibers are literally the project's right-pinched mapping spaces. It proves the relative slice is a right fibration by identifying a right-horn lifting square with a single inner horn one dimension higher. It then applies existing Kan-fibration and contractible-fiber nodes. This avoids introducing a categorical-equivalence-of-fibrations lemma merely to restate 02WR.

I initially considered adding a general relative slice fibration node and ran real searches for it. I did not create it: the point-slice case needed here is the face calculation in step 2, not a new non-elementary input. The general join theorem `lem-coef-infinity-anodyne-cocones` was inspected as another possible input, but even it is unnecessary. No claim of absence is made for an unrun search.

I read `dag/chapters/sec-six-functors.json`, `dag/units/sk-prop-sf-biduality-general.json`, and the ancestor's current proof in `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.proof.md`. The inherited historical ancestry has no dedicated current-blueprint paragraph for this generic infrastructure; it is retained and explained rather than rebinding the unit. The result supplies the boundary test used by `lem-coef-infinity-parameter-cone-extension`. No chapter/unit statement, realized field, coefficient convention, target or base-change map changes. No SGA source is used.

## What remains

No mathematical part of this one-level split remains. The already existing node `lem-cbc-right-fibration-space-fiber` remains unsplit; it is a genuine generic input, and its statement is all that step 3 uses. The work stops at that existing frontier as required. This worker does not push; the independent second reader receives the accepted sandbox.

## Not duplicates

No new-node pairs require approval. Before deciding against new nodes I searched all `dag/nodes` for relative initial/final objects, right/left fibrations, relative slices, 02WS, 02WR and 01C0, and used `tools/blueprint_refs.py search` for `left fibration`, `slice mapping`, `relative slice`, `01C0`, `slice`, `relative initial` and `boundary`. The general slice projection, right-pinched fibers, right-fibration-over-space theorem, and fiber criteria are already represented. The Stacks 01C0 occurrence in `lem-weil-pbc-coherent-local-isomorphism` concerns coherent modules and is unrelated to Kerodon 01C0. I read all candidate statements before choosing the existing inputs. Nothing restating an item clause is introduced.

## Review by Q87

I checked the unchanged item against Kerodon 02WS (all three conditions and its proof), 02WR (the slice comparison and its fiberwise explanation), and 01L5 (natural mapping-space model comparisons). The item is the positive-dimensional boundary criterion for an inner fibration, including exact equality of the projection and the full boundary restriction. The proof does not assume that a relative initial object is an ordinary initial object. The diagram is not assumed to have any extra colimits or limits. I also read 018F, 01C0, 01NV, 00ZP and 01NU online and Stacks' actual `definition-trivial-kan` in the archived TeX. There are no new-node source statements to review.

Step 1 cites `lem-coef-infinity-slice-right-fibration`, whose statement gives the join model, its simplicial operators, and the exact strict vertex fibers as right-pinched Kan mapping spaces. I checked that its target vertex is x, while the variable first vertex is z. Applied in Y it gives Map_Y(pz,px), not a fiber over a variable object of Y absent from X. `def-cbc-enhanced-diagrams-cones` specifies precisely the same right-pinch convention. The pullback target consists of the initial face in X and a whole simplex in Y agreeing on that face.

Step 2 uses only the cited slice formula and the inner/right horn definitions of `def-coef-infinity-fibrations`. I checked every face: the base face is d_(m+1), and coning the included faces of Lambda_i^m gives exactly all faces except d_i in dimension m+1. Since 0<i<=m, this new horn is inner. The p-filler retains the fixed last vertex and both maps of the q-square. In particular m=1, i=1 becomes Lambda_1^2, so the edge-lifting part of right fibrancy is really proved. This is a two-line consequence of the definitions once the domains are written out; it is marked elementary. It hides no anodyne saturation or equivalence-lifting assertion.

Step 3 cites only the first clause of `lem-cbc-right-fibration-space-fiber`. I opened that node and checked that it assumes exactly a right fibration and a Kan base, and concludes all-horn lifting; its homotopy-fiber comparison is unused. The domain and codomain of q_z are the actual strict fibers from step 1, and pullback stability is written by pairing the prescribed base map with a lifted simplex. The Kan-base hypothesis is supplied by the slice statement, not by a general quasicategory assumption. This off-unit generic tool is explicitly declared in `split_report.tool_uses`.

Step 4 uses the first equivalence in `lem-cbc-kan-fibration-fiber-criterion`: a Kan fibration is a weak equivalence precisely when its vertex fibers are contractible, and precisely when it lifts all boundaries. I verified that step 3 supplies the required Kan fibration before each application. Every vertex (z,alpha) of T indexes exactly one such vertex fiber of q_z. `lem-coef-right-fibration-contractible-fibers` applies because step 2 supplies right fibrancy, and its statement permits an arbitrary simplicial base T; no unsupported claim that T is Kan is needed. For the converse I checked pullback boundary lifting directly, including dimension zero, against `def-weil-pbc-trivial-kan-fibration`. Thus no assertion that a strict fiber is automatically a homotopy fiber is used. The off-unit Kan criterion is declared as a generic tool.

Step 5 cites the slice formula and the whole boundary-lifting definition. I checked the domains degreewise: the first face Delta^m and the cones on all its proper faces form exactly the full boundary in dimension m+1. The new last vertex is x, not p(x); p(x) belongs only to the base simplex. The gluing equations on their intersection are precisely those of the given pullback square. The construction is reversible by restriction. At m=0 the two boundary vertices are prescribed, and the q-boundary problem is its surjectivity problem. Hence dimension zero for q is n=1 for p; no n=0 condition was silently added to the item. This is elementary gluing from the cited constructions.

Step 6 cites the naturality and Kan-space clauses of `lem-coef-infinity-pinch-comparison`, together with the mapping and realization conventions of `def-cbc-enhanced-diagrams-cones`. I did not identify the opposite right-pinch with the original right-pinch. Instead the step compares through U_(C^op)(a,b) = U_C(b,a)^op and the realization homeomorphism given by barycentric reversal. I checked its compatibility with each simplicial operator alpha and with the functor p. This gives commuting comparisons on components and homotopy groups and proves the needed equivalence of mapping-space hypotheses. Inner horns reverse to inner horns, the first vertex reverses to the last vertex, and the reversal is involutive, so both lifting equations are recovered exactly. The step is marked non-elementary because the natural pinch theorem is a real input.

For delivery-errors B I checked that all existing notions used are either stated inline or supplied by actual cited definitions. There are no new statements, proof sketches hidden in new statements, or unsupported Mathlib leaves. The item and the proof use ordinary TeX commands once, with JSON serialization supplying only the necessary escaping. For C I opened every cited statement, generated a verbatim excerpt for each step/citation pair, and checked the hypotheses as described above. The union of step uses is exactly `proof_deps`; no citation relies on a dependency's internal proof. Definitions and generic off-unit tools do not alter the unit's route. For D the item itself carries the slice, lifting, fiber and duality arguments; no clause is delegated to a new node.

For E I tested the identity fibration (q is an identity and every vertex is relative initial/final), the map to a point (the criterion reduces to ordinary initial/final objects), discrete quasicategories (the n=1 condition detects precisely unique available arrow lifts), and the lowest horn and boundary dimensions. Empty mapping spaces are allowed: Map_X(z,x) and Map_Y(pz,px) can both be empty, in which case q_z has empty base and the fiber statements are vacuous; if its base is nonempty but its source empty, neither weak equivalence nor boundary lifting holds. The specified vertex x makes an empty X impossible, without adding a new hypothesis. No nonempty-fiber assumption was inserted. No new statement is left for a small-case test.

Mathlib searches were run only with the supplied command and recorded from its actual log. I read the returned signatures and the pinned `Quasicategory/InnerFibration.lean` and `SimplicialSet/CategoryWithFibrations.lean`. The inner fibration definition, inner-horn fillers, ordinary initial objects, and the Kan generating families do not prove the item. I also read `ModelCategory/Over.lean`: its fibration-on-an-ordinary-overcategory instances are not the relative join-slice assertion. Two semantic phrasings for the item and two for the prospective slice input found no applicable result. No prospective node was created because the special slice fact was proved directly instead.

## Validation

The supplied remote `srvcheck.py` checks returned `check_dag OK: no finding introduced by the sandbox or on its nodes` and `review_split PASS; 0 new nodes`, with the two generic tool uses declared. Final validation command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q87 lem-coef-infinity-relative-initial-boundary --no-push`. The final READY handoff is conditional on that dry run printing OK. No local DAG checker, preflight, compiler, Lake or build tool was run. Only the sandbox was written; no delivery is pushed by this worker.


## Second reading by Q87

- Statement: independently read Kerodon 02WS, 02WR and 01L5 online; checked both quasicategory hypotheses, inner fibrancy, natural mapping-space interpretation, exact projection/restriction equations and n > 0. PASS; no statement dispute or correction.
- Step 1: opened both cited statements and Kerodon 018F; the last-vertex slice and strict fibers are precisely the prescribed right-pinched spaces. PASS, including empty mapping spaces.
- Step 2: checked against the slice formula, inner/right horn definitions and Kerodon 01C0; the domain contains d_(m+1) and every coned face except d_i, hence is the inner horn Lambda_i^(m+1). PASS, including m = i = 1.
- Step 3: opened lem-cbc-right-fibration-space-fiber and read Kerodon 01NV; the explicitly pulled-back right fibration has a Kan mapping-space base, exactly the hypotheses of its first clause. PASS; no use of its homotopy-fiber clause.
- Step 4: opened all three cited statements and read Kerodon 00ZP and 01NU; q_z is already Kan-fibrant, its vertex fibers are exactly the fibers at (z, alpha), and pullback preserves boundary lifting including dimension zero. PASS; no Kan hypothesis on T is used.
- Step 5: checked against the slice statement and Stacks simplicial.tex, label definition-trivial-kan (08NL), lines 5533-5545; face-by-face gluing gives the whole boundary, with m = 0 corresponding to n = 1. PASS after clarifying that the slice definition fixes x when the upper boundary map is empty.
- Step 6: opened both cited statements and read Kerodon 01L5; checked the operator reversal, reversed mapping-prism endpoints, naturality under p, realization gluing and recovery of both lifting equations. PASS after spelling out the mapping-prism isomorphism.
- New nodes: none; zero new nodes and zero Mathlib leaves. No elementary node, duplicate, restatement or unsupported leaf to remove.

Small cases independently checked: for p = id every mapping map and relative slice map is an identity; for Y a point the criterion is ordinary initial/final contractibility; for nerves of discrete categories n = 1 detects a missing arrow over a base identity; for ordinary categories, two arrows z to x over the same base arrow are forced equal by the n = 2 boundary with third edge id_x; the fixed x precludes empty X, while empty mapping bases are allowed and nonempty bases with empty source fail surjectivity. The n = 0 boundary for q fixes both endpoints of the n = 1 problem for p and adds no dimension-zero requirement on p.

Changes and reasons: clarified the empty-upper-boundary case in step 5; expanded the reversal of prisms and its simplicial naturality in step 6; enlarged three citation quotes so their constructions and hypotheses are visible; appended the actual logs of two fresh Mathlib searches using undercategory/initial-object vocabulary. The declaration signatures returned by leanfinder concern ordinary initial functors or the initial simplicial set. The independent grep and reading of Mathlib/AlgebraicTopology/Quasicategory/InnerFibration.lean found definitions and basic inner-fibration lemmas, not this result. Searches for the item id and relative-initial/final names in the read-only slopmaster2 WeilConjectures and Comparator trees found no attachment. No master sorry is treated as proved. All proof uses are backed by verbatim cited statements; the two off-unit theorem inputs remain declared as generic tools in split_report.tool_uses. The current blueprint ancestor proof and the chapter/unit records were read; historical ancestry and the unit route are retained. No SGA source is used.

Validation: the prescribed remote deliver.py dry run is being run on this repaired sandbox; its final result is recorded below after completion. No local DAG/preflight/review checker, compiler, Lake or build tool is run.

Second-reader validation result: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q87 lem-coef-infinity-relative-initial-boundary --no-push .` printed `OK (not pushed) deliver/Q87/lem-coef-infinity-relative-initial-boundary at bb0bbdbaca: preflight passed`. The tool explicitly reported admission to server preflight slot 29. The report-only addition of this result is included in the final delivery command, which runs preflight again.
