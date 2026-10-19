# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-left-fibration-equivalence-lift.json` — item, statement and dependencies retained; four proof steps added; status `split`.
- `citations.json` — verbatim statement quotations for every cited node at every proof step.

Attachments: none. I searched both named `WeilConjectures` source trees for the item id, its Kerodon tags (019K and 01EW), and the left-fibration/conservativity/isofibration notions. No sorry-free project declaration states the item. The existing declarations about ordinary categorical fibrations and Mathlib simplicial sets do not state this quasicategorical result.

WANTED: Kerodon, Proposition 4.4.2.11 (tag 019K) and Example 4.4.1.11 (tag 01EW), https://kerodon.net/tag/019K and https://kerodon.net/tag/01EW, for conservativity and isofibration of left fibrations. The pages were read online on 2026-10-17 and are not archived under `literature/`; the proof is therefore marked agent-written. No SGA source is used.

## What was wrong or incomplete

The imported node was an unsplit statement with no proof. I found no statement error. The proof now expands the source's lift of an inverse triangle, repeats it to obtain a genuine inverse, derives the prescribed-source isofibration clause, and gives the prescribed-target lift by first lifting the inverse edge and then the inverse-triangle 2-simplex. The exact base edge in the prescribed-target clause is retained because it is the edge 12 of the lifted 2-simplex. No new node was created: the only non-elementary inputs are the two existing definition nodes, and no item clause was moved into a helper.

I searched the whole DAG and blueprint for left-fibration conservativity, isofibration, equivalence-edge lifting, and tags 019K/01EW. Existing relative-coslice and outer-horn nodes use this item but do not state it as an already finished declaration; they are not duplicates of this item and are not needed as proof dependencies. Mathlib searches (LeanFinder, Loogle, grep, LeanSearch) returned only generic all-horn/model-category or inner-fibration primitives, so no Mathlib leaf applies.

## What I could not finish

Nothing remains for the first-reader split. The second reader should perform the independent mathematical review and delivery; no Lean source was written and no compiler, Lake, or build tool was run.

## Review by Q01

I read `dag/chapters/sec-smooth-purity.json`, `dag/units/sk-prop-sf-cbc.json`, the item node, the current `main-20261015` blueprint ancestry for `thm-cbc-finite-level-proetale`, the two cited definition nodes, and the Kerodon pages 019K and 01EW. The chapter and unit route remain unchanged. The item statement uses exactly the definitions of equivalence edges, quasicategories, and left fibrations in `def-cbc-enhanced-diagrams-cones` and `def-coef-infinity-fibrations`; their full statements were copied into `citations.json` where used.

Step 1 was checked against 019K: for an edge whose image is invertible, the inverse and its 2-simplex witness give a base 2-simplex with edges `r(u)`, the inverse, and the identity. The left horn has precisely the two prescribed edges `u` and `id_X`, so the lifted 2-simplex supplies `v` and `v u ≃ id_X`. The source and target vertices agree with the item hypotheses.

Step 2 repeats Step 1 for `v`, since its image is the chosen base inverse. The two one-sided inverse witnesses paste associatively to identify the second lift `w` with `u`; substituting that equality gives `u v ≃ id_Y`. Together with `v u ≃ id_X`, this is exactly the inverse criterion in the enhanced-diagrams definition, so reflection is proved without assuming an unmentioned full Kan condition.

Step 3 was checked against the left-fibration horn range in `def-coef-infinity-fibrations`: all inner horns are included, and the `n=1,i=0` lift fixes the source vertex. The reflection result from Steps 1–2 makes the lifted edge an equivalence, which is precisely the stated isofibration source clause. No target or base nonemptiness hypothesis was added.

Step 4 uses the prescribed-target data exactly: an inverse `e'` of `e` gives a base 2-simplex on `(r(y),m_0,r(y))` with edges `e'`, `id`, and `e`. The left 1-horn lifts `e'` from `y`; the left 2-horn with edges `v` and `id_y` then produces edge 12 over `e` exactly. Step 1's reflection applies to that edge, proving it is an equivalence with target `y`. I checked the orientation of all three edges and the `Λ^2_0` horn before writing the step.

I checked the B–E checklist: every cited fact is present in the cited statement, every non-elementary argument is written in a proof step, no new node is a restatement of an item clause, and the proof dependency union equals the step uses. Small cases include `n=1` source lifts, `n=2` inverse triangles, identity equivalences, and empty simplicial sets. The recorded Mathlib searches were actually run with `msearch.py`; they do not claim a match. No definition, coefficient category, base-change morphism, or unit/chapter record was changed.


## Second reading by Q01

- Item statement: read Kerodon 019K, Proposition 4.4.2.11, and 01EW, Example 4.4.1.11 online; the left-fibration, quasicategory and equivalence hypotheses agree with both cited definition statements. The source-prescribed formulation is explicitly defined in the item, and Step 4 proves the additional exact target-prescribed lift. Verdict: true, unchanged, no statement dispute. These are Kerodon references, not Stacks tags; there is no corresponding Stacks source to open.
- Step 1: checked against 019K's displayed inverse triangle, the inverse definition in def-cbc-enhanced-diagrams-cones, and the relative lifting equalities and horn range in def-coef-infinity-fibrations. The horn is Lambda_0^2 with edges 01=u and 02=id_X, so the new edge 12 is exactly over the chosen inverse. Verdict: correct as written.
- Step 2: checked the repeated inverse lift against 019K and the quasicategory axiom in def-cbc-enhanced-diagrams-cones. The original homotopy-pasting/substitution prose used more than that node explicitly states (C1/E5). Verdict: repaired by two explicit inner 3-horns. On (X,Y,X,Y), faces d0=B, d2=(u,id_Y,u), d3=A give a Lambda_1^3 and face d1=(id_X,w,u). On (Y,X,X,Y), faces d0=H, d1=B, d3=(v,id_X,v) give a Lambda_2^3 and face d2=(v,u,id_Y). I checked each of the three shared edges of each horn; the resulting inverse triangles have the exact original edges u and v. Only the cited quasicategory definition and degeneracies are needed.
- Step 3: checked the full statement of def-coef-infinity-fibrations and 01EW's left-fibration assertion. Inner indices satisfy 0<i<n, and Lambda_0^1 consists of vertex 0, so the lifted source is x and its image is exactly e. Steps 1–2 then make that edge an equivalence. Verdict: correct; no new theorem is silently invoked.
- Step 4: checked the two inverse-triangle witnesses in def-cbc-enhanced-diagrams-cones and the left 1- and 2-horn lifting clause in def-coef-infinity-fibrations. The base triangle has ordered edges (e',e,id); the lifted edges 01=v and 02=id_y force the target of 12 to be y, and its base edge to be the original e exactly. Verdict: correct, including the prescribed-target condition used by the parent outer-horn item.
- New nodes: none, hence no statement-only/B1–B7 repairs or Mathlib leaves to review. Searched DAG/blueprint tags 019K/01EW, left-fibration, conservativity and equivalence-lifting vocabulary: no duplicate supplies this result. The parent outer-horn node depends on this item, so citing it would be circular; it is not used. The existing homotopy-category triangle-calculus node is unnecessary because both 3-horns are written out directly.

Small cases checked independently: empty source (all clauses vacuous), empty base (source necessarily empty), identity map, the point, identity equivalences (degenerate inverse triangles), nerves of ordinary categories, and dimensions n=1,2,3. There is no dimension-zero nonemptiness requirement. In the nerve case the two inner 3-horns express precisely the ordinary cancellation calculation from vu=1 and wv=1, and produce uv=1. All specified source/target vertices and all relative base equalities survive the construction.

I independently ran msearch.py with the new LeanFinder phrasing “A simplicial map with lifting for the initial and inner horns reflects invertible edges of quasi categories”, Loogle `"SSet", "ReflectsIsomorphisms"`, and an AlgebraicTopology grep for left fibration/conservative/isofibration/invertible edge. LeanFinder returned primitive inner horn filling and truncated edge-homotopy definitions/comparisons, not the item; the other two searches returned zero hits. I read Basic.lean's quasicategory/hornFilling declarations and the TwoTruncated.lean homotopy primitives; these are not a full leaf for the present relative one-sided fibration assertion. The actual search records are appended to searches.jsonl and the node. Independent source-tree searches for the item id, its two tags, and left-fibration identifiers found no project declaration to attach. No Lean, compiler, Lake or build command was run.

Changes: replaced only Step 2's hidden pasting/substitution with the two face-by-face inner-horn constructions; adjusted its source explanation and split summary; appended the independent searches. Both definition citations remain correct verbatim excerpts and citations.json's step/node pairs still equal the proof-step uses. The item statement, statement dependencies, provenance, unit/chapter route and blueprint ancestry are unchanged. The earlier Review by Q01 is retained as the first worker's account; its Step 2 description is superseded by this explicit repair.
