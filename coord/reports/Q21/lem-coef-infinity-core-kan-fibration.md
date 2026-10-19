# Worker report: lem-coef-infinity-core-kan-fibration

1. Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-core-kan-fibration.json`: statement, split into six proof steps, no complete Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-inner-fibration-equivalence-outer-horn.json`: statement-only generic relative outer-horn lifting lemma, unsplit, no Mathlib match.
- `dag/nodes/sec-six-functors/lem-coef-infinity-equivalence-two-out-of-three.json`: statement-only triangle-edge two-out-of-three lemma, unsplit, no Mathlib match.
- `citations.json`: nine exact quotations, covering every step/node citation.
- `report.md`: this report. `searches.jsonl` is the search-command evidence.

2. Attachments

None. Searches of the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the item tag, the proposed new-node tags, and quasicategory/isofibration/outer-horn/core terminology found no project theorem stating any of these three items. Ordinary-category results are not attachments of these simplicial-set statements. No Lean source was changed and no compiler was run.

3. Literature wanted

WANTED: Kerodon, Proposition 4.4.3.7 (Tag 01EZ), for lem-coef-infinity-core-kan-fibration.

WANTED: Kerodon, Proposition 4.4.2.1 (Tag 019D) and Theorem 4.4.2.6 (Tag 019F), for lem-coef-infinity-core-kan-fibration, Kan-complex clause.

WANTED: Kerodon, Proposition 4.4.2.13 (Tag 01H0), for lem-coef-inner-fibration-equivalence-outer-horn.

WANTED: Kerodon, Remark 1.4.6.3 (Tag 004U), for lem-coef-infinity-equivalence-two-out-of-three.

These Kerodon statements and the relevant proofs were read online; no source was installed into the repository. The item's proof is agent-written with `proof_origin.by = agent`. The four-character identifiers here are Kerodon tags, not identically spelled but unrelated Stacks tags. No SGA route is used.

4. Corrections and route

The previous worker's absent-node diagnosis is stale: the assigned file now exists in the shared DAG. Its statement is correct, so I preserved it. The starting proof was empty. During self-review I rejected an early draft that used an absolute horn filler as if it lay over the specified base simplex, and that hid two-out-of-three in prose. The final split has separate statement-only nodes for these two genuine generic facts. Neither restates the item's map-of-cores conclusion or its Kan-complex conclusion.

I read the chapter and historical unit, and the current main-20261015 proof of `prop-coef-integral-exceptional-adjoint`, paragraph 2 and its displayed derived Hom/limit calculation. The inherited chain passes through coherent finite-Reedy realization and the source-attachment join/cone calculus. This item supplies the core-map Kan-fibration argument used by `lem-coef-infinity-isofibration-exponentiation`; that parent is not cited back, which would be circular. Its historical unit binding and all inherited maintainer fields are retained. The one off-unit theorem used is the existing absolute outer-horn converse, declared as a generic tool solely in Step 6. No unit step or target statement is replaced.

5. Remaining work

No mathematical clause is left unaccounted for at this splitting level. The two new nodes intentionally have statements only. Validation is the required `deliver.py Q21 lem-coef-infinity-core-kan-fibration --no-push .` server dry run, whose output accompanies this handoff; no push is authorized. A second reader must inspect and deliver the accepted sandbox.

## Review by Q21

I checked the final six-step argument against Kerodon 01EZ, including its distinction between one-dimensional horns and higher horns. The assigned hypotheses are exactly an inner fibration between quasicategories plus equivalence lifting with prescribed source; I did not assume a Kan fibration or target lifting at the start. The item and both new statements use the existing inverse-edge/two-inverse-triangles definition, rather than an unspecified equivalence predicate.

For Step 1 I read `def-cbc-enhanced-diagrams-cones`: its inverse-witness sentence lets a simplicial map preserve equivalences by applying the map to the witnesses, and its core sentence gives precisely the claimed simplicial subset. This is a direct construction, not an additional theorem. Step 2 uses that same inverse-witness definition to choose the inverse triangle. For the prescribed-target horn I lift the reverse edge from the given object, then prescribe the initial 2-horn with edges the lifted equivalence and the identity. I checked its vertices, both prescribed edges, and the base triangle agree strictly. The conclusion `pc=b` of the relative lemma is essential here. Its hypotheses hold with n=2 and the lifted initial edge invertible. The edge recovered opposite the initial vertex maps to the original base edge. The triangle two-out-of-three statement then makes it an equivalence; the identity witnesses are the constant 2-simplices. This proves the missing direction of one-dimensional edge lifting explicitly without assuming an uncited opposite-isofibration theorem.

For Step 3 I read the whole statement of `lem-coef-inner-fibration-equivalence-outer-horn`, and checked Kerodon 01H0's final-horn proposition and its initial-horn opposite dual. The new node requires an inner fibration, not an isofibration, and returns a filler over the *specified* base simplex. The current p satisfies that hypothesis. Both distinguished edges are actually in the appropriate horn for n>=2 and are equivalences upstairs because the input horn lands in the core. Inner horns use exactly the assumption in the item's own statement. I did not use the existing absolute outer-horn node here: it does not assert this relative conclusion.

For Step 4 I read Kerodon 004U and the new triangle node. The latter says any two edges of the *given* 2-simplex being equivalences force the third to be so, which is exactly what the filled 2-horn needs. It is not merely closure of composites or two-out-of-three for a natural transformation of triangles. For n>=3 I wrote the vertex-count argument: an omitted face avoiding the two edge vertices and the horn index exists among at least four vertices. All remaining degeneracies are identities. Thus the core definition applies to the actual filler, and no all-edges assertion is silently inferred just from the base being in the core.

Step 5 is the definition of all-horn lifting, collecting the preceding cases for n>=1. For Step 6 I opened the existing `lem-cbc-equivalence-outer-horn-filling` statement. Its converse explicitly states that either outer-horn extension property forces the chosen edge to be an equivalence. Since K is Kan, the whole final-horn property for every n>=2 is present; since K has inner fillers, it is a quasicategory as required. This gives every edge invertible, and then the core equality degree by degree. The existing node is sufficient for this clause, so no new Kan-implies-core node was created.

The two new nodes were checked separately on small cases. For the relative statement, p=id has the prescribed base simplex itself as filler; p to the point recovers the absolute outer-horn criterion. Nerves of ordinary functors give cancellation/factorization along an invertible initial or final edge. No zero- or one-dimensional relative assertion is smuggled into this node, and with empty source no upper horn map exists. For two-out-of-three, the point, discrete nerves and groupoid nerves have the expected behavior; in the nerve of [2] there is no triple of noninvertible arrows satisfying its two-equivalences antecedent. Repeated vertices and identities do not change the conclusion. For the item, an empty Kan complex is allowed, and Kan-fibration lifting imposes no surjectivity from a dimension-zero horn. These checks revealed no statement dispute.

I reviewed delivery-errors B through E: no elementary packaging lemma was promoted to a node; no new node restates an item clause; all non-elementary inputs are named; each dependency's actual statement supplies what is taken from it; no smallness assumption is changed; there is no parent/back-edge cycle; and all new nodes carry filled blueprint provenance and statement-only proof fields. The nine quotations in `citations.json` were checked as verbatim substrings of the corresponding final statements. `proof_deps` equals the union of step uses.

For each of the three statements I ran LeanFinder, Loogle, grep and LeanSearch through the prescribed search command, then a second phrasing of each search. The fresh 24 records are in the assigned item's log and copied exactly as queries/results into the appropriate nodes; the assigned item also retains its five historical search records. I read the candidate source declarations: Mathlib's Quasicategory/Basic and InnerFibration files provide the primitive inner lifting notions; SimplicialSet/CategoryWithFibrations gives all-horn fibrations, not a proof that an arbitrary categorical isofibration restricts to cores. The Quasicategory/TwoTruncated homotopy-composition facts do not state the inverse-triangle equivalence predicate or its two-out-of-three theorem. Ordinary `Functor.core` and ordinary strongly cocartesian/isomorphism lemmas concern ordinary categories. No hit states any full new node or a one-line specialization of it, so there are zero Mathlib leaves.

## Not duplicates

I searched the whole DAG and blueprint by the tags and by outer-horn, isofibration, core and two-out-of-three terminology before creating nodes. The same four-character source identifiers also occur as unrelated Stacks tags; the pairwise entries below make that distinction explicit.

lem-coef-inner-fibration-equivalence-outer-horn vs lem-cbc-equivalence-outer-horn-filling: the existing node gives absolute fillers in one quasicategory; the new node lifts a horn along arbitrary inner p over a fixed base simplex, a stronger relative assertion not supplied by an absolute filler.

lem-coef-inner-fibration-equivalence-outer-horn vs lem-cbc-invertible-prism-extension: the existing statement extends an absolute invertible prism; it does not give relative outer-horn fillers with image exactly b.

lem-coef-inner-fibration-equivalence-outer-horn vs lem-coef-infinity-cocartesian-mapping-criterion: the existing node characterizes cocartesian edges using mapping spaces; it does not assert the required relative lifting property for every equivalence edge.

lem-coef-infinity-equivalence-two-out-of-three vs lem-sf-triangle-two-out-of-three: the existing node concerns three components of a shift-compatible natural transformation on a distinguished triangle in triangulated categories, rather than the three edges of one 2-simplex in a quasicategory.

lem-coef-infinity-equivalence-two-out-of-three vs lem-weil-pbc-generic-fibre-localization-domain-irreducible: the existing node uses Stacks 004U for irreducibility of a domain spectrum; the new node uses Kerodon 004U for equivalence edges.

lem-coef-inner-fibration-equivalence-outer-horn vs def-weil-pbc-hypercover-cohomology-colimit: the existing node uses Stacks 01H0 in hypercover/sheaf-cohomology arguments, not Kerodon 01H0 for relative quasicategory horns.

lem-coef-inner-fibration-equivalence-outer-horn vs lem-sc-hypercover-bottom-refinement-descent: the existing node uses Stacks 01H0 in hypercover/sheaf-cohomology arguments, not Kerodon 01H0 for relative quasicategory horns.

lem-coef-inner-fibration-equivalence-outer-horn vs lem-sc-hypercover-injective-module-row: the existing node uses Stacks 01H0 in hypercover/sheaf-cohomology arguments, not Kerodon 01H0 for relative quasicategory horns.

lem-coef-inner-fibration-equivalence-outer-horn vs lem-sc-hypercover-refinement-section-lifts: the existing node uses Stacks 01H0 in hypercover/sheaf-cohomology arguments, not Kerodon 01H0 for relative quasicategory horns.

lem-coef-inner-fibration-equivalence-outer-horn vs lem-sc-hypercover-resolution-comparison: the existing node uses Stacks 01H0 in hypercover/sheaf-cohomology arguments, not Kerodon 01H0 for relative quasicategory horns.

lem-coef-inner-fibration-equivalence-outer-horn vs lem-weil-pbc-grothendieck-cohomology-limit-vanishing: the existing node uses Stacks 01H0 in hypercover/sheaf-cohomology arguments, not Kerodon 01H0 for relative quasicategory horns.

lem-coef-inner-fibration-equivalence-outer-horn vs lem-weil-pbc-grothendieck-etale-local-epimorphism: the existing node uses Stacks 01H0 in hypercover/sheaf-cohomology arguments, not Kerodon 01H0 for relative quasicategory horns.

lem-coef-inner-fibration-equivalence-outer-horn vs lem-weil-pbc-grothendieck-hypercover-bottom-colimit: the existing node uses Stacks 01H0 in hypercover/sheaf-cohomology arguments, not Kerodon 01H0 for relative quasicategory horns.

lem-coef-inner-fibration-equivalence-outer-horn vs lem-weil-pbc-grothendieck-hypercover-comparison-cocone: the existing node uses Stacks 01H0 in hypercover/sheaf-cohomology arguments, not Kerodon 01H0 for relative quasicategory horns.

lem-coef-inner-fibration-equivalence-outer-horn vs lem-weil-pbc-grothendieck-hypercover-comparison: the existing node uses Stacks 01H0 in hypercover/sheaf-cohomology arguments, not Kerodon 01H0 for relative quasicategory horns.

lem-coef-inner-fibration-equivalence-outer-horn vs lem-weil-pbc-grothendieck-hypercover-limit-generation: the existing node uses Stacks 01H0 in hypercover/sheaf-cohomology arguments, not Kerodon 01H0 for relative quasicategory horns.

lem-coef-inner-fibration-equivalence-outer-horn vs lem-weil-pbc-grothendieck-hypercover-local-primitives: the existing node uses Stacks 01H0 in hypercover/sheaf-cohomology arguments, not Kerodon 01H0 for relative quasicategory horns.

lem-coef-inner-fibration-equivalence-outer-horn vs lem-weil-pbc-grothendieck-hypercover-model: the existing node uses Stacks 01H0 in hypercover/sheaf-cohomology arguments, not Kerodon 01H0 for relative quasicategory horns.

lem-coef-inner-fibration-equivalence-outer-horn vs lem-weil-pbc-grothendieck-hypercover-resolution: the existing node uses Stacks 01H0 in hypercover/sheaf-cohomology arguments, not Kerodon 01H0 for relative quasicategory horns.

lem-coef-inner-fibration-equivalence-outer-horn vs thm-weil-pbc-hypercover-cohomology-module-part: the existing node uses Stacks 01H0 in hypercover/sheaf-cohomology arguments, not Kerodon 01H0 for relative quasicategory horns.

lem-coef-inner-fibration-equivalence-outer-horn vs thm-weil-pbc-hypercover-cohomology: the existing node uses Stacks 01H0 in hypercover/sheaf-cohomology arguments, not Kerodon 01H0 for relative quasicategory horns.

lem-coef-infinity-equivalence-two-out-of-three vs def-sc-generic-point: the existing definition uses Stacks 004X for generic points of irreducible closed subsets; the new node uses Kerodon 004X only to identify inverse-triangle witnesses for equivalence edges.

lem-coef-infinity-equivalence-two-out-of-three vs lem-weil-pbc-irreducible-on-top: the existing theorem uses Stacks 004Z for an open continuous map with irreducible base and densely irreducible fibres; the new node uses Kerodon 004Z to identify homotopy inverses of quasicategory edges.

## Second reading by Q21

I independently read delivery-errors B–E, GOAL.md, coord/dag-sync.md, the chapter/unit records, the current main-20261015 exceptional-adjoint proof paragraph 2, all three delivered statements, and the statements of every cited node. These sources are Kerodon, not Stacks: I opened Kerodon 01EZ (Proposition 4.4.3.7), 01H0 (Proposition 4.4.2.13), 004U (Remark 1.4.6.3), 019D (Proposition 4.4.2.1), 019F (Theorem 4.4.2.6), and 004R/004X/004Z (the isomorphism/inverse-triangle comparison). The web reader timed out on 01EZ; an independent HTTP fetch succeeded and I read its statement and horn-by-horn proof. No Stacks theorem with the same four-character tag is used. The historical unit metadata is preserved; the current blueprint ancestry is the coherent realization needed for the displayed derived Hom/limit calculation, not a replacement of that calculation.

- Item statement — PASS against Kerodon 01EZ and 019D(b),(d): inner lifting and source-prescribed equivalence lifting are precisely the assumed isofibration data; the conclusion is all positive-dimensional horns on cores, plus the full Kan-complex clause. No surjectivity or nonemptiness condition is added.
- Step 1 — PASS against the inverse-witness and core sentences of def-cbc-enhanced-diagrams-cones: applying p to the inverse and both triangles preserves their boundaries, so the core map is defined. Fixing the horn square is elementary and supplies exactly the hypotheses subsequently used.
- Step 2 — PASS against the definition and both new statements: Lambda_1^1 prescribes the source; Lambda_0^1 prescribes c at the target. For the latter, the base triangle has vertices p(c),d,p(c) and edges w,e,id. The lifted upper Lambda_0^2 has vertices c,c',c and edges v,id. Their images agree on the entire horn. The relative lemma supplies edge 12 over e exactly, and triangle two-out-of-three makes it invertible. The two inverse triangles exchange roles to witness that w is an equivalence, so source lifting is applicable to w; I made this explicit. Constant triangles witness the identity case. No target-lifting assumption is used.
- Step 3 — PASS against the relative lemma and Kerodon 01H0: the inner case uses the stated inner-fibration hypothesis; the initial distinguished edge 01 is in face 2 and the final distinguished edge (n-1)n is in face 0, including n=2. Both edges are equivalences upstairs since the upper horn lands in the core. The supplied filler lies over the specified b. I made the initial-face index explicit.
- Step 4 — PASS against the core definition and the triangle lemma: for n>=3 a vertex j outside {r,s,i} exists among at least four vertices, giving an included face containing rs; for n=2 exactly two edges are prescribed and two-out-of-three applies to the actual chosen triangle. Degenerate edges have constant inverse witnesses. The base simplex being in the core alone is never used to infer invertibility upstairs.
- Step 5 — PASS against the item's Kan-fibration definition: Steps 2–4 exhaust n>=1 and every horn index. This collection step is elementary and includes the empty-core case.
- Step 6 — PASS against the actual converse statement of lem-cbc-equivalence-outer-horn-filling and Kerodon 019F(3)=>(1): K has the required inner fillers and every final-horn extension for any chosen edge. Thus every edge is invertible, and the two inclusions of cores are literal degreewise inclusions compatible with operators. This is a generic off-unit tool; the report's split_report.tool_uses requests its acceptance by the maintainer, without changing the maintainer-owned tool_uses field.
- Proposed new lem-coef-inner-fibration-equivalence-outer-horn — REMOVED AS DUPLICATE after the refreshed delivery base exposed lem-cbc-inner-fibration-equivalence-outer-horn-lift. I opened its statement: it supplies both initial and final relative fillers with the same two strict equalities, under exactly inner lifting and an extremal equivalence. Its smallness condition is met by fixing a common universe for the two simplicial sets in Step 1. Steps 2 and 3 and both citation quotations now use this existing generic tool; split_report.tool_uses requests maintainer acceptance. The following source and small-case checks remain valid against Kerodon 01H0: arbitrary inner p between quasicategories, n>=2, final equivalence edge upstairs, and strict prescribed-base filler match hypothesis by hypothesis. For its initial clause, order reversal sends vertex j to n-j, Lambda_0^n to Lambda_n^n and edge 01 to edge (n-1)n in C^op. It preserves inner horns, sends the two inverse triangles to inverse triangles with reversed order, and is involutive. Applying the final clause to the reversed square and reversing its filler gives both required equalities in the original square. B1–B7 pass: self-contained statement only, primitive definitions cited, no proof fields filled, single-escaped TeX, correct source tag/proposition, no Mathlib leaf claimed. Tests: p=id uses b itself; p to a point recovers absolute outer filling; ordinary nerves give factorization along an invertible edge; empty source has no upper horn maps; n=0,1 are excluded as intended.
- New lem-coef-infinity-equivalence-two-out-of-three — PASS against Kerodon 004U with 004R/004X/004Z: the three edges belong to one specified composition triangle, and the inverse-triangle predicate is the same predicate as source isomorphism. B1–B7 pass: all objects introduced, definitions cited, no proof or proof_deps, TeX correct, exact source places, no claimed Mathlib leaf. Tests: constant triangle, discrete and groupoid nerves, and nerves of [1] and [2], including repeated vertices and degenerate edges. Only when two classes are invertible can the antecedent hold; cancellation then has exactly the stated conclusion. The empty case has no 2-simplex.

I searched all DAG chapters and both blueprint snapshots by tags and by outer-horn, relative lifting, core, invertibility and two-out-of-three terminology. The existing absolute outer-horn and prism nodes give no prescribed-base filler for an arbitrary inner p; the cocartesian mapping criterion does not state equivalence edges are relatively cartesian/cocartesian. The marked-anodyne terminal-object theorem also does not assert the relative lifting statement. The existing ordinary distinguished-triangle two-out-of-three node concerns different objects. The more general lem-coef-infinity-mapping-composition does contain the homotopy-category comparison that would imply triangle two-out-of-three, but is unavailable here: its dependency path is mapping-composition -> pinch-comparison -> right-fibration-fibers -> isofibration-exponentiation -> this item. Citing it would make a cycle. Neither new node restates a clause of this item or is a two-line consequence of the available cited definitions.

For each new node I ran my own LeanFinder, Loogle, grep and LeanSearch with fresh phrasings; the four records for the retained triangle node are copied verbatim from searches.jsonl into that node; the four for the removed duplicate remain in the authentic search log. An initial grep mistakenly passed --sub as a positional directory; its authentic log entry remains, but is not used as evidence in any node. I reran it with the documented positional directory. I read Mathlib's InnerFibration.lean:64–105, Basic.lean:34–55, TwoTruncated.lean:236–289 and CategoryWithFibrations.lean:71–103. The inner-horn and all-horn primitives do not prove relative outer lifting. The homotopy-category triangle declarations do not state the inverse-triangle predicate comparison or its two-out-of-three property; using them requires an additional comparison theorem, so no new node qualifies as a Mathlib leaf. Read-only searches in slopmaster2, upstream master and dag/lean_names_upstream.json found no matching attachment; upstream master sorry declarations were not counted as proofs.

Changes made: removed the duplicate relative outer-horn node for lem-cbc-inner-fibration-equivalence-outer-horn-lift, repointed Steps 2 and 3, replaced both citation quotations by its verbatim statement, and requested its off-unit tool acceptance; added four independent search records to the retained new node (all eight searches remain in the authentic log); explicitly justified invertibility of the inverse edge in Step 2; identified the exact included face in Step 3; expanded the new two-out-of-three node's source with the inverse-triangle comparison references; updated split_report and appended this independent review. The item statement, the retained triangle statement and the six-step route are preserved; the two relative-horn citation quotations were updated to the existing node. All nine quotations were rechecked against the final cited statements, and each step's uses names exactly its non-elementary inputs. The final delivery has one new unsplit node and zero Mathlib leaves. This final count and the duplicate removal supersede the earlier worker report's two-node count and initial nonduplication conclusion. No Lean, compiler, Lake, build command, live-project edit or local preflight/check_dag/review_split run was used. The first worker's handoff restriction on pushing is superseded by this second-reader brief's explicit delivery instruction.

Dry-run repair: the first captured dry run failed only the duplicate check for lem-cbc-inner-fibration-equivalence-outer-horn-lift. That node is now present in the refreshed shared DAG; its full statement was read before deleting the uncommitted duplicate. Its statement dependencies and empty proof fields introduce no back-edge to this item. No existing node was edited. The repaired dry run and final delivery are recorded by the required delivery command.

Validation: the repaired server dry run printed `OK (not pushed) deliver/Q21/lem-coef-infinity-core-kan-fibration at 51ee096322: preflight passed`. The required server preflight, including check_dag.py and review_split.py, accepted the one-new-node split after removal of the duplicate relative-horn node.
