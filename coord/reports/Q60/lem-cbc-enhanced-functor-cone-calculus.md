## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-enhanced-functor-cone-calculus.json`: statement, split into ten derivation steps; statement unchanged.
- `lem-cbc-internal-hom-quasicategory.json`: statement, Mathlib leaf `SSet.instQuasicategoryObjIhom` at `Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/Inner/PushoutProduct.lean:153-154`.
- `lem-cbc-equivalence-outer-horn-filling.json`: statement-only, unsplit; no Mathlib match.
- `lem-cbc-invertible-prism-extension.json`: statement-only, unsplit; no Mathlib match.
- `lem-cbc-right-fibration-morphism-space.json`: statement-only, unsplit; no Mathlib match.
- `lem-cbc-simplicial-composition-spine.json`: statement-only, unsplit; no Mathlib match.
- `lem-cbc-kan-fibration-fiber-criterion.json`: statement-only, unsplit; no Mathlib match.
- `lem-cbc-terminal-boundary-extension.json`: statement-only, unsplit; no Mathlib match.

The seven new nodes are all in `dag/nodes/sec-smooth-purity/`. `citations.json` has 26 current verbatim step/node quotations. `searches.jsonl` is the unmodified append-only output of the mandated search command; the extra `.leansearch.txt` files preserve its full new semantic hits.

## Attachments

None. Searches by the exact item/child ids and by quasicategory, right fibration, outer horn, pinched, coherent cone and terminal boundary in both read-only `WeilConjectures/` source checkouts returned no project declaration stating these results. The exact internal-hom Mathlib instance is a leaf, not a project attachment. No master sorry declaration is treated as a proof.

## WANTED

WANTED: an archived Kerodon reference for the remaining foundations and their application to `lem-cbc-enhanced-functor-cone-calculus`: Tags 019F, 01DP, 01KR, 01L5, 01PF, 00ZP, 06R1, 01TL and 01U5 (and the slice and cartesian-fibration propositions named in those sources). These were read online, not downloaded to the shared literature. The removed slice/model node no longer needs Tag 01KR; the reused arrow and pinch nodes use 01KQ and 01L5. The item's proof is therefore explicitly agent-written. Scholze's archived lecture notes supply the ambient route and internal-hom fact. Kerodon tags are not Stacks tags; no SGA source is used.

## What was wrong or incomplete

The earlier sandbox had contradictory reports about five now-removed, unpublished clause-only nodes. The current split derives the actual item from reusable horn/fibration results instead of relabelling its clauses. The internal-hom clause is the sole exception because it is exactly a Mathlib theorem. No new definition or node merely isolating the item's componentwise-equivalence, cone, limit or terminal-space clause remains.

STATEMENT-DISPUTED (earlier unpublished child, now removed): `lem-cbc-limit-cone-criterion` compared an apex mapping space with a cone-category mapping space. For the nerve of finite sets, take K=Δ⁰, F={0,1}, μ=id_F, x={*}, and λ selecting 0. The cone μ is terminal in FinSet/F. Map(x,F) has two points, while Map_(FinSet/F)(λ,μ) has one. The main item's displayed map has target Map_Fun(Δx,F), is the identity on two points in this example, and is correct. Step 8 now derives that correct criterion. The item's statement was never changed.

The current blueprint opening says to choose a compactification; it does not contain the earlier report's alleged WANTED sentence. The ancestry remains the historical `thm-cbc-finite-level-proetale` through the compact-support-extension and coherent-cofiltered-diagram nodes. Its current proof is `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/thm-cbc-finite-level-proetale.proof.md`. This is a node-level foundation split; no chapter/unit route, target statement, or unit realization field is changed.

The preceding pass added LeanSearch with a distinct semantic phrasing for all eight then-proposed nodes (seven retained now), added focused grep queries, corrected the Mathlib match's `how` to `exact`, recorded its verified line 153, normalized JSON to indent 1, regenerated citations from current statements, and made step 5's homotopy inverse explicit. The invalid old Loogle identifier query on the item was replaced by the actually executed valid `"Quasicategory", "ihom"` query.

## What could not be finished

The six non-Mathlib foundations are intentionally unsplit statement-only nodes: stage 1 asks for one level, not recursive splitting. Their proofs and the archive request remain for subsequent items. The main item's ten-step natural-language proof is complete relative to those statements.

## Review by Q60

I read the stage-1 worker contract, all delivery-errors B–E, the three levels of SETUP, GOAL, dag-sync, and the chapter/unit records before reviewing the split. I then read the item and the full current definition `def-cbc-enhanced-diagrams-cones`, Scholze Lecture II printed pp.13–15, and the current blueprint opening. The definition fixes universes, right-pinched mapping spaces, the exact oriented comma pullback, the path direction for homotopy fibers, and terminal/initial objects. The arbitrary simplicial shape and arbitrary diagram in the item are retained. No filteredness or diagram-arrow invertibility is introduced.

For every step I opened each cited statement and regenerated its whole statement as a verbatim quotation. Step 1 takes only internal-hom closure from the Mathlib leaf; fullness puts a filler back in the full subcategory because an inner horn contains all vertices. Step 2 now takes exactly the Kan assertions of the existing pinch-comparison node, which names both mapping models explicitly. Step 3 uses the same horn/spine statements: in dimension two the missing edge is a composite of equivalences or their inverses, and in higher dimensions every edge was already in the horn. This proves the Kan core without assuming it.

Step 4 uses the prism node with A empty, B=K and Q=C. Its hypothesis is precisely invertibility of every vertical component edge; no horizontal edge of K is assumed invertible. The outer-horn node's converse applies because step 1 already makes the functor object a quasicategory. Evaluation takes inverse witnesses to inverse witnesses for the forward implication. Step 5 uses coherent composition on whole mapping spaces and natural pinch comparison, plus the definition of quasi-inverse and natural equivalence. The α and β naturality squares give Tu_*≃id and u_*T≃k; conjugation by δ has explicit inverse, so R=T k^{-1} is a two-sided homotopy inverse. Thus the mapping-space conclusion does not hide a full-faithfulness theorem or demand triangle-compatible choices.

Step 6 applies the existing arrow-target right-fibration statement with D=Fun(K,C) and T=F. It explicitly pulls that right fibration back along Δ_K, pairing a lifted arrow-family with the prescribed base simplex. Projecting, filling, and lifting an inner horn proves total-space closure. The existing pinch-comparison node gives both the Kan property of the fiber and its natural comparison with the right-pinched model. Step 7 uses the generic right-fibration transport/morphism-space statement, not a restatement of the cone clause. A square ending at id_F and a composition triangle identify a^*μ with μΔ_K(a). The spine and pinch statements supply coherent compatibility; reversing a fiber path yields the prescribed path from μΔ_K(a) to λ. This is the item's homotopy fiber, not a strict fiber or a bare arrow set.

Step 8 uses exactly the Kan mapping-path/fiber criterion and the definition of terminality: all pairs (x,λ) exhaust cone vertices. If the target space is empty, a map into it has empty source, so the criterion still covers that case. Step 9 uses the final-boundary-extension statement to fill every boundary in the full terminal-object subcategory. For n=0 it uses the chosen terminal vertex. Filling the missing face and then the boundary gives all horns. The Kan fiber criterion now makes its map to a point a weak equivalence. This proves contractibility of the full subcategory, including higher simplices, rather than merely uniqueness in the homotopy category. Step 10 reverses vertex order, exchanging horn i with horn n−i and cones/terminality with cocones/initiality. The pinch comparison applied in the opposite identifies mapping models. The explicitly typed dual map is Map_C(y,x)→Map_Fun(F,Δ_Kx) for a cocone with apex y.

I checked each new statement against its source and edge cases:

- Internal hom: Scholze Lecture II basic fact (1), and the exact Mathlib instance read at PushoutProduct.lean:153–154. Any small A is allowed, including empty A; no strict-Segal assumption appears.
- Outer horn: [Kerodon 019F](https://kerodon.net/tag/019F), Theorem 4.4.2.6. Both endpoint orientations, n≥2 and the converse quantified over all such horns match. The n=2 ordinary-category case tests the two inverse identities.
- Prism: [Kerodon 01DP](https://kerodon.net/tag/01DP), Lemma 4.4.4.8, specialized to Q→Δ⁰. The relative simplicial subset, all dimensions n≥2 and arbitrary B remain. A=B is tautological; A empty is exactly step 4.
- Existing arrow and pinch tools: [Kerodon 01KQ](https://kerodon.net/tag/01KQ), Proposition 4.6.4.13, and [01L5](https://kerodon.net/tag/01L5), Proposition 4.6.5.10. Source-to-F orientation gives exactly the right fibration used in step 6. The pinch comparison is natural in every simplicial functor and states the Kan property of both models. Empty bases give empty total spaces; ordinary nerves give discrete identity comparisons.
- Right-fibration transport: [Kerodon 01TL](https://kerodon.net/tag/01TL), Proposition 5.1.2.1; Proposition 5.1.4.15 (01UM); and [01U5](https://kerodon.net/tag/01U5), Remark 5.1.3.8. The node honestly states the agent-formulated right-fibration specialization of the cartesian mapping square. E and B are quasicategories; lifts have prescribed target and contractible compatible choices. A discrete base reduces the formula to path spaces within a fiber. The identity fibration gives Map_B(x,y) as the fiber of the constant map to the one-point fiber.
- Spine: [Kerodon 01PF](https://kerodon.net/tag/01PF), Corollary 4.6.8.5, Remark 4.6.8.7, Construction 4.6.8.9 and the unitality/associativity propositions. It is the full simplicial multiarrow-space theorem. For n=1 the restriction is the identity; for an ordinary nerve it is the usual unique composite.
- Kan fibers: [Kerodon 00ZP](https://kerodon.net/tag/00ZP), Proposition 3.3.7.6; the endpoint path-space fibration of Theorem 3.1.3.1 and interval contraction justify the stated mapping-path expansion. Empty source/base cases are retained: ∅→∅ passes, while ∅→Δ⁰ fails. No properness or base Kan hypothesis is added to the first Kan-fibration assertion.
- Final boundary: [Kerodon 06R1](https://kerodon.net/tag/06R1), Proposition 4.7.3.11, with Definition 4.7.3.1 and pinch comparison 01L5. It fixes the last vertex and requires m≥1; m=1 supplies incoming arrows, m=2 their compatibility. It does not itself assert the item's contractibility conclusion.

Every unsplit new node has an empty proof/dependency list, explicit objects/hypotheses, an inline definition of its extra fibration/boundary notation, and its own Mathlib searches. No elementary algebraic identity has been promoted to a node. The exact internal-hom match is a Mathlib leaf; all other primitive results require substantive horn/fibration arguments. The DAG, the full blueprint index and both source checkouts were searched by tags and mathematical vocabulary. Blueprint searches for quasicategory, right fibration, outer horn, pinched and the relevant source tags found no blueprint duplicate. I opened the three related existing coefficient-foundation statements; their mapping-excision, anodyne-join/restriction and final-vertex-inclusion assertions do not supply any of these new facts. All `same_as` fields remain empty, and the full ancestry via list is present.

All recorded Mathlib queries have actual msearch log entries. The new LeanSearch phrasings differ from the earlier LeanFinder statements; their full hits were read. The inner-horn hits state only inner horn filling, the StrictSegal hits concern unique fillers, HasFibers/Grothendieck concern ordinary categories, and the generic model-category predicates do not supply a geometric-realization weak-equivalence theorem for simplicial sets. I read Basic.lean:39–58, PushoutProduct.lean:142–154, and CategoryWithFibrations.lean:36–49,66–100 to check those distinctions. No unavailable service was recorded as absence.

### Resumption check, 2026-10-16

A fresh whole-DAG search found `lem-coef-infinity-arrow-target-right-fibration` and `lem-coef-infinity-pinch-comparison`, which were absent from the earlier report. I opened their complete statements and their sources (Kerodon 01KQ and 01L5). They supply all needed content of the unpublished slice/model node, which I removed. Step 2 now cites the existing Kan assertions directly. Step 6 writes out stability of horn lifting under pullback, so it needs no new pullback lemma. Steps 5, 7 and 10 now use the existing natural pinch comparison. Both off-unit nodes are declared generic tools in `split_report.tool_uses`; neither depends on this item. The other six non-Mathlib new nodes retain only their statements, and the exact internal-hom leaf is unchanged. The current split has seven new nodes and 26 citation records. The prior search log is retained verbatim; every query on the remaining nodes is backed by that log. Citation, search-log and duplicate checks all returned empty finding lists against the refreshed shared DAG.

I reopened the primitive sources: outer horns (019F), relative prism (01DP), composition spaces (01PF), Kan fibers (00ZP), terminal boundary extension (06R1), and cartesian mapping squares/right-fibration edges (01TL, 01UM, 01U5). In the transport node the homotopy-fiber paths run from the transported target to the source; the cartesian description first gives the reverse path, and path inversion in the Kan fiber identifies them. With K empty the cone projection is C→C and step 7 reduces to its usual mapping space. With Q empty the mapping assertions are vacuous and the nonempty-terminal hypothesis is essential. For an ordinary category the n=2 outer-horn test is exactly the two inverse equations. No extra smallness, filteredness, or invertibility assumption enters these substitutions.

### Fresh resumption audit, 2026-10-16

I independently reread the ten saved steps and all ten cited node statements against the current shared tree. The item still has its original statement and is unsplit in that tree. Exact-id and notion searches in both project source checkouts found no attachment. I read the current blueprint opening and Scholze Lecture II printed pp.13–15, and reopened Kerodon 019F, 01DP, 01PF, 00ZP, 06R1, 01TL, 01UM, 01U5, 01KQ and 01L5. In particular, 00ZP allows an arbitrary simplicial base, 01DP imposes its invertibility condition only on the vertical component edges, and 01UM identifies right fibrations with cartesian fibrations having Kan fibers. The right-fibration mapping node explicitly includes the coherent transport theorem being used; it does not pretend that the pointwise uniqueness remark alone proves the whole assertion.

The small-case checks agree: empty K leaves the cone category equivalent to C, empty mapping targets force empty sources, ordinary nerves make the multiarrow restriction an isomorphism, and the terminal-boundary n=1 case supplies the incoming edges needed by the argument. I checked the additional existing right-fibration-exponentiation node: its hypothesis is a right fibration, whereas the prism lemma has only a quasicategory as target and an outer horn with invertible vertical edges. It supplies no duplicate of that lemma.

I repaired step 10 to avoid a strict identification between opposite right-pinched spaces. It now uses the existing natural pinch comparison separately in C and its opposite, identifies the reversed arrow spaces, and writes out the realization-coordinate reversal and its compatibility with simplicial operators. This elementary identification explains why weak equivalences and terminality become the stated dual assertions. No additional foundational lemma is hidden in the word “dual.” The source and all new statements are unchanged.

I reread every recorded query and actual hit list, and verified the Mathlib internal-hom instance at PushoutProduct.lean:153–154. The read-only delivery citation, search-log, and duplicate checks each returned an empty finding list. Search-log history is preserved without inventing or rerunning any query. The required dry run uses the default shared locks; its result is recorded separately in dry-run-final.log and validation-record.json.

## Not duplicates

lem-cbc-terminal-boundary-extension vs lem-coef-infinity-slice-equivalence-final: the new node characterizes a specified final vertex in the ambient quasicategory by boundary extension, while the existing node characterizes equivalence arrows as final objects of a join slice; neither statement specializes to the other.

lem-cbc-terminal-boundary-extension vs lem-coef-infinity-pinch-comparison: the new node characterizes finality of a specified vertex by extension of boundaries ending at that vertex (Kerodon 06R1); the existing node compares right-pinched and arrow mapping spaces (Kerodon 01L5). It gives neither the boundary-extension characterization nor terminality. Its tag is mentioned only to relate the mapping conventions.

The earlier direct pair audits below are retained where their new ids remain. Four-character Kerodon and Stacks tags can collide; unrelated scheme/module statements were opened and distinguished by subject and actual statements. The related quasicategorical nodes are distinguished explicitly.

lem-cbc-right-fibration-morphism-space vs lem-weil-pbc-flat-morphism-affine-criterion: the existing statement concerns schemes or modules (Let $g:X\to Y$ be a morphism of schemes [def-pc-scheme]. Then $g$ is flat [def-weil-flat-morphism] if and only if for every pair of affine opens $U=\operatorname{Spec}B\subseteq X$); the new statement concerns quasicategorical mapping/composition or right-fibration transport. No specialization of the existing algebraic statement supplies it.

lem-cbc-right-fibration-morphism-space vs lem-weil-pbc-flat-ring-map-iff-flat-affine: the existing statement concerns schemes or modules (Let $\varphi:R\to A$ be a homomorphism of commutative rings and $\operatorname{Spec}\varphi:\operatorname{Spec}A\to\operatorname{Spec}R$ the induced morphism of affine schemes [def); the new statement concerns quasicategorical mapping/composition or right-fibration transport. No specialization of the existing algebraic statement supplies it.

lem-cbc-right-fibration-morphism-space vs lem-coef-infinity-anodyne-cocones: the existing statement is about right-anodyne inclusions, join pushouts and restriction on cocone mapping spaces; it gives neither this horn/model/transport theorem nor this boundary criterion.

lem-cbc-right-fibration-morphism-space vs lem-weil-pbc-integral-chow-relatively-ample: the existing statement concerns schemes or modules (Let $k$ be a field [def-weil-field] and let $X$ be an integral scheme [def-pc-scheme, def-pc-integral-scheme], separated and of finite type over $k$ [def-weil-proper-morphism, def-); the new statement concerns quasicategorical mapping/composition or right-fibration transport. No specialization of the existing algebraic statement supplies it.

lem-cbc-terminal-boundary-extension vs lem-coef-infinity-mapping-excision: the existing statement computes mapping spaces for functors on a simplicial pushout by a homotopy pullback; it does not establish the boundary-extension or slice-model theorem.

lem-cbc-terminal-boundary-extension vs lem-coef-infinity-anodyne-cocones: the existing statement is about right-anodyne inclusions, join pushouts and restriction on cocone mapping spaces; it gives neither this horn/model/transport theorem nor this boundary criterion.

lem-cbc-terminal-boundary-extension vs lem-coef-infinity-terminal-anodyne: the existing statement characterizes a final vertex by right-anodyneness of its point inclusion; it does not assert the boundary-extension criterion or the right-fibration slice/pinch comparison.






lem-cbc-simplicial-composition-spine vs lemma-nagata-closed-subscheme-fp-system: the existing statement concerns schemes or modules (Every $X_\alpha\hookrightarrow Y$ is of finite presentation, all transitions are closed immersions, and the canonical map $X\to\varprojlim_\alpha X_\alpha$ is an isomorphism.); the new statement concerns quasicategorical mapping/composition or right-fibration transport. No specialization of the existing algebraic statement supplies it.

lem-cbc-simplicial-composition-spine vs lem-pc-coherent-open-section-carrier: the existing statement concerns schemes or modules (Let $X$ be a Noetherian scheme [pqf-def-locnoeth], $E$ a quasi-coherent module [pqf-def-coherent, def-weil-sheaf-of-modules-category], $U$ an open subset, and $s\in E(U)$. There ar); the new statement concerns quasicategorical mapping/composition or right-fibration transport. No specialization of the existing algebraic statement supplies it.

lem-cbc-simplicial-composition-spine vs lem-weil-pbc-module-binary-local-properties: the existing statement concerns schemes or modules (Let $X$ be a scheme [def-pc-scheme], $W,V$ opens and $G$ a module sheaf [def-weil-sheaf-of-modules-category] on $W\cup V$. If its restrictions to both $W$ and $V$ are quasi-coheren); the new statement concerns quasicategorical mapping/composition or right-fibration transport. No specialization of the existing algebraic statement supplies it.

lem-cbc-simplicial-composition-spine vs lem-weil-pbc-module-finite-type-affine-enlargement: the existing statement concerns schemes or modules (Let $X$ be a quasi-separated scheme [def-pc-scheme, def-weil-pbc-scheme-conventions], let $W\subseteq X$ be a quasi-compact open [def-weil-pbc-quasi-compact-scheme], and let $V\sub); the new statement concerns quasicategorical mapping/composition or right-fibration transport. No specialization of the existing algebraic statement supplies it.

lem-cbc-simplicial-composition-spine vs lem-weil-pbc-module-filtered-colimit-finite-presentation: the existing statement concerns schemes or modules (Let $X$ be a scheme [def-pc-scheme] which is quasi-compact and quasi-separated [def-weil-pbc-scheme-conventions], and let $\mathcal F$ be a quasi-coherent $\mathcal O_X$-module [pq); the new statement concerns quasicategorical mapping/composition or right-fibration transport. No specialization of the existing algebraic statement supplies it.

lem-cbc-simplicial-composition-spine vs lem-weil-pbc-module-finite-type-affine-capture: the existing statement concerns schemes or modules (Let $X$ be a scheme [def-pc-scheme], $V$ an affine open, and $K\subseteq V$ a quasi-compact open [def-weil-pbc-quasi-compact-scheme]. Let $H$ be a quasi-coherent module [def-weil-s); the new statement concerns quasicategorical mapping/composition or right-fibration transport. No specialization of the existing algebraic statement supplies it.

lem-cbc-simplicial-composition-spine vs def-weil-pbc-module-binary-submodule-pullback: the existing statement concerns schemes or modules (Let $X$ be a scheme [def-pc-scheme], $W,V$ opens, $H$ a module sheaf [def-weil-sheaf-of-modules-category] on $X$, $Q$ a module sheaf on $V$, and $\iota:Q\to H|_V$. Put $j:V\to W\cu); the new statement concerns quasicategorical mapping/composition or right-fibration transport. No specialization of the existing algebraic statement supplies it.

lem-cbc-simplicial-composition-spine vs lem-weil-pbc-module-finite-type-affine-generators: the existing statement concerns schemes or modules (Let X be a scheme [def-pc-scheme], V an affine open, and K a compact open with K contained in V [def-weil-pbc-quasi-compact-scheme]. Let H be a quasi-coherent O_X-module [def-weil-); the new statement concerns quasicategorical mapping/composition or right-fibration transport. No specialization of the existing algebraic statement supplies it.

lem-cbc-simplicial-composition-spine vs lem-weil-pbc-module-binary-submodule-mono: the existing statement concerns schemes or modules (For any scheme $X$ [def-pc-scheme], opens $W,V$, module sheaves $H$ on $X$ and $Q$ on $V$ [def-weil-sheaf-of-modules-category], and a monomorphism $\iota:Q\to H|_V$, the first proj); the new statement concerns quasicategorical mapping/composition or right-fibration transport. No specialization of the existing algebraic statement supplies it.

lem-cbc-simplicial-composition-spine vs lem-weil-pbc-module-finite-type-global-approximation: the existing statement concerns schemes or modules (Let $X$ be a quasi-compact and quasi-separated scheme [def-pc-scheme, def-weil-pbc-scheme-conventions, def-weil-pbc-quasi-compact-scheme], $U\subseteq X$ a quasi-compact open, and ); the new statement concerns quasicategorical mapping/composition or right-fibration transport. No specialization of the existing algebraic statement supplies it.

lem-cbc-simplicial-composition-spine vs lem-weil-pbc-module-submodule-binary-gluing-second-restriction: the existing statement concerns schemes or modules (For any scheme $X$ [def-pc-scheme], opens $W,V$, module sheaves $H$ on $X$ and $Q$ on $V$ [def-weil-sheaf-of-modules-category], and any morphism $\iota:Q\to H|_V$, the concrete pul); the new statement concerns quasicategorical mapping/composition or right-fibration transport. No specialization of the existing algebraic statement supplies it.

lem-cbc-simplicial-composition-spine vs lem-weil-pbc-module-submodule-binary-gluing-restrictions: the existing statement concerns schemes or modules (Let $X$ be a scheme [def-pc-scheme], $W,V$ opens, $H$ a module sheaf on $X$ and $Q$ on $V$ [def-weil-sheaf-of-modules-category], and $\iota:Q\to H|_V$. Suppose the restriction of $); the new statement concerns quasicategorical mapping/composition or right-fibration transport. No specialization of the existing algebraic statement supplies it.

lem-cbc-invertible-prism-extension vs lem-weil-pbc-site-sheaves-enough-injectives: the existing statement is about enough injective objects for module sheaves on a ringed site; it says nothing about invertible simplicial prism extensions.

lem-cbc-invertible-prism-extension vs lem-weil-pbc-grothendieck-functorial-injective-embedding: the existing statement embeds objects of a Grothendieck abelian category functorially into injectives; it says nothing about simplicial horn extension.

lem-cbc-right-fibration-morphism-space vs lem-coef-infinity-mapping-excision: the existing statement computes mapping spaces for a simplicial pushout; it supplies no outer-horn, slice, transport, spine-composition or final-boundary theorem.

lem-cbc-right-fibration-morphism-space vs lem-coef-infinity-terminal-anodyne: the existing statement characterizes finality by right-anodyneness of the vertex inclusion; it does not state the new node's boundary extension, mapping-space transport, or simplicial slice/spine result.

lem-cbc-simplicial-composition-spine vs lem-coef-infinity-mapping-excision: the existing statement computes mapping spaces for a simplicial pushout; it supplies no outer-horn, slice, transport, spine-composition or final-boundary theorem.

lem-cbc-simplicial-composition-spine vs lem-coef-infinity-anodyne-cocones: the existing statement states a pushout-join anodyne theorem and invariance of cocone mapping spaces under right-anodyne restriction; neither is the primitive result of the new node.

lem-cbc-simplicial-composition-spine vs lem-coef-infinity-terminal-anodyne: the existing statement characterizes finality by right-anodyneness of the vertex inclusion; it does not state the new node's boundary extension, mapping-space transport, or simplicial slice/spine result.

## Validation

The read-only delivery citation, search-log and duplicate helpers return no findings against the current shared DAG. The 14-node dependency closure is acyclic, has no missing or merged dependency, and proof_deps equals the union of step uses. All JSON files have indent 1 and a final newline; every unsplit new node has an empty proof and proof_deps. The item statement is byte-for-byte unchanged.

The previous attempts did not accept the current seven-node snapshot: they encountered shared-lock contention and termination (most recently exit 137). An older eight-node version had passed, which is not evidence about this snapshot. The first fresh required command requested restoration of the duplicate-distinction line between the boundary criterion and the existing pinch-comparison node; that line has now been restored. The required command is `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q60 lem-cbc-enhanced-functor-cone-calculus --no-push`, with the default worktree/group locks. No push is attempted. Its completed result will be kept in the sandbox dry-run log and validation record.

## Current resumption and required dry run

This resumption reread all eight sandbox node statements and the three existing foundation statements used by the item. The current shared item remains unsplit and its statement agrees byte for byte with the sandbox. Searches of both project source checkouts for the item tag and the quasicategory/coherent-cone vocabulary found no declaration to attach. The Mathlib internal-hom instance was checked again at its recorded file, lines 153–154; it assumes exactly Quasicategory X and allows every simplicial A in the fixed universe.

I reopened Kerodon 019F, 01DP, 01PF, 00ZP, 06R1, 01TL, 01UM, 01U5, 01KQ and 01L5. In steps 3–4 the endpoint horn index and the invertible vertical-edge hypothesis match the outer-horn and prism statements. Step 5's conjugation calculation still uses the multiarrow-space compatibility, rather than asserting that unrelated chosen unit and counit satisfy triangle identities. Steps 6–7 use source evaluation with fixed target F, a right fibration, and the transport is contravariant, as required for the path from μΔ(a) to λ. Step 8 quantifies over every cone vertex, and step 9 uses the nonempty-terminal hypothesis for the zero-dimensional boundary. Step 10 uses opposite arrow spaces and geometric realization, rather than identifying opposite right-pinched spaces strictly. The empty-shape, empty-space, n=1 spine and ordinary-nerve checks in the signed review remain valid. No further mathematical correction was needed.

The required command first failed in its temporary checkout because a concurrent delivery held the shared git configuration lock. The lock was inspected read-only; it had already gone away. The clean retry printed `OK (not pushed) deliver/Q60/lem-cbc-enhanced-functor-cone-calculus at 10c5490e59: preflight passed` and exited 0. Citation, search-log and duplicate helpers independently returned empty findings against the refreshed DAG. This final report update is being included in a further ordinary required dry run; its exact output is retained in `dry-run-final.log` and `validation-record.json`. The node files, citations and search log are unchanged from the successful run. There has been no push, direct git command, shared-repository write, launcher change, Lean edit or compiler invocation by this worker.

## Earlier second reading (a previous round; superseded)

- Step 1 checked against `lem-cbc-internal-hom-quasicategory`, `def-cbc-enhanced-diagrams-cones`, and Scholze Lecture II basic fact (1): internal-hom and full-subcategory closure have the stated hypotheses; verdict OK.
- Step 2 checked against `lem-coef-infinity-pinch-comparison` and Kerodon 01L5: both mapping-space models are Kan; verdict OK.
- Step 3 checked against `lem-cbc-equivalence-outer-horn-filling`, `lem-cbc-simplicial-composition-spine`, and Kerodon 019F/01PF: the dimension-two and higher-dimensional core argument is valid; verdict OK.
- Step 4 checked against `lem-cbc-invertible-prism-extension`, `lem-cbc-equivalence-outer-horn-filling`, and Kerodon 01DP/019F: the empty-subset specialization uses exactly componentwise equivalences; verdict OK.
- Step 5 checked against `lem-cbc-simplicial-composition-spine`, `lem-coef-infinity-pinch-comparison`, and Kerodon 01PF/01L5: the conjugation calculation supplies a two-sided homotopy inverse without hidden triangle assumptions; verdict OK.
- Step 6 checked against `lem-coef-infinity-arrow-target-right-fibration`, `lem-coef-infinity-pinch-comparison`, and Kerodon 01KQ/01L5: the cone pullback and right-fibration argument are correctly typed; verdict OK.
- Step 7 checked against `lem-cbc-right-fibration-morphism-space`, `lem-coef-infinity-pinch-comparison`, `lem-cbc-simplicial-composition-spine`, and Kerodon 01TL/01U5: transport and homotopy-fiber path orientation agree; verdict OK.
- Step 8 checked against `lem-cbc-kan-fibration-fiber-criterion` and Kerodon 00ZP: all cone vertices and empty-space cases are covered; verdict OK.
- Step 9 checked against `lem-cbc-terminal-boundary-extension` and Kerodon 06R1: boundary and horn filling in the full terminal-object subcategory, including dimensions 0 and 1, is valid; verdict OK.
- Step 10 checked against `lem-coef-infinity-pinch-comparison`, `def-cbc-enhanced-diagrams-cones`, and the opposite construction: vertex reversal gives the cocone and initial-object duals without a strict opposite-pinched identification; verdict OK.
- New node `lem-cbc-internal-hom-quasicategory` checked against Mathlib `SSet.instQuasicategoryObjIhom` at PushoutProduct.lean:153–154 and its recorded searches; exact Mathlib leaf, verdict OK.
- New node `lem-cbc-equivalence-outer-horn-filling` checked against Kerodon Theorem 4.4.2.6 (019F), including both endpoint orientations and n≥2; statement-only and self-contained, verdict OK.
- New node `lem-cbc-invertible-prism-extension` checked against Kerodon Lemma 4.4.4.8 (01DP), specialized to the inner fibration into Δ⁰; arbitrary A⊆B and n≥2 are retained, verdict OK.
- New node `lem-cbc-right-fibration-morphism-space` checked against Kerodon Proposition 5.1.2.1 (01TL) together with 01UM/01U5; the stated transport and mapping-space fiber formula has all objects introduced, verdict OK.
- New node `lem-cbc-simplicial-composition-spine` checked against Kerodon Corollary 4.6.8.5 and Construction 4.6.8.9 (01PF); the multiarrow restriction and coherent composition clauses match, verdict OK.
- New node `lem-cbc-kan-fibration-fiber-criterion` checked against Kerodon Proposition 3.3.7.6 (00ZP) and the stated mapping-path model; the fibration, fiber, and empty cases are explicit, verdict OK.
- New node `lem-cbc-terminal-boundary-extension` checked against Kerodon Proposition 4.7.3.11 (06R1); the specified last vertex and m≥1 condition match, verdict OK.

Changes made in this second reading: added this required audit section only. No mathematical statement, proof step, citation, or search record required correction. The seven-node count remains six statement-only foundations plus one exact Mathlib leaf; no duplicate or elementary node was found.

## Second reading by Q60

- Step 1 checked against `lem-cbc-internal-hom-quasicategory`, `def-cbc-enhanced-diagrams-cones`, and Scholze Lecture II basic fact (1): internal-hom and full-subcategory horn closure have the required hypotheses; verdict OK.
- Step 2 checked against `lem-coef-infinity-pinch-comparison`: both right-pinched and arrow mapping spaces are Kan; verdict OK.
- Step 3 checked against `lem-cbc-equivalence-outer-horn-filling`, `lem-cbc-simplicial-composition-spine`, and Kerodon 019F/01PF: inner and outer core fillers preserve equivalence edges; verdict OK.
- Step 4 checked against `lem-cbc-invertible-prism-extension` and `lem-cbc-equivalence-outer-horn-filling`: the componentwise equivalence condition is exactly the prism hypothesis; verdict OK.
- Step 5 checked against `lem-cbc-simplicial-composition-spine` and `lem-coef-infinity-pinch-comparison`: the conjugated quasi-inverse gives both homotopy inverses without triangle-compatible choices; verdict OK.
- Step 6 checked against `lem-coef-infinity-arrow-target-right-fibration`, `lem-coef-infinity-pinch-comparison`, and the explicit pullback: the coherent cone category and its fibers are correctly typed; verdict OK.
- Step 7 checked against `lem-cbc-right-fibration-morphism-space` and the composition/pinch nodes: transport and homotopy-fiber path orientation agree; verdict OK.
- Step 8 checked against `lem-cbc-kan-fibration-fiber-criterion`: all cone vertices are covered, including empty mapping-space cases; verdict OK.
- Step 9 checked against `lem-cbc-terminal-boundary-extension` and the fiber criterion: boundary and horn filling prove the full terminal-object subcategory is Kan and contractible when nonempty; verdict OK.
- Step 10 checked against the opposite construction, `def-cbc-enhanced-diagrams-cones`, and the pinch comparison: reversal yields the cocone and initial-object assertions without a strict pinched-space identification; verdict OK.
- `lem-cbc-internal-hom-quasicategory` checked against Mathlib `SSet.instQuasicategoryObjIhom` at `PushoutProduct.lean:153-154`; exact leaf, verdict OK.
- `lem-cbc-equivalence-outer-horn-filling` checked against Kerodon 019F, including both endpoint orientations and $n\ge2$; self-contained statement-only node, verdict OK.
- `lem-cbc-invertible-prism-extension` checked against Kerodon 01DP, with arbitrary $A\subseteq B$ and only vertical-edge invertibility; self-contained statement-only node, verdict OK.
- `lem-cbc-right-fibration-morphism-space` checked against Kerodon 01TL with 01UM/01U5 transport data; self-contained statement-only node, verdict OK.
- `lem-cbc-simplicial-composition-spine` checked against Kerodon 01PF; coherent multiarrow composition and inverse homotopies are stated explicitly, verdict OK.
- `lem-cbc-kan-fibration-fiber-criterion` checked against Kerodon 00ZP and the stated mapping-path model; empty fibers and weak-equivalence criterion are retained, verdict OK.
- `lem-cbc-terminal-boundary-extension` checked against Kerodon 06R1; specified final vertex and $m\ge1$ boundary condition match, verdict OK.

Changed the item node’s `created.item` from the stale cofiltered-diagram id to the delivered item id, because delivery metadata must name this item. Added this independent second-reading section; no mathematical statements, proof steps, citations, or search records otherwise required correction.
