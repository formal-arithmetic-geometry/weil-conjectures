## Worker report

Files written:

- `dag/nodes/sec-purity-real-sheaves/lem-a1-lft-flat-lfp-source-descent.json`: repaired split, unchanged statement and statement dependencies, three assembly steps.
- `dag/nodes/sec-purity-real-sheaves/lem-a1-fppf-source-finite-affine-charts.json`: new statement-only unsplit lemma; Mathlib has individual affine criteria and compact-cover tools, not the combined chart-selection conclusion.
- `dag/nodes/sec-purity-real-sheaves/lem-a1-finite-affine-family-fppf-algebra.json`: new statement-only unsplit lemma; Mathlib has coproduct and affine flatness ingredients, not the complete compatible two-map construction and all its coordinate properties.
- `citations.json`: verbatim statement quotes for every assembly-step citation.

Attachments: none. Project search for the blueprint tag and source-descent notion found no finished declaration in WeilConjectures. The existing Sheaf theorem `AlgebraicGeometry.locallyOfFiniteType_of_flat_lfp_source` explicitly ends in `sorry`, so is not an attachment.

WANTED: none.

The sandbox initially contained only dispatcher marker files, with no node, report or search log from an earlier delivery. I copied the current live node as the returned baseline and preserved its original metadata, source, searches and Lean record. The first dry run exited because the report was missing; no delivery remained active. The released stage-1 repair note explicitly reopens the otherwise reviewed split. The fault to repair was the 3961-character seven-step proof, not its mathematics: two independently actionable lemmas now own the two substantial arguments, and neither concludes the parent's local-finite-type descent assertion. No statement correction was necessary. Nothing remains mathematically unfinished beyond the deliberately statement-only new tasks.

## Argument allocation and retained proof

The finite-chart node owns old steps 1-3: selection of affine neighbourhoods and an affine cover of the inverse image, all three affine-pair ring criteria and tower compatibility, openness, and quasi-compact finite image selection. The empty-target/vacuous pointwise case remains explicit in assembly step 3.

The finite-family node owns old steps 4-6: finite coproduct construction and the product-spectrum identification including the component maps; the two structural maps and their composition equality; stalkwise flatness, componentwise local finite presentation and local finite type; the full-affine coordinate criteria; surjectivity and proper extended maximal ideals giving faithful flatness, including the zero-ring case. It is stated for a general finite family of ring towers, not for the original scheme triangle. This is comparable work to chart selection, rather than moving the whole parent into one node.

Old step 7 is the parent's final assembly: apply existing 0367 and the pointwise criterion. The old proof is retained below verbatim as the work specification for the two parallel workers; the new node statements themselves contain no proof sketches.

### Old step 1 — owner: lem-a1-fppf-source-finite-affine-charts

Fix $y\in Y$. Choose an affine open $V=\operatorname{Spec}R\subseteq S$ containing $h(y)$, and an affine open $W=\operatorname{Spec}A\subseteq Y$ containing $y$ and contained in $h^{-1}(V)$, using the affine-open basis. Cover the open subset $q^{-1}(W)\subseteq X$ by affine opens $U_\alpha=\operatorname{Spec}B_\alpha$ of $X$ contained in $q^{-1}(W)$. The pointwise finite-type criterion shows that it suffices, for each such $y$, to prove the induced ring map $R\to A$ is of finite type. If $Y$ has no points this criterion is vacuous and the conclusion already holds.

Cited nodes: lem-weil-pbc-affine-opens-basis, lem-weil-pbc-lft-pointwise-criterion

### Old step 2 — owner: lem-a1-fppf-source-finite-affine-charts

For every $\alpha$, apply the affine-pair flatness criterion to $q$ and the pair $(U_\alpha,W)$: $A\to B_\alpha$ is flat. Apply the affine-pair finite-presentation lemma to the same pair: $A\to B_\alpha$ is of finite presentation. Apply the affine-pair finite-type criterion to $h\circ q$ and $(U_\alpha,V)$: $R\to B_\alpha$ is of finite type. These ring maps form the tower $R\to A\to B_\alpha$ since the morphism is $h\circ q$. All the opens used here are affine opens of the original schemes, so no claim about the affineness of an intersection is needed.

Cited nodes: lem-weil-pbc-flat-morphism-affine-criterion, lem-weil-pbc-lfp-affine-opens-finite-presentation, lem-weil-pbc-lft-affine-pairs

### Old step 3 — owner: lem-a1-fppf-source-finite-affine-charts

The morphism $q$ is open because it is flat and locally of finite presentation. Thus every $q(U_\alpha)$ is open in $Y$, hence in $W$. Surjectivity of $q$ and the covering of $q^{-1}(W)$ imply $W=\bigcup_\alpha q(U_\alpha)$. The affine scheme $W$ is quasi-compact; choose finitely many indices $\alpha_1,\ldots,\alpha_n$ whose images cover $W$. This uses quasi-compactness only of $W$, and imposes none on $q$ or $q^{-1}(W)$.

Cited nodes: lem-weil-pbc-flat-lfp-open, lem-weil-pbc-affine-scheme-qcqs

### Old step 4 — owner: lem-a1-finite-affine-family-fppf-algebra

Form $Z=\coprod_{i=1}^nU_{\alpha_i}$ and the morphisms $q_Z:Z\to W$, $p_Z:Z\to V$ induced by the component maps; then $p_Z=(h|_W)\circ q_Z$ by the coproduct universal property. The components are pairwise disjoint open subschemes covering $Z$. By the finite-coproduct spectrum identification, $Z\cong\operatorname{Spec}B$ with $B=\prod_{i=1}^nB_{\alpha_i}$, with the specified component maps. At a point of component $U_{\alpha_i}$ the local-ring map of $q_Z$ is the local-ring map of $q$ at that point, because both source and target have merely been restricted to open neighbourhoods. Thus $q_Z$ is flat by the stalkwise definition. Each component is an affine neighbourhood with finitely presented $A$-algebra by step 2, so the pointwise definition gives that $q_Z$ is locally of finite presentation. Each component also has finite-type $R$-algebra, so the pointwise finite-type criterion gives that $p_Z$ is locally of finite type. Finally $q_Z$ is surjective by the chosen finite image cover.

Cited nodes: lem-weil-pbc-scheme-coproduct-family, lem-weil-pbc-finite-affine-coproduct-spectrum, def-weil-flat-morphism, def-sbc-locally-finite-presentation, lem-weil-pbc-lft-pointwise-criterion

### Old step 5 — owner: lem-a1-finite-affine-family-fppf-algebra

Apply the affine-pair criteria to the full affine source $Z=\operatorname{Spec}B$ and the full affine targets $W=\operatorname{Spec}A$ and $V=\operatorname{Spec}R$. From flatness and local finite presentation of $q_Z$ obtain that $A\to B$ is flat and of finite presentation. From local finite type of $p_Z$ obtain that the composite $R\to B$ is of finite type. The tower $R\to A\to B$ is exactly that of the two maps constructed in step 4, so its composite ring map agrees with that induced by $p_Z$.

Cited nodes: lem-weil-pbc-flat-morphism-affine-criterion, lem-weil-pbc-lfp-affine-opens-finite-presentation, lem-weil-pbc-lft-affine-pairs

### Old step 6 — owner: lem-a1-finite-affine-family-fppf-algebra

For a maximal ideal $\mathfrak m\subset A$, surjectivity of $q_Z$ supplies a prime $\mathfrak n\subset B$ whose inverse image is $\mathfrak m$. Every image of an element of $\mathfrak m$ lies in $\mathfrak n$, hence $\mathfrak mB\subseteq\mathfrak n\ne B$. Thus every extended maximal ideal is proper. Together with flatness of $A\to B$ from step 5, the cited faithful-flatness criterion implies that $A\to B$ is faithfully flat. If $A$ is the zero ring the condition on maximal ideals is empty, and the same criterion still applies.

Cited nodes: lem-weil-pbc-flat-faithfully-flat-maximal-ideals

### Old step 7 — owner: lem-a1-lft-flat-lfp-source-descent

Apply the ring-tower descent lemma to $R\to A\to B$: step 5 gives finite type of $R\to B$ and finite presentation of $A\to B$, while step 6 gives faithful flatness of $A\to B$. Conclude that $R\to A$ is of finite type. For each $y\in Y$, the affine pair $(W,V)$ chosen in step 1 now satisfies the pointwise finite-type criterion for $h$. Therefore $h$ is locally of finite type.

Cited nodes: lem-a1-finite-type-fppf-source-algebra, lem-weil-pbc-lft-pointwise-criterion

## Searches and sources

I read Stacks `descent.tex` Tag 02KL (`lemma-flat-finitely-presented-permanence`), especially its affine reduction, openness/finite-image selection, finite-coproduct sentence and final algebra step, and Tag 0367 (`lemma-finite-type-local-source-fppf-algebra`). For the chart node I also read `morphisms.tex` Tags 01T2 (`lemma-locally-finite-type-characterize`), 01TQ (`lemma-locally-finite-presentation-characterize`), 01U5 (`lemma-flat-characterize`) and 01UA (`lemma-fppf-open`). For the finite-family node I read the same affine criteria and `algebra.tex` Tag 00HP (`lemma-ff`), including the nonzero-maximal-fibre criterion. The coproduct statement and product-spectrum statement were read directly in the existing DAG. The source's “Clearly we may replace” sentence is precisely the non-elementary argument now assigned to the finite-family node, not an unexplained assembly step.

DAG searches covered 02KL, 0367, finite affine covers and faithfully flat products; blueprint searches covered 02KL, finite affine, faithfully flat and the combined chart/product search. I read the nearest ancestor and current main-20261015 blueprint; its affine-Hc0 node has no proof text, so the precise inherited auxiliary schemehood route and the 02KL sentences are recorded. The two new ids do not occur in the live DAG. The existing fpqc-singleton refinement was also read in Lean: it is closed but assumes an fpqc-cover datum and gives only flatness/surjectivity/affineness, not the finite-presentation and base finite-type coordinate conclusions. Thus it does not state either new node.

All recorded new Mathlib queries were run with msearch.py and their actual output is in searches.jsonl. Both lemmas were searched with LeanFinder, Loogle, LeanSearch and grep; each received a second natural-language phrasing. All services answered. I read the relevant Mathlib sources in Cover/QuasiCompact.lean, Morphisms/Flat.lean, FinitePresentation.lean and FiniteType.lean. The compact-cover selection theorem requires building a quasi-compact-cover structure and then separate coordinate criteria; the coproduct and affine faithful-flatness theorems require several geometric and algebraic steps. These are not one-line Mathlib leaves.

## Review by Q27

I checked the repaired parent against Stacks 02KL and its existing algebra input 0367. The statement and statement dependencies are byte-for-byte unchanged from the live baseline. The source route and all seven arguments are retained by the allocation above. The parent has three steps totalling fewer than 3000 characters, and no step exceeds 2000 characters.

Assembly step 1 cites only the finite-chart node. Its statement supplies exactly the affine neighbourhoods, finite image cover, flat finitely presented A-algebras and finite-type R-algebras used there. I verified that its hypotheses are the original flatness, local finite presentation, point-surjectivity and finite type of h composed with q; it adds neither quasi-compactness of q nor separatedness. Its proof task includes openness plus affine target quasi-compactness, not quasi-compactness of the inverse image. Affine opens are taken in the original schemes, so no affine-intersection assumption occurs.

Assembly step 2 cites only the finite-family node. Its finite indexing, ring towers and component properties all come from step 1, and the image cover is precisely joint surjectivity of the spectra. Its statement explicitly supplies the coproduct-to-product identification with the right component maps and both structural maps, not merely abstract affineness. It also explicitly supplies faithful flatness, finite presentation and the finite-type composite, so no property is borrowed from the proof of a cited node. I checked the old maximal-ideal argument: a prime above a maximal ideal contains its extension, making that extension proper; flatness plus 00HP then applies. This is retained as a separate worker task in the report, with its conclusion in the new node.

Assembly step 3 cites 0367's existing node and the existing pointwise finite-type criterion, both of whose full statements I opened. The former assumes exactly the three properties obtained in step 2 and needs no Noetherian hypothesis. The latter is an if-and-only-if for an affine pair at every point, exactly supplied by steps 1-3. Neither citation is a definition used as a theorem. All four citation quotes are verbatim copied statements in citations.json.

Small cases checked: identity q and a single affine chart; an infinite disjoint union of affine copies mapping onto an affine target (q need not be quasi-compact); empty Y, where the pointwise criterion is vacuous; a one-element finite family, where the result is ordinary affine faithful flatness; and the empty finite family, whose joint surjectivity forces Spec A empty, hence A=0 and B=0. In particular the family lemma makes no false claim that each component is faithfully flat individually. No new lemma restates the parent or one of its clauses: one constructs finite coordinate data, the other assembles arbitrary finite data. No SGA route is used. I checked B-E for statement-only form, self-contained objects, definition dependencies, genuine search records, duplicates, C1/C4 citation support, cycles, hidden claims and hypotheses. The only correction was the requested redistribution of the proof into two comparable tasks.

## Not duplicates

lem-a1-fppf-source-finite-affine-charts vs lem-a1-finite-type-fppf-source-algebra: 0367 starts with a single faithfully flat finitely presented algebra and concludes finite type of A over R; this helper constructs the finite affine input instead.

lem-a1-fppf-source-finite-affine-charts vs lem-a1-lft-flat-lfp-source-descent: the parent concludes local finite type of h; this helper states only finite chart data.

lem-a1-fppf-source-finite-affine-charts vs lem-a1-scheme-lqf-etale-source-locality: local quasi-finiteness in an etale source triangle; no finite affine selection or compatible product-algebra conclusion.

lem-a1-fppf-source-finite-affine-charts vs lem-a1-fppf-integer-model: integer approximation of a single faithfully flat finitely presented ring map is unrelated to selecting charts or packaging a finite family.

lem-a1-fppf-source-finite-affine-charts vs lem-trf-lfp-fppf-source-locality: descent equivalence for local finite presentation for an arbitrary fppf family; it does not state the coordinate data constructed here.

lem-a1-fppf-source-finite-affine-charts vs thm-pd-fpqc-local-properties: finite-field base extension descent of geometric scheme properties, not finite affine chart selection or product-algebra assembly.

lem-a1-finite-affine-family-fppf-algebra vs lem-a1-finite-type-fppf-source-algebra: 0367 starts with a single faithfully flat finitely presented algebra and concludes finite type of A over R; this helper constructs the finite affine input instead.

lem-a1-finite-affine-family-fppf-algebra vs lem-a1-lft-flat-lfp-source-descent: the parent descends a property of h; this helper assembles an arbitrary finite family of ring towers and never concludes finite type of A over R.

lem-a1-finite-affine-family-fppf-algebra vs lem-a1-scheme-lqf-etale-source-locality: local quasi-finiteness in an etale source triangle; no finite affine selection or compatible product-algebra conclusion.

lem-a1-finite-affine-family-fppf-algebra vs lem-a1-fppf-integer-model: integer approximation of a single faithfully flat finitely presented ring map is unrelated to selecting charts or packaging a finite family.

lem-a1-finite-affine-family-fppf-algebra vs lem-trf-lfp-fppf-source-locality: descent equivalence for local finite presentation for an arbitrary fppf family; it does not state the coordinate data constructed here.

lem-a1-finite-affine-family-fppf-algebra vs thm-pd-fpqc-local-properties: finite-field base extension descent of geometric scheme properties, not finite affine chart selection or product-algebra assembly.

lem-a1-fppf-source-finite-affine-charts vs lem-galois-fpqc-singleton-affine-refinement: assumes a singleton fpqc datum and constructs a flat surjective affine refinement, without finite-presentation and R-finite-type coordinate conclusions.

lem-a1-fppf-source-finite-affine-charts vs lem-weil-pbc-fpqc-affine-standard-refinement: assumes a general fpqc cover and supplies a faithfully flat product after further refinement; does not preserve the specified finite family or assert finite presentation and R-finite type.

lem-a1-fppf-source-finite-affine-charts vs lem-weil-pbc-finite-affine-coproduct-spectrum: identifies the scheme with the product spectrum only, without flatness, finite presentation, base finite type or faithful flatness.

lem-a1-finite-affine-family-fppf-algebra vs lem-galois-fpqc-singleton-affine-refinement: assumes a singleton fpqc datum and constructs a flat surjective affine refinement, without finite-presentation and R-finite-type coordinate conclusions.

lem-a1-finite-affine-family-fppf-algebra vs lem-weil-pbc-fpqc-affine-standard-refinement: assumes a general fpqc cover and supplies a faithfully flat product after further refinement; does not preserve the specified finite family or assert finite presentation and R-finite type.

lem-a1-finite-affine-family-fppf-algebra vs lem-weil-pbc-finite-affine-coproduct-spectrum: identifies the scheme with the product spectrum only, without flatness, finite presentation, base finite type or faithful flatness.

lem-a1-finite-affine-family-fppf-algebra vs lem-sc-faithfully-flat-tensor-zero: detects zero modules after tensoring with an already faithfully flat module; no finite-family construction or coordinate presentation statements.

lem-a1-finite-affine-family-fppf-algebra vs lem-weil-pbc-criterion-flatness-fibre-noetherian: is a local Noetherian fibre flatness criterion for a module and a ring tower; our rings are arbitrary and the conclusion includes compatible finite coproducts and finite presentation.

lem-a1-finite-affine-family-fppf-algebra vs lem-weil-pbc-faithfully-flat-maximal-ideal-nonzero: assumes faithful flatness and concludes nonzero maximal fibres, whereas our node constructs the product and proves faithful flatness from jointly surjective component spectra.

lem-a1-finite-affine-family-fppf-algebra vs lem-weil-pbc-field-extension-base-change-faithfully-flat: concerns scalar extension by a field extension, not products of general flat finitely presented algebras.

lem-a1-finite-affine-family-fppf-algebra vs lem-weil-pbc-flat-faithfully-flat-maximal-ideals: is the already cited supporting criterion for one flat map with proper extended maximal ideals; it does not construct the product map or prove its hypotheses or presentation and finite-type properties.

lem-a1-finite-affine-family-fppf-algebra vs lem-weil-pbc-flat-module-faithfully-flat-maximal-ideals: is a faithful-flatness criterion for a single module with all maximal fibres nonzero; it does not construct a finite coproduct or establish the coordinate algebra properties.

lem-a1-finite-affine-family-fppf-algebra vs lem-weil-pbc-local-completion-faithfully-flat: concerns completion of a Noetherian local ring; no completion or Noetherian hypothesis occurs in the new finite-family lemma.

Dry-run duplicate follow-up: I opened all seven 00HP statements listed by the gate. They are supporting faithful-flatness criteria or distinct applications; none states the finite-family construction. Added all seven explicit pair comparisons above.

## Landing-return repair, 2026-10-22

The return in `coord/returns/Q27.md` identifies returned head `3af9a12cfa5`: the independent reader approved its mathematics, but landing refused a side-project completion that had not been promoted into the live DAG. I retained that delivery's sandbox, including both new statement-only nodes, the full seven-step argument, all search results and all citation quotes. The required first dry run completed successfully at `dec1b88ab7e`; it was allowed to exit before any further delivery invocation.

I compared the retained item with the current read-clone node. Before this repair their only differing fields were `proof`, `proof_deps` and `split_report`; their statements, statement dependencies, source, blueprint ancestry and maintainer records agree. Neither new id exists in the current read clone. The released stage-1 re-split order remains present and requires the two new tasks. The delivery tool obtains current `origin/sheaf-dag` and preserves its maintainer-owned fields, so this is a fresh delivery against the live project.

I reopened every statement cited by the three assembly steps. The two newly created statements still supply the precise chart data and compatible product-ring construction requested by their old quotes. Both existing live statements, `lem-a1-finite-type-fppf-source-algebra` and `lem-weil-pbc-lft-pointwise-criterion`, still contain the entire returned citation quotes verbatim. The first requires faithful flatness AND finite presentation of A to B, as well as finite type of R to B; all three are conclusions of the finite-family node. The second requires an affine pair at every point, exactly what chart selection supplies. No changed citation forces a replacement node. I also reread all statement-dependency definitions and the affine criteria, coproduct and maximal-ideal lemmas underlying the retained seven-step argument; their current statements support the same allocation. `repair-comparison.json` records the statement fingerprints and quote comparisons locally.

This repair clarifies assembly steps 2 and 3, rather than merely re-pushing an unchanged delivery: step 2 now explicitly identifies the image-cover equality with joint spectrum surjectivity and identifies BOTH structural maps with the coordinate tower; step 3 lists every algebra-descent hypothesis at its application and the affine-neighbourhood condition at the pointwise criterion. I corrected the stale seven-step wording in the split-report blueprint description to describe the three-step assembly and its retained original arguments. No statement, dependency, helper task, source route or logged search changed.

For this repair I reread Stacks 02KL and 0367 in `descent.tex`, 00HP in `algebra.tex`, and the affine-pair characterizations and flat-lfp openness in `morphisms.tex`. I rechecked the one-chart case, the infinite disjoint-union source (which needs no quasi-compactness assumption), empty Y and the empty finite family over the zero ring. The latter is allowed because joint surjectivity then forces Spec A empty. I reread the recorded search hits in Mathlib's Flat, FinitePresentation, Limits and QuasiCompact-cover files: the individual results remain ingredients rather than exact matches for either full helper. The search questions have not changed, so the genuine existing searches were reused. The upstream project search still gives no completed exact declaration; the Sheaf declaration remains explicitly `sorry`. No Lean was written and no compiler or build was run.
