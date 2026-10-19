# Worker report

1. Files written: `dag/nodes/sec-six-functors/lem-coef-infinity-terminal-pullback-criterion.json` (statement, split, no Mathlib match); `dag/nodes/sec-six-functors/lem-coef-kan-homotopy-commuting-pullback-invariance.json` (statement-only, no Mathlib match); `citations.json`; this report. There is one new unsplit node and no Mathlib leaves. The item statement and inherited metadata are retained; its proof and split report are revised.
2. Attachments: none. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint id, `infinity_terminal_pullback_criterion`, terminal/pullback notions and finite-limit declarations found no project declaration stating all clauses. The item has `lean_audit.slopmaster2.state = none`. The recorded later-stage Sheaf theorem is not an attachment to a finished slopmaster2 proof; this work writes no Lean and invokes no compiler.
3. WANTED: Denis-Charles Cisinski, *Higher Categories and Homotopical Algebra*, CatLR.pdf, §§6.2, 6.6 and 7.3, especially Theorem 6.6.9, Remark 6.6.11, Proposition 7.3.16 and Theorem 7.3.27, for this item. Online source read; no local archival copy. WANTED: Lurie, *Higher Topos Theory*, Proposition 4.4.2.2 and Remark 4.4.2.3, for the existing colimit-gluing tool, and Kerodon 01P9/032B for the existing excision/path-invariance tools. No document was downloaded. Proof origin remains `agent`.
4. The imported record had ten proof steps despite status unsplit. Three exceeded 2000 characters and contained useful separate results rather than one routine calculation. Steps 2, 3, and 4 now cite the path comparison, strict path-pullback invariance plus the new homotopy-commuting invariance node, and mapping excision respectively; the other seven steps retain the original route. The item therefore still has ten steps, with no hidden argument longer than 2000 characters and no changed hypothesis or conclusion. No statement dispute was found. The blueprint parent is paragraph 2 of the coefficient-adjunction proof; the generic categorical infrastructure does not replace the geometric or coefficient route of the unit.
5. Nothing mathematical remains unfinished for this one-level split. Sources not archived are identified above. Server dry run and delivery results are appended below.

## Blueprint and searches

Read the chapter record `sec-six-functors` and unit `sk-prop-sf-biduality-general`, the three levels in SETUP, GOAL and dag-sync, and the current blueprint `main-20261015/.../sk-thm-sf-package/prop-coef-integral-exceptional-adjoint.{md,proof.md}`. The parent paragraph uses the derived coefficient-adjunction calculation, so these are generic coherent-limit tools below that node, not a different unit proof. No unit record changes are needed. `blueprint_refs.py ancestor` gives `prop-coef-integral-exceptional-adjoint`; `search "terminal pullback criterion"` gives no blueprint equivalent. The broader finite-limits search found ordinary geometric and category-theoretic notions, not the coherent criterion. The item's exact `from.place` and empty `same_as` are retained.

The inherited Mathlib searches and their reported results are preserved. This run executed leanfinder, Loogle, grep and LeanSearch through msearch; all are in searches.jsonl. Loogle returned zero hits for `"Quasicategory", "IsLimit"`; natural-language searches returned ordinary CategoryTheory finite limits and simplicial-set finite pullbacks. I opened Quasicategory/Basic.lean:34-42,70-87 and InnerFibration.lean:76-91, and LimitsOfProductsAndEqualizers.lean:270-276. The former only provide inner horn filling and inner fibrations; the latter assumes an ordinary category. Neither is an exact match or a one-line specialization to coherent simplicial diagrams. Thus the item remains non-Mathlib. The new homotopy-commuting node was searched with LeanSearch, Loogle, LeanFinder and grep, including the second semantic phrasing and broader Loogle query already recorded at 08:31 in searches.jsonl. I read those retained results and the model-category RightHomotopy source: changing path objects and transitivity of right homotopies do not state the required comparison of simplicial path-pullback spaces. These existing searches are retained verbatim in the node, without repeating the unchanged search questions. The node remains a statement-only non-Mathlib node.

## Not duplicates

The new node is distinct from every existing node sharing its Kerodon tags:

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-coef-spaces-homotopy-fiber-detection: the new node compares path-model pullbacks of two spans under weak equivalences and specified homotopies on both legs; the existing node detects a weak equivalence of total spaces from homotopy-fiber maps over a weak-equivalence base.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-coef-kan-fibration-arbitrary-base-fibers: the new node treats homotopy-commuting maps between four Kan-complex spans and proves a path-model comparison; the existing node treats a strictly commuting map between Kan fibrations over an arbitrary simplicial base and compares strict fibers.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-coef-kan-pullback-path-comparison: the new node compares two different spans using objectwise weak equivalences and endpoint homotopies; the existing node constructs one span's path model and compares it with its strict pullback when one leg is a fibration.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-coef-kan-homotopy-pullback-invariance: the new node allows specified homotopy commutation and inserts the endpoint homotopies with coherent inverses and concatenation; the existing node assumes strict commutation and applies the map to the path simplex directly.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-weil-pbc-formal-systems-surjective: the new node is a homotopy-pullback statement for Kan complexes; the existing node characterizes epimorphisms of coherent formal modules by their first component.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-weil-pbc-preadditive-epi-iff-cokernel-zero: the new node is a simplicial weak-equivalence comparison; the existing node is the categorical characterization of epimorphisms by a zero cokernel.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective: the new node concerns path spaces of Kan complexes; the existing node characterizes epimorphisms of abelian sheaves by local surjectivity.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-coef-kan-iterated-chain-comparison: the new node handles one cospan with arbitrary endpoint homotopies; the existing node handles an iterated finite tower of strictly matched Kan fibrations and its successive path models.

Existing `lem-coef-infinity-mapping-excision`, `lem-coef-kan-pullback-path-comparison` and `lem-coef-kan-homotopy-pullback-invariance` are reused rather than restated as children. The finite-limit gluing in step 8 retains the original direct cone-space construction; it does not invoke `lem-coef-infinity-colimit-gluing`. The existing finite-shape-generation and limits-products-pullbacks statements were not used: their dependency closures return to this item. A closure traversal of the selected dependencies instead found no path back to the item, no missing node and no merged dependency.

The additional Kerodon composition reference shares the identifier 01PF with the following nodes. I opened their statements as well; none states the new comparison.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lemma-nagata-closed-subscheme-fp-system: the existing node concerns finite-presentation closed subschemes and an inverse limit; the new node concerns weak equivalences of Kan-space path pullbacks. The shared identifier is a Stacks/Kerodon tag collision.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-coef-infinity-adjunction-mapping-equivalence: the existing node turns an adjunction unit/counit with triangle homotopies into mapping-space equivalences; the new node compares path pullbacks of homotopy-commuting spans and assumes no adjunction.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-coef-infinity-mapping-composition: the existing node constructs composition on mapping spaces and proves its homotopy laws; the new node uses coherent path concatenation to compare two spans and prove a weak equivalence of their path pullbacks.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-cbc-simplicial-composition-spine: the existing node supplies trivial Kan spine restriction and coherent composition; it does not assert weak-equivalence invariance of path pullbacks under homotopy-commuting span maps.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-pc-coherent-open-section-carrier: the existing node lifts an open section to a coherent subsheaf on a Noetherian scheme; the new node concerns Kan-space span comparisons.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-weil-pbc-module-binary-local-properties: the existing node glues finite type and quasi-coherence of module sheaves from two opens; the new node concerns weak homotopy equivalences of path pullbacks.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-weil-pbc-module-finite-type-affine-enlargement: the existing node enlarges a finite-type quasi-coherent submodule across an affine open; the new node has only Kan-complex and homotopy hypotheses.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-weil-pbc-module-filtered-colimit-finite-presentation: the existing node presents a quasi-coherent sheaf as a filtered colimit of finitely presented modules; the new node is a homotopy-pullback comparison of spaces.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-weil-pbc-module-finite-type-affine-capture: the existing node captures a module on a compact open in a finite-type submodule on an affine scheme; the new node compares path-model pullbacks.

lem-coef-kan-homotopy-commuting-pullback-invariance vs def-weil-pbc-module-binary-submodule-pullback: the existing node defines a module-sheaf pullback using restriction and direct image; the new node proves a weak-equivalence statement for simplicial path pullbacks.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-weil-pbc-module-finite-type-affine-generators: the existing node constructs finitely many module generators over a compact open; the new node concerns specified simplicial homotopies between span maps.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-weil-pbc-module-binary-submodule-mono: the existing node proves that a module-sheaf pullback projection is a monomorphism; the new node proves weak-equivalence invariance for Kan-space path pullbacks.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-weil-pbc-module-finite-type-global-approximation: the existing node globally approximates a quasi-coherent sheaf by a finite-type subsheaf agreeing on an open; the new node has no sheaf or scheme objects.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-weil-pbc-module-submodule-binary-gluing-second-restriction: the existing node identifies a sheaf pullback after restriction to one open; the new node compares homotopy pullbacks of Kan spaces.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-weil-pbc-module-submodule-binary-gluing-restrictions: the existing node proves the two open restrictions of a module-sheaf pullback agree with the given local data; the new node treats weak equivalences and endpoint homotopies of simplicial spans.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-weil-pbc-module-finite-type-submodule-extension: the existing node extends a finite-type quasi-coherent submodule from a compact open of a qcqs scheme; the new node compares Kan-space path pullbacks.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-weil-pbc-module-finite-type-affine-union: the existing node constructs a finite-type submodule on a union with an affine open; the new node is a simplicial homotopy-invariance assertion.

lem-coef-kan-homotopy-commuting-pullback-invariance vs lem-weil-pbc-module-submodule-binary-gluing: the existing node glues compatible finite-type quasi-coherent modules across two opens; the new node compares two Kan-complex cospans with specified endpoint homotopies.

## Review by NX

I read all cited node statements, not their proof interfaces alone. I also read Cisinski's online Theorem 6.6.9 and Remark 6.6.11 (Cartesian squares and homotopy Cartesian squares of spaces) and Theorem 7.3.27 (finite limits from a final object and pullbacks). For the generic local gluing input I read HTT Proposition 4.4.2.2 and Remark 4.4.2.3: it needs only the three specified local colimits and the pushout, with the induced arrows determined by the cocones. Kerodon 01P9 explicitly makes the morphism-space map of an inner fibration a Kan fibration, consistent with the existing excision statement. I read the new homotopy-commuting node statement and its four recorded Mathlib searches; it is a statement-only node and is the exact input to step 3. No SGA source is used.

Step 1 uses the definition's actual terminal-object clause and the cone-calculus statement's equivalence from maps into the apex to fixed-apex coherent-cone spaces. It does not confuse the core of the varying-apex cone category with a fixed-apex transformation mapping space.

Step 2 cites the path-comparison node exactly for the Kan property of the displayed path model and its strict-to-path comparison under a Kan-fibration hypothesis. No strict path inverse is introduced.

Step 3 cites strict path-pullback invariance for strictly commuting spans and the new homotopy-commuting node for specified endpoint homotopies. The new node's hypotheses match the two weak-equivalence legs and common base in this step; composition-spine supplies coherent concatenation and inverse homotopies. No strict path inverse on Kan 1-simplices is asserted.

Step 4 uses mapping-excision's exact monomorphism hypothesis, actual restriction-and-constant-path comparison, and natural pre/postcomposition clauses. There is no completeness hypothesis to import. Taking one diagram constant supplies exactly the cone-space calculation needed later.

Step 5 uses the final-index-colimit node only for its explicit standard-simplex cocone. Reversal of ordinal operators converts it to the initial-vertex cone; the pinch-comparison statement supplies natural equivalences with unpinched arrow spaces, so reversal exchanges endpoints correctly. Barycentric reversal directly intertwines the defining quotient relations for realization. Cone-calculus then identifies evaluation at the initial vertex with the inverse of composition with that cone. This includes n=0 and records how evaluation at the final vertex is the cospan-leg composite.

Step 6 applies step 4 to the two-edge cospan and step 5 to its edges. Step 3 allows the equivalences of edge cone spaces with their actual endpoint homotopies. The two edge triangles yield exactly the supplied square's path (one followed by the inverse of the other). Composition-spine and the naturality in excision retain its higher parameters. Cone-calculus then gives both directions of the limiting test, so the comparison is not an arbitrary map to an equivalent space.

Step 7 uses cone-calculus for functor quasicategories and equivalence effects on mapping spaces, and composition-spine for the inverse-triangle and associativity homotopies. An inverse equivalence of cospan diagrams induces inverse homotopies on fixed-apex cone spaces; the same is true of changing an apex by an equivalence. Two-out-of-three therefore preserves and reflects the test. The actual comparison respects maps of cones by the restriction and composition compatibility already proved.

Step 8 keeps the original direct gluing argument. Cone-calculus produces the maps X→Y←Z from the restricted local cones, together with paths to those actual restrictions. The assumed pullback gives P and the compatible local cones at P; step 4 identifies their triple with an actual global cone up to a path. The same natural restriction comparison, the equivalences induced by the three local limiting cones, step 3, and the pullback test proved in step 6 identify the map induced by that global cone with an equivalence for every x. Cone-calculus then proves it limiting. All three local limits and the monic leg are hypotheses here. This does not cite colimit-gluing or the proof of any other node. The previous report paragraph describing an opposite-colimit argument was inaccurate and has been corrected to the retained proof text.

Step 9 uses monomorphism-boundary-cells' explicit sequence indexed by nondegenerate simplices, not by all simplices. Finite many cells can be ordered within each stage by the elementary universal property of a finite pushout. The boundary of an n-simplex has only proper injective ordinal maps as nondegenerate simplices, so it is finite of smaller dimension. Noninjective attaching maps and identified faces are allowed, since only the boundary→simplex leg must be monic.

Step 10 uses the definition for the empty-diagram terminal cone and the previous steps for the cell attachment. The induction is on dimension and then the number of top-dimensional cells, so each local shape used has already been treated. For n=0 the boundary is empty and the operation produces products by pullbacks over the terminal object. Thus it proves existence for all finite nondegenerate-simplex shapes rather than only finite nerves.

Small cases checked: empty E gives false terminal-existence antecedent; empty K gives the terminal object; Δ0 uses its own vertex; two isolated vertices are a product; an ordinary nerve yields the ordinary terminal/pullback criterion with discrete path spaces; empty Kan spaces and empty fibers are permitted by the fiber statements; degenerate cospan legs and attached simplices with identified faces preserve the arguments. All sizes are fixed in a containing universe as in the definition and excision statements.

Against delivery-errors B–E: the statement is self-contained and unchanged, all uses are cited, every use has a verbatim statement excerpt in citations.json, no clause of the item was moved to a new node, and no separate lemma remains concealed in a >2000-character step (the longest revised step is below that threshold). The substantive correction is to cite the existing smaller results for the long comparisons, while keeping the actual cospan comparison and finite induction in the item. The two directly used off-unit tools in split_report are cone-calculus and composition-spine, with their reasons retained. The two fiber tools no longer cited directly after extracting steps 2–3 have been removed from that list. This is my self-review signature, not an independent maintainer review.


## Repair continuation, 2026-10-17

The retained split was checked first with the required server dry run: `OK (not pushed)` at ed1d663ef3. I compared the current shared item with the sandbox: its statement, statement dependencies, Lean record, blueprint metadata, and proof steps 1 and 5–10 are unchanged. The return’s original steps 2, 3, 4 have lengths 2060, 2765, 2195; their replacements are 396, 569, 516 characters. Each hidden comparison now has a cited statement: the existing path comparison, existing strict invariance plus the one new homotopy-commuting lemma, and existing mapping excision. The maximum remaining step length is 1722. This is extraction of the requested arguments, not a new proof route or a change of the stage-2 statement.

I reopened every cited statement and checked all 18 step/node quotations against it verbatim. A traversal of the current dependencies, including those of the reused comparison and excision nodes, finds no path back to this item. For the new node I reread online Kerodon 010B, 032B, 00ZN and 01PF: 032B covers strict commutation only; the new node is explicitly an agent-formulated extension for specified endpoint homotopies, with their inverse/concatenation comparison and all parameters retained. The path direction is H_u inverse, then c(gamma), then H_v, so both endpoints lie over a(x), b(y). If U or V is empty both pullbacks are empty; for discrete W the homotopies force strict commutation and reduce to the existing theorem; identity maps with nonconstant endpoint homotopies give path transport and its inverse, not an unjustified constant-path map. Choice of coherent composition is taken on the whole parameter space, not chosen separately at vertices. The new lemma is strictly smaller than the item and asserts neither its limiting-cone criterion nor finite-limit existence. No Stacks tag covers this infinity-categorical comparison, and no SGA source is used.

I corrected the report’s step-8 mismatch and removed its two unused direct tool declarations. I retained the earlier logged searches and added the already-run second phrasing to the new node’s search records after reading its results. No search was fabricated or repeated, and no Lean file or compiler was used. A final dry run after these metadata/report repairs is required below.
