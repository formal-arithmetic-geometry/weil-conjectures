# Q83: lem-sfb-closed-point-fp-patching

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-closed-point-fp-patching.json`: statement node, split into eleven steps. The item is not a Mathlib match. No new nodes and no new Mathlib leaves.
- `citations.json`: one entry for each node cited in each step, quoting that node's verbatim statement, including its hypotheses.
- `searches.jsonl`: genuine searches run with msearch.py for this item; inherited node searches are retained in the item.
- `report.md` and the sandbox-only `write_split.py` used to write the JSON.

## Attachments

No attachment for the item. Searches under `lean/WeilConjectures/` for its blueprint tag, closed-point patching and finite-presentation patching found no declaration of this equivalence. The ordinary gluing declarations do not state the local-spectrum result. The already attached declaration `AlgebraicGeometry.locallyOfFinitePresentation_of_comp` belongs to the existing dependency `lem-a1-map-over-base-finite-presentation`; I read its statement and proof at `WeilConjectures/Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean:53` and reuse that node.

## WANTED

None. All mathematical sources needed for this split are available in the supplied Stacks source.

## Corrections and scope

The statement's mathematical content is preserved. Its imported string contained doubled TeX backslashes; these have been reduced to one TeX backslash. I added the existing definition dependencies for quasi-compactness and quasi-separatedness. There is no statement dispute.

The proof is based on Limits Tag 0BPA, `lemma-glueing-near-closed-point`, and the neighbourhood/property-descent argument in Tag 0EY3, `lemma-glueing-near-point-properties`. I use the proof pattern of 0EY3 for smoothness and open/closed immersions, not a claim that its printed statement lists those three properties. Their actual descent inputs are the existing nodes for 0C0C, 0EUU and 01ZP.

I corrected two potential gaps in a terse assembly: the overlap isomorphism is descended by descending both arrows and then both inverse equations, and finite presentation of the glued object includes quasi-separatedness. The arrow finiteness needed for immersion descent is proved using the stronger existing over-base finite-presentation cancellation lemma 02FV; it does not depend on an unstated separatedness assumption.

I read the chapter and unit records and the newest blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3). This is a foundational chart-patching tool in the recorded Neron/trait-extension prerequisite below that direct-image route, not the unit's key statement. No unit realization fields are changed. `blueprint_refs.py ancestor` returns `None` for this deeply created item; its inherited `from.node = null` and `via` chain are retained, and its existing precise `from.place` is retained. The search of all imported blueprint nodes for gluing, finite presentation and closed points found no equivalent statement, so `same_as` remains empty.

## Not duplicates

There are no new nodes. In particular, no new node repeats any clause of this item or any Stacks descent lemma. The existing `lem-per-finite-point-fp-gluing` is restricted to schemes inducing the identity on the complementary open and asserts proper/finite/integral detection. It does not replace this item's arbitrary gluing triples or its smooth/open/closed detection. The existing general spreading-out and gluing nodes supply the actual proof ingredients instead.

## Review by Q83

I read delivery-errors B through E in full and checked the written JSON against them. The only changed node is the assigned item; there are no new statements to check for duplicate creation, unsupported definitions or missing searches. The current Mathlib searches used leanfinder twice, loogle, leansearch and grep with two patterns. Their results were ordinary Scheme.GlueData, RelativeGluing and finite-presentation chart declarations; I read the gluing source to distinguish those results from patching over a local spectrum. No search was invented, and no compilation or Lean writing was performed.

For step 1 I checked the actual statements of the affine-neighbourhood limit lemma and the affine-transition limit lemma: the former supplies a directed set and affine transitions, and the latter explicitly supplies the restriction-to-open limit. The canonical local-ring morphism node identifies the stalk with the prime localization and factors through every neighbourhood. The open-subscheme Noetherian lemma and locally Noetherian quasi-separated lemma provide qcqs for the non-affine overlaps, so I did not assume these overlaps affine. The equality of the inverse image of the closed point with the unique local maximal ideal is written out. This proves that the second limit really has base V, not T.

For step 2 I read all three clauses of `thm-pd-spreading-out`: object descent, arrow descent and eventual equality. Both overlap models have finite presentation by the explicit base-change clause (3) of `lem-weil-pbc-qcqs-morphism-permanence`. Clause (2) is applied separately to the inverse arrows and clause (3) separately to the inverse identities, taking common stages in a directed set. No isomorphism-descent fact is being taken from a node that states only object descent.

For step 3 the statement of `lem-galois-glue` gives the relative scheme with the prescribed identifications on an open cover. The two-member cocycle is precisely the two inverse equations from step 2. The local-spectrum morphism factors through W, so the restriction is the specified X_T and the overlap map is the specified alpha. I also read Constructions' Relative glueing section, Tag 01LG and its lemma 01LH, to check this matches the source's first paragraph.

For step 4 I checked that the definition of local finite presentation is pointwise and permits the chosen affine charts on U or W to remain charts on S. The affine-open finite-presentation lemma states the all-affine-chart formulation used to infer local finite type by forgetting relations. The qcqs permanence node explicitly gives compactness of the source from a quasi-compact map to a quasi-compact base, and quasi-compactness of a map from a quasi-compact source to a quasi-separated target. Thus the two pieces give a quasi-compact X and then a finite-type map X to S. Only after this do I apply the finite-type-over-Noetherian node and the locally Noetherian quasi-separated node, then the quasi-separated part of qcqs permanence. I checked these source assertions against Morphisms 01T6, Definitions 01TP and Properties 01OY. This retains the quasi-separated clause of finite presentation instead of proving a weaker finiteness notion.

For step 5 the source and target of every use of spreading are finite-presentation models over one common stage. Compatibility on V becomes equality on W intersect U by the explicit equality clause, and the statement of the morphism-gluing node provides both existence and uniqueness. The equality of the composites to S, and uniqueness of the global arrow, are checked on the actual open covering. I did not infer uniqueness merely from equality on the local spectrum.

For step 6 I checked Situation 081D directly in limits.tex: the stages, the two models and the target model must be qcqs. The permanence node gives those hypotheses from finite presentation. The already closed `lem-a1-map-over-base-finite-presentation` states local finite presentation of arbitrary over-base arrows when the source structure map is locally of finite presentation and the target structure map locally of finite type. These hold here; its proof is the project's 02FV declaration, which I read. It supplies precisely the extra hypothesis needed for 0EUU and the stronger-than-needed hypothesis for 01ZP. Neither the node nor this application assumes a separated target.

For step 7 `lem-weil-pbc-descend-smooth-qcqs` states smooth descent for arbitrary qcqs fixed models with an lfp arrow; the structure arrow has that property. I checked its hypotheses against 0C0C. The separate open-restriction smoothness node includes composition with the base open in clause (b), which the source-cover smoothness lemma then uses. The base-change node's statement explicitly includes smoothness in clause (2), despite its title referring to proper base change.

For step 8 the separated-descent node explicitly has no finiteness hypothesis on the arrow. I apply it to X_W mapping to W, not to a different diagonal. The over-pullback diagonal node explicitly identifies closedness of the base-changed diagonal with separatedness of the base-changed map. Closed-immersion target locality is then applied over the two open subsets of X times_S X, which really cover that target. The converse uses the actual closed-immersion base-change statement and the same diagonal comparison. I read 01ZQ and its proof, and did not take diagonal comparison from a definition node alone.

For step 9 I checked the exact statements and source texts of 0EUU and 01ZP. Both use fixed qcqs X_W and Y_W; the former requires local finite presentation, the latter only local finite type, both supplied in step 6. This step produces open-neighbourhood restrictions rather than claiming a local spectrum itself is an open covering member.

For step 10 the closed-immersion locality node states precisely locality for arbitrary open covers of the target, so it applies to Y_U and Y_W with inverse-image sources X_U and X_W. The converse uses the closed-immersion base-change node. For step 11 I wrote the elementary open-immersion locality argument from its definition: open image, global injectivity by choosing a target open around a common image point, and compatible inverse maps and sheaf maps. The base-change converse is the separate open-immersion base-change node. Only this last routine step is marked elementary. Every other substantial fact is an existing cited statement.

I checked edge cases: D a field gives U and V empty and T=S; D local gives T=S while U=V; an isolated closed component gives V empty and the argument glues disjoint pieces; empty source objects and arrows are permitted by spreading and gluing. Nonseparated finite-presentation schemes remain allowed throughout. In particular the proof never assumes an affine intersection of arbitrary affine source charts. Every step is shorter than 2000 characters, and there is no sublemma hidden in a long step. No SGA source or alternate chapter route is used.

The tool lemmas from other units are recorded under `split_report.tool_uses` as foundational black boxes. They do not replace a step of the current unit's argument. Verbatim citations were generated from the statements actually read, including all their hypotheses. The server's standalone review_split check passed before this report was written.

## Unfinished work

None for this stage-1 split. Existing dependency nodes retain their own stage status; no claim of completed Lean proofs is made.
