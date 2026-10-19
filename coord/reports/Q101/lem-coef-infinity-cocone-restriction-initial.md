# Stage 1 report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-infinity-cocone-restriction-initial.json`: item split; no new nodes; no Mathlib leaves.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

## Attachments

None. I found no sorry-free project declaration stating the item exactly in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or the reference upstream tree.

## WANTED

- Kerodon Proposition 7.1.6.13, tag [02XB], for the relative-initiality theorem. It is online and was read, but is not archived under `literature/`; the proof is recorded as agent-written.

## Findings and corrections

The imported statement is mathematically coherent and was retained. It is strictly stronger than initiality in a fixed cocone category: the target cone `t` may have an arbitrary base diagram. The proof is split into four steps. Step 1 uses the existing join-cone calculus to identify right-join diagrams with coherent cocone triples and to compute their mapping spaces. Step 2 applies the colimit universal property from the coherent-cocone definition to show that the apex mapping space maps equivalently to the space of cocones with arbitrary apex. Step 3 takes the homotopy pullback along that equivalence and identifies the projection with restriction. Step 4 checks that this is the actual simplicial restriction map and that all mapping objects are Kan complexes. No new prerequisite node was needed: the existing join-cone statement already contains the needed mapping formula, and the coherent-diagram definition contains the colimit and Kan-space meanings.

## Not duplicates

- `lem-coef-infinity-cocone-restriction-initial` vs `lem-cbc-enhanced-functor-cone-calculus`: the existing node gives colimit universal properties for a fixed base diagram; this item compares maps from a colimit cone to arbitrary right-cone targets whose bases may vary.
- `lem-coef-infinity-cocone-restriction-initial` vs `lem-coef-infinity-join-cone-calculus`: the existing node gives the join/fat-cone equivalence and mapping formula but does not assert that a colimiting cocone is initial relative to restriction; that conclusion is the item.
- `lem-coef-infinity-cocone-restriction-initial` vs `lem-coef-infinity-final-index-colimit`: final-index evaluation is a different special colimit theorem and does not give the relative mapping-space statement for an arbitrary right join.

## Review by Q101

I read the target node, its blueprint ancestry (`prop-coef-integral-exceptional-adjoint`, paragraph 2), the full statements of `def-cbc-enhanced-diagrams-cones` and `lem-coef-infinity-join-cone-calculus`, and Kerodon 02XB. The statement's right join, interval-to-join cocone convention, arbitrary target base, and weak-equivalence conclusion agree with the source. I checked the edge cases `K=∅` (the claim reduces to initiality of the apex) and `K=Δ⁰` (an equivalence cocone gives the expected restriction equivalence).

For step 1, the join-cone statement explicitly supplies the triple model and its homotopy-pullback mapping-space formula, while the definition node supplies the coherent-cocone objects and transformations. For step 2, I verified that “colimiting cocone” means an initial object in the coherent cocone category, so every mapping-space fiber from the chosen cocone is contractible; the join mapping formula turns these fibers into the fibers of the apex-to-cocone map. For step 3, the second map in the homotopy pullback is therefore an equivalence, and projection to the first factor is a weak equivalence; this first factor is exactly the mapping space after restriction. Step 4 checks degreewise that the map is precomposition with `K ↪ K^{▹}` and uses the definition's Kan-complex clause.

I ran the required `msearch.py` searches for the item with LeanFinder, Loogle, grep, and LeanSearch (including a second phrasing). The ordinary-category hits (`Cocone.isColimitEquivIsInitial`, `IsColimit.homEquiv`, and ordinary Kan-extension declarations) were read and rejected because they do not state coherent mapping spaces in quasicategories. The search records remain in the node's `mathlib_searches`; no Mathlib match was found. I also searched the DAG and blueprint for the Kerodon tag, relative initiality, cocone restriction, and mapping-space formulations; no duplicate or blueprint node states this item. No Lean files, compilers, Lake, or live project files were touched.

## Unfinished work

No new nodes were created. The item is split and ready for the second reader's review and delivery.

## Second reading by Q101

I independently read Kerodon Proposition 7.1.6.13 (02XB), Example 4.6.6.8 (04J5), and Remark 7.1.5.9 (02WM) online, the item and both original dependencies in the shared DAG, and all three additional existing dependency statements used below. The item is the colimit dual of 02XB with the ambient functor landing in a point; arbitrary target boundary diagrams are essential and were retained. Its smallness, quasicategory hypothesis, right join, prescribed interval-to-join comparison, colimit hypothesis and full mapping-space conclusion agree. No Stacks tag states this infinity-categorical assertion. The item statement is unchanged and is not disputed. Kerodon's proof uses cocartesian fibrations; the delivered mapping-space proof is agent-written, rather than falsely attributed to individual sentences of that proof.

- Step 1: Checked against the complete statement of `lem-coef-infinity-join-cone-calculus`, the natural arrow/right-pinch comparison in `lem-coef-infinity-pinch-comparison`, and the full-faithfulness assertion of `lem-cbc-enhanced-functor-cone-calculus`; repaired. The explicit opposite operator reverses horns and join blocks, and the interval reversal gives the specified right cocone. The source's left-cone formula, applied to the reversed pair of objects, gives exactly the two maps with common target `Map_D(F, Δ_K y)`. The barycentric reversal and pinch comparisons justify homotopy types without incorrectly identifying right-pinched mapping simplicial sets under opposites.
- Step 2: Checked against the cocone dual explicitly included in `lem-cbc-enhanced-functor-cone-calculus` and the initial-object definition in `def-cbc-enhanced-diagrams-cones`; repaired. The original varying-boundary formula alone did not justify its assertion about a mapping space with boundary fixed. The cited fixed-cocone mapping-fiber formula and its colimit criterion now give precisely `q_y`, with no extra assumptions on `F`, `K`, or `y`; the empty-mapping-space case is covered explicitly.
- Step 3: Checked against the boundary projection in the join-cone statement and the fibration replacement, trivial-fibration boundary-lifting criterion, and homotopy-pullback clauses of `lem-coef-kan-quillen-right-proper`; repaired. Factoring the equivalence `q_y` yields a trivial Kan fibration; its pullback remains trivial by the displayed lifting-square argument. Thus the conclusion concerns the actual restriction map with arbitrary `G`, not merely an unnamed equivalent space.
- Step 4: Checked against the internal-functor and right-pinched definitions and the functor-quasicategory/Kan-mapping assertions of `lem-cbc-enhanced-functor-cone-calculus`; repaired. The definition node alone contains no theorem that these mapping spaces are Kan. The remaining degreewise precomposition check is elementary.
- New nodes: none. No elementary fact, duplicate, clause of the item, or unsearched potential Mathlib leaf has been introduced. B1–B7 therefore impose no new-node obligations.

Small cases checked: for `K = ∅`, a cocone is its apex, so the claim is precisely contractibility of maps from an initial object; for `K = Δ⁰`, the colimiting edge is an equivalence and the apex map is forced to be `μ b λ⁻¹`, including its coherent uniqueness; for `K = Δ¹`, the last object computes the colimit and gives the same restriction property. With an empty target quasicategory there is no diagram on the nonempty right cone, so the assertion is vacuous. In the nerve of vector spaces over any field, a two-point diagram gives the usual direct-sum universal property against an arbitrary target two-point cocone; the zero diagram gives the zero apex, including the empty shape. These checks introduce no hidden nonemptiness or invertibility hypothesis.

Independent duplicate/attachment searches used `rg` over the shared DAG, every chapter of the current blueprint tree, and the read-only slopmaster2 and exact-master source trees, by the item id, Kerodon tag, relative initiality, cocone restriction, and mapping-space terminology. The fixed-base cone calculus is a prerequisite, not this varying-base conclusion. No exact project attachment or duplicate was found. I independently ran `msearch.py` with grep (`relative initiality coherent cocone restriction` and `opposite quasicategory join mapping space`), LeanFinder (`opposite quasicategory join mapping space`), and Loogle (`"Cocone", "IsInitial"`); their actual outputs are in `searches.jsonl` and were appended to the item's searches. The semantic join hits and the three Cocone/IsInitial hits have ordinary Category instances and Hom sets; the grep queries had zero hits. They do not prove the quasicategory mapping-space statement. I read the ordinary Mathlib `Cocone.isColimitEquivIsInitial` declaration at `CategoryTheory/Limits/ConeCategory.lean:345` and its ordinary-category context.

Changes: retained all four steps and the item statement; expanded the duality in Step 1; repaired the fixed-boundary inference in Step 2 using the existing exact criterion; supplied the model-structure citation and pullback argument in Step 3; repaired the Kan-space citation in Step 4; refreshed `proof_deps`, `proof_origin`, `split_report`, search records, and `citations.json`. Each citation now quotes the cited node's complete statement verbatim, so the relevant clauses are reviewable without relying on a proof. The generic off-unit `lem-cbc-enhanced-functor-cone-calculus` use is requested in `split_report.tool_uses`; it supplies a coherent category tool, not an alternative route through another unit. There are still zero new nodes and zero Mathlib leaves. Only the named sandbox was modified; no Lean files or compilation/build tools were used.
