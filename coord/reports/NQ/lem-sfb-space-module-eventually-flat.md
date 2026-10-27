# Stage-1 report: lem-sfb-space-module-eventually-flat

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-space-module-eventually-flat.json: item, statement unchanged, split into five proof steps. No Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-module-flat-chart-test.json: one new statement-only node, unsplit, no Mathlib match. It states geometric-stalk relative flatness versus ordinary relative flatness on any surjective etale scheme atlas; it has no inverse system or eventual-flatness conclusion.
- citations.json: a verbatim statement quote for each of the 19 step citations.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag and eventual-flatness terminology found scheme results such as AlgebraicGeometry.exists_eventually_isFlatOver_of_limit, not the algebraic-space module statement. The existing scheme declaration assumes Noetherian stage rings; it cannot attach this item.

## WANTED

None. The required Stacks sources are present.

## Issues found and corrected

The item was unsplit with no proof. Its statement is correct and unchanged. Its fixed blueprint provenance already has node=null with a detailed inherited place and via chain; the new supporting lemma inherits that recorded ancestry, adding the item's id to via. The current latest blueprint's direct-image proof has since replaced the historical alteration paragraph; this is inherited supporting material, not a proposed change to the unit or chapter route. I read the current latest unit and direct-image proof as well as the DAG unit and chapter.

An important hypothesis distinction is that lem-pc-flat-module-descent and its preorder variants assume Noetherian stage rings. I did not use them. The existing lem-pc-affine-flat-module-descent states the needed result for arbitrary rings, so no new scheme-limit theorem was created. Likewise lem-sfb-space-eventually-flat concerns morphisms, not arbitrary modules, and lem-sfb-space-module-base-change-flat-proper-support requires proper support. Neither supplies this item's missing module argument.

## Not duplicates

lem-sfb-space-module-flat-chart-test vs lem-sfb-stack-fibre-regular-slice-flat: the existing node constructs a flat regular slice in a stack from regular equations; the new node compares two definitions of relative flatness for an arbitrary quasi-coherent module and any atlas.

lem-sfb-space-module-flat-chart-test vs lem-sfb-space-flat-etale-ringed-comparison: the existing node concerns the structure module of a morphism and flatness as an inverse-image-ring module sheaf; the new node concerns any quasi-coherent module and compares geometric relative stalks with ordinary Zariski relative stalks on an atlas.

lem-sfb-space-module-flat-chart-test vs lem-sfb-flat-space-derived-pushforward-base-change: the existing node is derived base change for a flat qcqs morphism and arbitrary quasi-coherent derived objects; it gives no atlas criterion for relative flatness of an arbitrary module.

lem-sfb-space-module-flat-chart-test vs lem-sfb-space-tor-independent-relative-amplitude: the existing node preserves Tor amplitude across a Tor-independent square; it does not compare geometric and ordinary relative module stalk flatness.

lem-sfb-space-module-flat-chart-test vs lem-sfb-space-strict-local-flatness: the existing node identifies geometric local rings and detects flatness of a morphism's ring map. It does not detect relative flatness of an arbitrary module on the source. The new node is the module version, Tag 05VU rather than the morphism criterion Tag 04NG.

lem-sfb-space-module-flat-chart-test vs lem-sfb-space-quasicoherent-geometric-stalk-tensor: the existing node supplies only a tensor isomorphism for stalks. To turn it into the new equivalence one still needs faithful-flat descent for module flatness over the unrelated base local ring and the strict-henselization flatness equivalence. The new node isolates that non-elementary relative-flatness argument rather than hiding it in the item.

## Review by NQ

I read Stacks spaces-limits.tex Tag 08K0 (lemma-descend-flat), including both affine charts, its module hypotheses and its appeal to the scheme theorem. In this item's affine-base specialization the target chart is simply the identity. I read limits.tex Tag 05LY (lemma-descend-module-flat-finite-presentation), especially its affine reduction, and algebra.tex Tag 02JO (lemma-flat-finite-presentation-limit-flat), including part (3)'s cartesian module and algebra systems. For the new node I read spaces-morphisms.tex Tag 05VU (lemma-flat-at-point), its statement and full proof: the proof works with any chosen chart diagram, identifies the geometric stalk as the ordinary stalk tensored with the strict henselization of the source local ring, uses faithful-flat descent for relative module flatness, and then flat.tex Tag 05VL (lemma-flat-up-down-henselization) for the target local ring. Taking the target chart to be the identity and applying this at all points gives exactly the new statement. The passage from some to any chart is supported by that proof, not inferred from the morphism-only criterion.

Step 1 uses the affine-atlas conclusion of lem-trf-space-qc-finite-affine-atlas-refinement. Quasi-compactness of the initial space follows directly by testing its quasi-compact morphism against the given affine base. The local-property chart test explicitly includes local finite presentation and permits the identity target chart. Finally lem-weil-pbc-lfp-affine-opens-finite-presentation gives finite presentation of the whole affine coordinate ring map; I read morphisms.tex Tag 01TQ (lemma-locally-finite-presentation-characterize). No separatedness of the space or affine overlaps is assumed.

Step 2 uses lem-sfb-space-module-pullback-quasicoherent only for quasi-coherence. The etale restriction and composition clauses of lem-trf-space-chart-adjunction-tensor-realization identify the atlas pullback with slice restriction, so the existing local finite free presentations restrict. The scheme Zariski-etale equivalence gives the Zariski module, and lem-sfb-scheme-etale-module-exact-finiteness-comparison explicitly preserves and reflects finite presentation without a Noetherian hypothesis. The final sections assertion is precisely clause (b) and the final sentence of lem-weil-pbc-quasi-coherent-finite-type-affine; I read properties.tex Tag 01PC (lemma-finite-presentation-module). This avoids silently assuming finite presentation is part of the bare category equivalence.

Step 3 uses the fibre-product and covering statement of lem-trf-space-fibre-products-etale-covers to keep surjective etale atlases at all stages and at the limit. The stated all-affine clause of lem-weil-pbc-limit-affine-transition supplies the ring colimit; the specified affine-spectra fibre-product theorem gives the tensor rings. The canonical composition comparison from the chart-adjunction theorem and the scheme pullback comparison from the Zariski-etale equivalence identify the same module, without selecting a replacement model. The affine-pullback-sections theorem supplies the module section tensor, and the displayed balanced tensor formula and its inverse identify it with the base-ring tensor used by 02JO. I checked that the maps to the original space agree by the Cartesian square, and that no non-affine scheme was treated as affine.

Step 4 uses the new 05VU chart criterion for the actual geometric-stalk hypothesis, then the whole-affine-open specialization of lem-pc-affine-chart-relative-flat-criterion (morphisms.tex Tag 01U4, lemma-flat-module-characterize). The existing affine module descent theorem has arbitrary stage rings. Its two algebras are R_i0 and B_0; the former is finitely presented over itself, the latter is finitely presented by step 1, and its module is finitely presented by step 2. The colimit and all tensor identifications are from step 3. I checked every hypothesis of that node rather than invoking its proof. The elementary multiplication isomorphism identifies R_k tensor R_i0 with R_k and gives the exact base-ring action. Its conclusion already gives every later stage; the support-bearing space base-change lemma is unnecessary.

Step 5 uses the converse direction of the same affine relative-flatness criterion, then the converse of the new chart criterion on the actual surjective atlas at each k. Both are global equivalences with exactly these ordinary versus geometric module stalks. Nothing is deduced merely from a definition of flatness or from the morphism-only criterion. No additional persistence theorem is hidden in this step.

I opened and read the statement of every node used by these five steps before copying the citation quotes. The new statement was searched against the whole DAG by 05VU and flatness/chart terminology, the whole blueprint using blueprint_refs.py (05VU, relative flatness, flat chart, module flat, geometric stalk), and the project Lean source. I read all five existing source-tag overlaps listed above. Searches in searches.jsonl completed before the pause; their logged results were reused. I added a second semantic phrasing and LeanSearch. The actual returned signatures concern scheme morphisms or algebraic flat modules and do not specialize to arbitrary quasi-coherent modules on algebraic spaces. The local Mathlib Flat.lean confirms the scheme-morphism scope of the apparent stalk matches. All recorded queries were actually run with msearch.py; no service failure is recorded as absence.

Edge cases checked: a constant or singleton index system, zero module, empty space/atlas (Spec 0), zero stage rings, and an empty limit although earlier sources are nonempty. The algebra theorem allows all these and forces eventual vanishing/flatness as appropriate; no nonzero-ring assumption is needed. All module pullbacks are ordinary tensors and are coherent with iterated base change. A local dependency scan found no path back to the item. Each proof step is below 2000 characters; no long step hides a lemma. The only new node is statement-only and strictly smaller than the item: it contains no finiteness or limit descent. Elementary tensor rebracketing remains in step 3. I reviewed delivery-errors B through E against these objects and hypotheses. No statement dispute, source-dependent target change, or SGA source is involved.

## Unfinished work

The supporting chart criterion remains a named, searched statement-only node as required by a one-level stage-1 split. No Lean was written, no compiler or build command was run, and no repository or launcher file was edited. Server dry run and push follow this report.
