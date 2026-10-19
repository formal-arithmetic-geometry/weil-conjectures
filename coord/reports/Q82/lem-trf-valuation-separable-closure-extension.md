# Q82 stage-1 delivery: lem-trf-valuation-separable-closure-extension

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-valuation-separable-closure-extension.json`: statement unchanged, split into six proof steps; zero new nodes and zero new Mathlib leaves.
- `citations.json`: eight step/node entries, quoting the exact statements used.
- `report.md`: this report. Search evidence remains in `searches.jsonl`.

The first dry run found the newly synchronized `lem-trf-valuation-torsionfree-flat` from Q33. I opened it, verified that its statement supplies exactly the flatness implication needed, and replaced the proposed new leaf by this existing Mathlib leaf. The uncommitted draft is retained under sandbox-only `drafts/`, outside the delivery tree. No existing dependency is edited. Preparation scripts are not delivery files.

## Attachments

No attachment for the item. Project-source searches by the blueprint tag and by separable closure, valuation, height/rank and faithful flatness found no declaration asserting every clause of this item. Upstream master is reference material, not evidence of a finished proof.

`ValuationSubring.exists_comap_eq` belongs to existing `lemma-nagata-valuation-ring-extension`, and `ValuationSubring.comap_eq_of_toLocalSubring_le` belongs to existing `lemma-nagata-valuation-intersection`. Both are already recorded closed; I read their source at WeilConjectures/Mathlib/RingTheory/Valuation/LocalSubring.lean:31–64.

## WANTED

None for this split. Algebraic-height invariance is an existing cited interface, not a new proof of Temkin's valuation theory. All other proof sources were read in the local Stacks checkout.

## Corrections and route

The item was unsplit with an empty proof. Its statement is true and remains unchanged. I clarified its source description: Stacks 0ASH itself states the finite-extension value-group-index inequality, not the complete infinite algebraic-height/fpqc result. The existing `lem-trf-valuation-algebraic-height` supplies the height interface and is reused.

The current main-20261015 `lem-trf-local-term-locality.proof.md` quotes Varshavsky's contracting-correspondence theorem and normal-cone specialization. It does not literally state this valuation-extension lemma. I retain and explain the historical semistable-alteration/nearby-cycle ancestry, specifically the use in `lem-trf-valuation-semistable-dominates-stable` step 4. No unit or chapter record changes. The two Nagata results are generic valuation-theory tools, already Lean-closed, declared in `split_report.tool_uses`; no sk-i-curve-zero node supplies the extension/intersection conclusions.

Original item searches are preserved, and fresh msearch.py queries are recorded exactly with hit summaries and log digests. I tried two natural-language formulations of the whole item and of its flatness ingredient; all services answered. The HasExtension hits assume compatible valuations rather than constructing the required extension, and rank-at-most-one results do not prove arbitrary finite-height invariance. For the flatness ingredient I read `Module.Flat.flat_iff_torsion_eq_bot_of_isBezout` (Mathlib/RingTheory/Flat/TorsionFree.lean:93–94), `ValuationRing.instIsBezout` (Valuation/ValuationRing.lean:379–386), and `Submodule.isTorsionFree_iff_torsion_eq_bot` (Algebra/Module/Torsion/Basic.lean:838–840). This confirms the existing Q33 Mathlib leaf, rather than warranting a new node.

## Not duplicates

No new node is delivered. `lem-trf-valuation-torsionfree-flat` is reused verbatim, and the proposed duplicate `lem-trf-valuation-torsion-free-flat` is removed from dag/nodes in the sandbox. Existing height, Nagata extension/intersection, flat-local-hom and affine-spectrum/fibre-product nodes are all reused. Whole-DAG keyword/tag searches and blueprint_refs searches for 0539, torsion-free, torsion free, Bezout, separable closure and valuation/flatness were performed before the draft; the first dry run caught the subsequently synchronized leaf.

## Review by Q82

I read delivery-errors B–E in full, the node, parent use, current blueprint proof, sk-i-curve-zero unit, and sec-trace-formula chapter. This is the author's direct-delivery self-review, not an independent second reader.

I read Stacks algebra.tex 00IA (lemma-dominate), 052K (lemma-x-or-x-inverse-valuation-ring), 00HR (lemma-local-flat-ff) and 00HQ (lemma-ff-rings); more-algebra.tex 0ASH (lemma-inequality-general) and the entire statement/proof of 0539 (lemma-valuation-ring-torsion-free-flat); morphisms.tex 01U5 (lemma-flat-characterize); schemes.tex 01I4 (lemma-fibre-product-affine-schemes); and topologies.tex 022B (definition-fpqc-covering). No SGA source is used. There are no new-node sources to review. The existing torsionfree-flat leaf was checked directly against both 0539 and the Mathlib source/instance listed above.

Step 1 uses the statements of `lemma-nagata-valuation-ring-extension` and `lemma-nagata-valuation-intersection`. They allow an arbitrary field extension and provide a valuation ring with fraction field K^s, domination and the intersection equality. I checked the project declaration only as evidence for these already recorded nodes, not as a proof of the whole item. Step 2 uses exactly the order-isomorphism/equal-height assertion of `lem-trf-valuation-algebraic-height`. K^s/K is algebraic by hypothesis and W cap K is V by step 1. Thus its prime-ideal order isomorphism transfers the finite chain itself, with the same number of strict inclusions.

Step 3 proves torsion freeness directly in the field K^s, then applies `lem-trf-valuation-torsionfree-flat`. Its statement assumes no finite presentation, discreteness or PID condition, which is essential here. Step 4 applies `lem-weil-pbc-flat-local-hom-faithfully-flat`; its full statement explicitly supplies both faithful flatness and surjectivity on spectra. Both rings are local, and domination gives the maximal-ideal condition. Step 5 uses `lem-weil-pbc-flat-ring-map-iff-flat-affine`, whose statement is exactly the spectrum/ring-map equivalence. I corrected the tempting but invalid shortcut of using an every-affine-pair criterion from only the global pair. Step 6 uses `lem-weil-pbc-fibre-product-affine-spectra` for the preimage of each arbitrary affine open: it is the pullback, hence Spec(W tensor_V R). Surjectivity restricts to that preimage. `def-weil-pbc-fpqc-covering` then applies literally: one affine open of the source suffices over each affine open of the target. Empty opens use the empty family. No finite-presentation hypothesis is invoked and no arbitrary open subset is assumed affine.

Every cited node statement was opened in full. Each of the eight citations in citations.json is a verbatim part of the statement, and nothing is taken only from a dependency's proof. All theorem uses have the hypotheses actually available. No new node packages a clause of the item, and the six proof steps each carry their own argument.

I checked height zero (V=K, W=K^s), K already separably closed (W=V is possible), and nondiscrete higher-rank valuations. No step assumes a discrete value group or that W is a finite V-module. The locality condition matters: for positive-height V, the inclusion V to its fraction field is flat but not faithfully flat. For the reused flatness leaf I tested the zero module, a field base, free modules, and A/(a) for a nonzero nonunit a (neither torsion-free nor flat). These also show why the PID-only flatness leaf would not suffice for arbitrary valuation rings.

B: no new nodes, and existing statement/import metadata is retained. C: all non-elementary inputs are named and the citations give precisely the assertions used. D: the proof assembles existing tools without transferring the item to a new node. E: fraction fields, algebraicity, contraction, maximal ideals and the direction of the affine fibre product are correct. All steps are below 600 characters; none triggers the 2000-character hidden-lemma threshold. The preliminary server review_split passed; the final dry run is rerun after deduplication.

## Unfinished work

None in this one-level split. The existing algebraic-height node remains downstream and unsplit, as stage 1 allows. No Lean was written and no compiler or Lake command was run.
