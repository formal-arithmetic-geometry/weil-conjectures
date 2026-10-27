# Q76 — lem-sfb-coherent-bounded-below-rhom-stalk

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-coherent-bounded-below-rhom-stalk.json`: item, statement unchanged, five-step split using seven existing nodes. No Mathlib match.
- `citations.json`: one verbatim statement quotation for each of the seven step/node citations.
- `report.md`: this report.
- `searches.jsonl`: actual searches recorded by the required msearch command. No new nodes or Mathlib leaves.

## Attachments

None. Searched the live `lean/WeilConjectures/` by the exact blueprint tag and by derived-Hom/stalk and coherent/bounded-below concepts. The ordinary internal-Hom stalk results (`StalkInternalHomFinitePresentation.lean`) are not a derived comparison. `DerivedHomFiniteFreeModel.lean` computes one side and does not state this item. The existing DAG stalk-localization declaration concerns only two degree-zero modules and only their individual cohomology groups. No project declaration found states every clause of this item.

## WANTED

None. All sources needed are present locally; no SGA source used.

## Corrections and scope

The item was statement-only, not an existing reviewed split, and the sandbox contained no earlier item/report/searches. No released repair note exists. The statement is correct and is retained exactly. It is the coherent degree-zero case of Stacks 0GM8(2); perfect.tex 08E8 confirms that a coherent degree-zero object is pseudo-coherent. Instead of moving the conclusion into a general stalk-comparison node, the split supplies the finite-free calculation using already existing smaller lemmas.

The chapter and unit records, SETUP's three levels, GOAL, worker/stage-1 instructions and delivery-errors B–E were read. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-images proof. This is a generic Zariski module calculation inside the inherited auxiliary curve-duality route, not a change to any constructible-coefficient unit theorem. The inherited `blueprint.from.node` is null; its detailed place and via list are preserved. `blueprint_refs.py ancestor` reports null, and searches `0GM8` and `coherent.*stalk` found no blueprint duplicate; the broader stalk search and existing DAG nodes were read. No unit realization field is appropriate: this item is not the unit's key statement.

The Mathlib queries were run through msearch only. Read both LeanFinder phrasings, Loogle, LeanSearch, and grep outputs. They produce ordinary module stalk/localization maps, free sheaf presentations, Ext size results or unrelated ring-map stalk surjectivity; none computes this derived internal Hom for arbitrary bounded-below E. The item's inherited search records are retained and the actual new records added. No unavailable service was reported as no match.

## Not duplicates

No new nodes are proposed. The existing `lem-sc-derived-internal-hom-stalk-localization` and `lem-sc-ext-stalk-localization` do not subsume this item: they concern degree-zero second arguments and per-degree cohomology, whereas E here can have infinitely many positive nonzero cohomology degrees and the conclusion is in D(A). I reused `lem-sc-derived-hom-finite-free-model` on both the open ringed space and the singleton ringed space instead of creating a redundant projective-resolution lemma. In particular I did not use `lem-sc-derived-hom-projective-resolution` for general E: its statement allows only G[0].

## Unfinished work

None for this stage-1 split. No Lean files were written and no compiler, Lake or build tool was run. The cited existing lemmas retain their own downstream work.

## Review by Q76

I read cohomology.tex, lemma-stalk-internal-hom (0GM8), its reduction to lemma-pullback-internal-hom, and that lemma's bounded-below argument. I also read the actual derived-Hom construction in section-internal-hom and restriction lemma 08DL, perfect.tex lemma-identify-pseudo-coherent-noetherian (08E8), coherent.tex lemma-coherent-Noetherian (01XZ), algebra.tex lemma-resolution-by-finite-free (00LP), and modules.tex's kernel/cokernel stalk calculation preceding lemma-abelian (01AG). There are no new node sources to check.

Step 1 uses the statement of `def-kun-truncations`, not an unstated existence theorem: its explicit cokernel formula gives a termwise bounded-below complex and its stated cohomology formula proves the truncation is a quasi-isomorphism. This is valid in the abelian module-sheaf category, with no quasi-coherence hypothesis on E. The lower bound is a cohomology bound initially and becomes a termwise bound only after this step.

Step 2 uses `lem-sc-coherent-affine-free-resolution`, whose statement gives the affine neighbourhood, finite-free terms and augmentation quasi-isomorphism under precisely Noetherian X and coherent F. `lem-sc-derived-internal-hom-restrict-open` states the derived isomorphism for arbitrary derived arguments, not merely module sheaves. Cofinality of neighbourhoods inside U is written explicitly. No affine-intersection assumption is needed.

Step 3 uses `lem-sc-derived-hom-finite-free-model` exactly with its bounded-above first complex and bounded-below second complex. Its ringed-space statement also applies to the one-point space with structure ring A. The two finite-free-model applications do not require injectivity to survive taking a stalk, and the proof never claims that. `lem-weil-pbc-module-stalk-exact` explicitly states preservation of kernels and cokernels and therefore preserves cohomology and quasi-isomorphisms. The stalk augmentation is consequently valid and all its terms are finite free over A. I opened and read both cited node statements before using them.

Step 4 uses the exact degree and signed differential formula of `def-pur-hom-complex`. I checked the inequality: p <= b and p+n >= a give the finite interval a-n <= p <= b. The finite-free term identifies both Hom modules with the same finite power, and the common-neighbourhood argument proves that taking stalks commutes with the finitely many factors. The differential computation proves an actual complex isomorphism. Thus the elementary classification hides no general infinite-product preservation or derived base-change theorem.

Step 5 uses the construction and representative-independence stated by `def-pur-derived-internal-hom`. The comparison is calculated by germ evaluation after replacing the arguments, rather than by choosing an arbitrary isomorphism between models. Precomposition and postcomposition commute with germs; inverting the quasi-isomorphisms in that definition preserves the commuting squares. This verifies that the computed isomorphism is the canonical comparison and that its square for u:F->F commutes. This is a formal functoriality check of the displayed maps, not an appeal to the proof of the existing cohomological stalk-localization node. No functorial finite-free resolution is assumed: naturality belongs to the canonical germ comparison and passes through the representative-independent derived construction.

For C4, citations.json copies the relevant cited statements verbatim (full statements when needed), including the boundedness hypotheses; it contains all seven step/node pairs. For C1, the non-elementary geometric resolution, restriction, Hom-model and stalk-exactness inputs are cited; finite products, degree bounds, truncation and the componentwise differential/functoriality calculations are written out. Existing off-unit inputs are declared as generic tool uses in split_report, without editing any maintainer tool_uses field. The proof does not cite any new restatement or create a cycle intentionally.

I tested F=0, E=0, a field as local ring, and E a shifted single module. If the interval a-n <= p <= b is empty, both degree-n terms are zero, so the formula remains correct. A coherent sheaf of infinite projective dimension is allowed: P is only bounded above, and no regularity or finite projective dimension was used. E may be unbounded above and non-quasi-coherent. Empty X gives no point and hence a vacuous universal assertion. The bounded-below assumption is used exactly to avoid an infinite diagonal product. Every step is shorter than 2000 characters; no suppressed long-step lemma remains. No statement dispute or source error was found.
