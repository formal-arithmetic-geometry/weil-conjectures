# Q45 — lem-trf-projective-determinant-chart-descent

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-projective-determinant-chart-descent.json`: statement node, split into nine steps; Mathlib searches found no match. The statement, statement dependencies and inherited blueprint provenance are unchanged.
- `citations.json`: 20 verbatim statement quotations, one per step/node citation.
- `report.md`: this report. `searches.jsonl` records the actual searches; `write_split.py` is the sandbox-only generation script.

New nodes: 0. New Mathlib leaves: 0. No Lean files or repository files written, no compilation or git commands run. Only the required delivery tool will build the delivery commit.

## Attachments

None for the item. Searched `lean/WeilConjectures/` by its exact id and by exterior-socle, annihilator, determinant-module and localization terminology. The project has general exterior localization and sheaf determinant declarations, which do not state all the socle chart and supplied tensor descent clauses. Existing `new-v2-generic-exterior-power-localization` already records the general localization result; I reuse it without changing its attachment record.

## WANTED

None. The source material required here is present.

## Corrections and source observations

No statement dispute or correction. The source's Tag 0FJA gives the annihilator model and suggests checking localizations, but does not supply those checks. The first proof of 0FJB also omits detailed verification of the wedge comparison. This item concerns only the chart realization and descent of supplied comparisons, so it does not recreate the exact-sequence comparison or assert its existence without proof. The proof is marked agent-written because the fraction argument and the elementwise descent verifications have been expanded by Q45.

The current blueprint under `literature/blueprint/latest/` was read, specifically `sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`. The inherited provenance is a deep auxiliary determinant input below the local-term theorem's semistable branch. Neither chapter nor unit is changed. This item is not the unit's key node.

## Unfinished work

None for this one-level split. Its reused unsplit/split dependency nodes keep their existing states and ownership. Delivery and independent maintainer review are the remaining process steps.

## Not duplicates

No new node pairs: no nodes were created. Whole-DAG searches for Tags 0FJA, 0FJ9, 00EK, exterior basis/localization, finite-projective covers and descent located the existing definitions and generic tools used below. `blueprint_refs.py search determinant`, `annihilator` and `00EK` found no blueprint node stating this complete item; its `same_as` remains empty. The generic scalar-comparison node `lem-trf-projective-exterior-scalar-comparisons` includes arbitrary base change and compatibility with short-exact-sequence determinant maps; it is not a substitute here and depends on the parent exact-sequence item, so using it would be circular. It is not cited.

## Review by Q45

I read Stacks `more-algebra.tex`, Tag 0FJ9 (`section-determinants`), Tag 0FJA (`remark-determinant-as-socle`) and the first and second proofs of Tag 0FJB (`lemma-det-ses`). I also read `algebra.tex` Tag 00DM (`section-tensor-algebra`, including the finite-free exterior basis), Tag 0C6F (`lemma-tensor-algebra-localization`), Tag 00EK (`lemma-cover-module`, statement and proof), and Tag 00NX (`lemma-finite-projective`, particularly the finite locally free implication). The tensor-localization statement used is the existing node for 00DL, whose fraction formula was checked. No new node needs a source review.

For step 1 I opened `new-v2-generic-exterior-power-localization`, which explicitly includes every degree, arbitrary modules, and multiplicative subsets containing zero; it really supplies localization of the pure-wedge map. `def-weil-pbc-exterior-algebra` supplies the direct-sum grading and pure-wedge spanning. The full-algebra assertion is spelled out by finite support and a product of finitely many denominators, rather than attributed to the degreewise node. The socle definition gives the actual exterior-algebra chart map, and the localization definition gives the fraction and equality criteria. The successive-map identity is checked on pure wedges, not assumed.

For step 2 the only quoted statements are the socle and localization definitions. Finite generation comes from the finite-free retraction already assumed in the item. I explicitly choose one annihilating denominator for each of finitely many products with generators and multiply them. This proves the entire restriction/localization comparison without assuming localization commutes with an infinite intersection or citing flatness for an unstated kernel theorem. It is a direct fraction argument, so marked elementary.

For step 3 the exterior-basis node states all basis vectors, vanishing above the rank, and the degree-zero normalization. Along with the graded direct sum from the exterior definition it supports the coefficient expansion. For each missing index j, the coefficient of the uniquely indexed wedge in x wedge v_j is plus or minus c_I; there can be no hidden cancellation between different I. This proves the free socle calculation in the proof rather than creating a new node repeating the item's chart clause. Only multiplication by a unit sign is used, so no division by 2 or characteristic restriction is hidden.

For step 4 the invariant-basis-number node explicitly assumes a nontrivial commutative ring. I apply it only on nonzero overlaps, and explain that coordinate maps localize to inverse coordinate maps. Zero overlaps are handled separately by uniqueness of maps of zero modules. The transitions are identified with the restrictions of the intrinsic socle maps, so the cocycle follows by cancellation. No claim about equal ranks over the zero ring is made. I read the Mathlib invariant-basis-number instance at `LinearAlgebra/InvariantBasisNumber.lean:313` and the exterior basis at `ExteriorPower/Basis.lean:97` as corroboration of existing leaves.

For step 5 I opened `lem-sc-affine-standard-cover-finite-projective`: it requires exactly a finite unit-ideal principal cover with finite free localizations and imposes no finite-presentation assumption on the global module. Our socle localizations are rank-one free, so these hypotheses hold. `lem-weil-pbc-cover-module-exact` explicitly states both injectivity and existence/uniqueness of gluing compatible elements of any module. It supplies the comparison with every other realization of the same charts, without an uncited effective-descent theorem. Defining D to be the actual annihilator construction avoids making an object out of an unproved existence choice.

For step 6 that same cover lemma detects equality on the common refinement, whose unit-ideal condition is verified by multiplying two finite expressions for 1. Basis independence follows from the equality inside the exterior algebra proved in step 3. Localization compatibility is checked by step 1 on pure wedges and the explicit fraction comparison of step 2; it does not use the more general scalar-comparison node. The case E=0 uses the degree-zero identification, while localization at a set containing zero has zero codomain.

For step 7 I opened `lem-weil-pbc-localization-tensor-product`: it gives the canonical tensor-localization map and fraction formula for arbitrary modules and arbitrary multiplicative subsets. It therefore identifies the actual source P_f with the tensor of the determinant charts. The supplied overlap compatibility makes the displayed q_a a compatible family in Q_f; 00EK glues it. Additivity, scalar compatibility and uniqueness follow from its injectivity assertion. The proof checks equality on all fractions, so equality merely on images of global elements is not confused with equality on localized modules.

For step 8 inverse compatibility is obtained by inverting the given compatibility equation. I use 00EK on P to glue the inverse images, and on P and Q to detect the inverse identities. No projectivity of P or Hom-localization theorem is assumed. Step 9 checks refinement and localization using the same elementwise uniqueness and the tensor fraction formula, over the localized ring where the images of the original covering elements still generate 1. It includes the zero-ring localization.

I checked B1–B10, C1–C8, D1–D5 and E1–E7 of the delivery-error checklist against these steps. In particular every non-elementary tool is a node citation whose statement was opened and quoted verbatim in `citations.json`; the extra arguments are finite coefficient/fraction calculations explicitly written out. No new leaf, definition, duplicate, hidden source tag citation or relabelled clause was introduced. Generic off-unit tools are declared in `split_report.tool_uses`, with their actual purpose; Mathlib leaves need no such declaration. I checked the dependency closure of every cited node: none reaches this item. All nine steps are below 900 characters, so no step exceeds the 2000-character long-step review threshold.

Small cases checked: R=0; E=0; free rank one (the annihilator is the degree-one summand); rank two over characteristic 2; E of different ranks on different components of a product ring; a zero overlap with incompatible chart rank labels; a multiplicative set containing zero; and a redundant zero principal-open chart. The coefficient argument and denominator products work in all these cases. In the zero ring even the empty cover is legitimate: 00EK says its sole global module is zero, and the module criterion gives the same conclusion.

## Mathlib searches read

Six actual searches, with two distinct semantic phrasings, were run through the required msearch command and appended to `searches.jsonl`. LeanSearch and LeanFinder returned exterior definitions, universal properties, pairing formulas and free-locus/finitely-presented localization facts, not this item. Loogle `ExteriorAlgebra, Module.Projective` and both socle/annihilator grep patterns found no match. I opened `ExteriorAlgebra.hom_ext` (Basic.lean:136), `ιMulti_span_fixedDegree` (Basic.lean:344), and `lhom_ext` (OfAlternating.lean:154); these supply extensionality/spanning tools, not a one-line specialization proving the item. All search records retain their exact query text and actual results; no service was unavailable.
