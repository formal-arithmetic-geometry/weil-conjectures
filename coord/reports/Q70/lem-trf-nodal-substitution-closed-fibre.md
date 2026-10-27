# Stage-1 report: lem-trf-nodal-substitution-closed-fibre

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-nodal-substitution-closed-fibre.json`: item, statement, now split into six steps; no Mathlib declaration supplies the entire item.
- `citations.json`: ten entries quoting the exact statements of the eight existing nodes used by the six proof steps.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint id, nodal substitution, formal-local structure, and the nodal equation found no declaration stating the item. Occurrences of nodal geometry in duality and lisse-cover files do not state this result. The existing coefficient-kernel node covers only the coefficient-map kernel, not this item.

## WANTED

None. All sources used are available in the read clone.

## What needed repair

The item had no proof. Its source suppresses the construction of the complete-target evaluation, the coefficient-quotient kernel argument, and the justification that agreement on coefficients and variables gives agreement on all series. The split supplies these arguments without changing any hypothesis or conclusion. The chosen isomorphism theta is retained throughout; no canonical coordinate choice is substituted for it.

The source's displayed special-fibre map repeats “x maps to” in both entries, and its last display says “v maps to” where the second source variable is y. These are typographical slips: the source introduces two coordinates u and v, and the item's statement already uses the intended two-variable map. No statement correction is needed.

The latest blueprint files for `sk-i-curve-zero` and `lem-trf-local-term-locality` use contracting correspondences; the item's blueprint provenance explicitly records a historical nodal-algebra branch. I retained that provenance and the assigned algebra statement. This delivery neither replaces a unit step nor asserts that nodal substitution proves the current local-term theorem.

## Unfinished work

None for this one-level split. Every non-elementary input is an existing node, whose own later work is outside this item.

## Searches and reuse

The sandbox initially contained only dispatcher brief markers, so there was no earlier proof, report, or search log to recover. I searched the entire DAG by power-series, complete-quotient, evaluation, coefficient-reduction, and nodal keywords, and searched the imported blueprint with `tools/blueprint_refs.py search` for power series, adic substitution, nodal, and coefficient reduction. I also read the latest blueprint chapter, unit, and ancestor statement/proof directly. The ancestor command identifies `lem-trf-local-term-locality` as the nearest blueprint node. No blueprint node states this algebra lemma in another form; `same_as` remains empty.

The five new Mathlib searches are recorded exactly in the item and in the command-generated log: LeanFinder in two phrasings, Loogle, LeanSearch, and source grep. I read the returned types: Weierstrass results concern one-variable distinguished quotients or division, substitution results concern general evaluation or substitution into series, and coefficient-kernel results supply only part of the argument. I read the available local `MvPowerSeries/Evaluation.lean` implementation of `eval₂Hom`, including its topological completeness hypotheses. The Loogle service returned `MvPowerSeries.ker_map_of_fg` from `MvPowerSeries/Ideal`, but that module is absent from this read clone's pinned Mathlib; I do not certify a Mathlib leaf from it. The already existing project node `lem-sbc-mv-power-series-quotient-kernel` states the needed algebraic kernel result independently. No new search is represented as an unavailable service or a full match.

## Not duplicates

No new nodes were created. In particular the ambient-ring, evaluation, and coefficient-kernel facts were reused rather than renamed.

## Review by Q70

I read Stacks `curves.tex`, Tag 0CBX (`lemma-formal-local-structure-nodal-family`), including the correction iteration and the displayed completed nodal map in its final paragraph. This item is the substitution and closed-fibre part only; it does not use flatness, convergence of the correction iteration, or surjectivity of C to B. I read the chapter/unit records and their current latest blueprint counterparts, and checked the inherited historical provenance against them.

For step 1 I read the exact statements of `lem-weil-pbc-power-series-noetherian`, `lem-weil-pbc-power-series-local-ring`, and `lem-weil-pbc-power-series-complete-over-complete-base`. The first applies to two variables over Noetherian A, the second describes the maximal ideal by constant coefficient, and the third applies to the combined ideal because A is complete for m. I wrote the decomposition F=F(0)+xG+yH explicitly to identify that ideal. The source for the Noetherian assertion was checked in Stacks `algebra.tex`, Tag 0306 (`lemma-Noetherian-power-series`). The two other existing nodes are agent-formulated power-series algebra tools; their full statements, rather than an implicit claim from their proofs, supply exactly what is used.

For step 2 I read `lem-weil-pbc-complete-local-quotient` and Stacks Tag 0325 (`lemma-quotient-complete-local`). Its proper-ideal hypothesis matters: xy-h lies in the maximal ideal because h lies in m, so the quotient is nonzero. The theorem supplies all three assertions about C, including completeness for its own maximal ideal.

For step 3 I read `lem-weil-pbc-power-series-adic-evaluation`. It states the map, its values on constants and variables, and the exact truncation formula modulo n^N. Its hypotheses require u,v in n and completeness of B for n, both present in the item. I checked the cited universal-property context in Stacks `more-algebra.tex`, Tags 07NL (`lemma-power-series-ring-over-Cohen-fs`) and 07NN (`lemma-embed-map-Noetherian-complete-local-rings`); the generic evaluation theorem is the existing node's explicit algebraic formulation. Factoring through xy-h is written out from uv=alpha(h), and locality follows from the maximal ideal containment. No finite-type or flatness condition is introduced.

For step 4 I read `lem-sbc-mv-power-series-quotient-kernel` in full, including its finitely-generated-ideal hypothesis. Noetherianity of A gives that hypothesis for m. I checked that surjectivity is supplied independently by lifting every coefficient; I do not take it from a kernel-only statement. I wrote out the inverse-image-of-(xy) calculation using a lift of its multiplier, so the claimed rho is a bijective quotient map preserving constants and both variables. This avoids citing the proof of the kernel node for a stronger result.

For step 5 I again checked the complete-local-quotient statement, now with R=B and I=mB. Locality of alpha ensures mB is contained in n, hence proper. I read the whole statement of `lem-weil-pbc-power-series-universal-property-complete`, including its uniqueness clause for ring maps with fixed coefficients and variables. The target ideal here is n/mB, not mB; the quotient theorem supplies completeness for precisely that target ideal. Both maps from A[[x,y]] have coefficient map A to k to D because theta is a k-algebra isomorphism. Their variable images agree by the assumed reductions of u and v. Thus uniqueness really proves equality for arbitrary infinite series; agreement only on polynomial generators was not used as an unsupported inference.

For step 6 I read `lem-weil-pbc-quotient-local-structure` and the local-power-series statement again. The quotient-local lemma states the maximal ideal and the nonzero local structure, and its containment hypotheses hold for (xy) inside (x,y) and mB inside n. An isomorphism preserves the unique maximal ideal, giving n/mB=(u,v) in the quotient; pulling this ideal back gives exactly n=mB+(u,v)B. The identification with a_C B follows from its stated generators. I wrote out both residue-field quotients, using the chosen theta for B, so their k-identifications respect the given base map.

I checked the small cases A=k and h=0, yielding the ordinary node; A=k[[t]] with h=t and the standard model B=A[[x,y]]/(xy-t); nonreduced complete bases with h=0; and arbitrary, rather than standard, theta. The proof never divides by h, assumes h is regular, assumes A injects into B, or assumes B is flat. A zero target is excluded already by the given isomorphism with the nonzero ring k[[x,y]]/(xy). The properness checks also exclude a zero hypersurface. The statements and the proof remain valid in positive and mixed characteristic.

Against delivery-errors B--E: every cited fact has an existing node and its exact statement was read; the citation file quotes those statements verbatim. There are no newly invented definitions, clause-restatement nodes, or unsearched new nodes. Every proof step has its source and its uses, and all six are marked non-elementary because each invokes a substantive existing algebra lemma. All steps are shorter than 2000 characters. I checked that none of the eight reused dependencies has a dependency path back to this item. The eight off-unit dependencies are explicitly declared in split_report.tool_uses as generic algebra tools. The item statement and all maintainer-owned fields were retained unchanged. No Lean was written and no compiler, Lake, local DAG checker, or repository git command was run.
