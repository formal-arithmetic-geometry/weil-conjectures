# Worker report: lem-coef-triangular-cofibrant-resolution

## Files written

- `dag/nodes/sec-six-functors/lem-coef-triangular-cofibrant-resolution.json`: the assigned statement, now split with five proof steps; no new nodes were needed.
- `citations.json`: verbatim statement quotes for every cited step/node pair.

## Attachments

None. No finished declaration for this exact statement was found in the project source.

## WANTED:

- WANTED: Lurie, *Higher Topos Theory*, Appendix A.3.3, especially Proposition A.3.3.2 and Remark A.3.3.5, archival copy for the project literature.
- WANTED: Bergner, *A model category structure on the category of simplicial categories* (math/0406507), Sections 1--2, archival copy for the project literature.

## What was wrong or incomplete

The imported node had a complete statement but no proof, status `unsplit`, and no split report. Its existing statement and dependencies were retained. The item is an auxiliary agent-formulated two-block collage lemma; the blueprint ancestor `prop-coef-integral-exceptional-adjoint` uses this construction in its directed-gluing support, but does not state it as a numbered theorem. No statement change was required. The nearby `lem-coef-poset-filtered-cofibrant-resolution` and `lem-coef-extreme-bimodule-attachment` nodes are related model-category results but do not state the prescribed two-block collage with both diagonal resolutions and endpoint module cofibrancy, so neither is a duplicate.

## Not duplicates

- `lem-coef-triangular-cofibrant-resolution` vs `lem-coef-poset-filtered-cofibrant-resolution`: the latter resolves a graded directed category and its lower-filtration diagram; it has no prescribed two diagonal resolutions or bimodule rows/columns.
- `lem-coef-triangular-cofibrant-resolution` vs `lem-coef-extreme-bimodule-attachment`: the latter computes a homotopy-pushout mapping square for an extreme arrow; it does not construct a Bergner-cofibrant two-block collage.
- `lem-coef-triangular-cofibrant-resolution` vs `lem-coef-fixed-object-simplicial-free-calculus`: the latter supplies the fixed-object free-cell model structure, while this item applies it to a projectively cofibrant mixed bimodule and proves the local trivial fibration and row/column conclusions.

## Review by NG

I reread the assigned node, its two statement dependencies, the unit record, the chapter record, and the blueprint proof of `prop-coef-integral-exceptional-adjoint`. I also read the full statements of `lem-coef-simplicial-projective-model-calculus`, `lem-coef-fixed-object-simplicial-free-calculus`, and `lem-coef-fixed-object-free-arrow-adjunction`, which are the only DAG nodes cited by the proof. Step 1 uses the projective model structure's objectwise weak equivalences and fibrations to obtain the mixed mapping bimodule replacement; its hypotheses are exactly the smallness and simplicial-category hypotheses in the item. Step 2 is the direct associativity and unit check for the two commuting module actions. Step 3 uses the enriched free-diagram adjunction and the fixed-object free-cell/Bergner characterization to identify each bimodule cell with a mixed free-arrow attachment; the reverse-empty condition ensures that no additional mixed words or relations occur. Step 4 restricts the same cell filtration to a row or column and checks that tensoring a boundary cell with the other diagonal mapping simplicial set preserves cofibrancy, giving the two endpoint projective-cofibrancy clauses. Step 5 checks diagonal, mixed, and reverse mapping pairs separately, then records functoriality and the empty/noninjective edge cases. Every cited quote in `citations.json` is copied verbatim from the cited node. I ran the required server-side `srvcheck.py ... check_dag` before this report was written; it admitted the check without a reported finding.

## Unfinished work

None. No Lean files were written and no compiler or build tool was run.
