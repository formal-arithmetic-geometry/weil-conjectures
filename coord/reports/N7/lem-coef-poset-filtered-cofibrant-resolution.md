# Worker report: lem-coef-poset-filtered-cofibrant-resolution

## Files written

- `dag/nodes/sec-six-functors/lem-coef-poset-filtered-cofibrant-resolution.json`: item split into seven proof steps; no new nodes.
- `citations.json`: verbatim statement quotations for every cited node in every step.
- No Mathlib leaves or new unsplit nodes were created.

## Attachments

No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this item. A keyword and blueprint search found no declaration tagged `(blueprint: lem-coef-poset-filtered-cofibrant-resolution)`.

## WANTED

WANTED: HTT archival copy, Definition A.3.5.7 and Lemma A.3.5.9, for `lem-coef-poset-filtered-cofibrant-resolution`; the online PDF was read on 2026-10-17 but is not present in `literature/`.

## What was checked and corrected

The imported item had an empty proof and no proof dependencies. I retained its statement and existing blueprint ancestry, then supplied the explicit fixed-object small-object proof following HTT Appendix A.3.5. The construction uses the already existing fixed-object simplicial-category model structure, free-arrow adjunction, cell-word filtration, small-object factorization, Kan model structure, and localization/Dwyer–Kan definitions. No duplicate node was needed: each used result already exists in the DAG. The first draft cited the localization-universal-property node for the generating cofibrations; I removed that citation after checking that the generating sets are stated directly in `lem-coef-simplicial-interval-lifting`.

## Review by N7

I read the item source (HTT Definition A.3.5.7 and Lemma A.3.5.9, pp. 894–895 of the online PDF) and the current blueprint proof that places this as the simplicial foundation for `prop-coef-integral-exceptional-adjoint`. The source requires a partially ordered grading, empty mapping spaces in the decreasing direction, a same-object enriched functor whose mapping maps are trivial fibrations, preservation of the grading, and projective cofibrancy of all lower subcategories. I checked that the imported statement includes all of these and explicitly retains the empty-poset and no-largest-element edge cases.

Step 1 uses the statements of `lem-coef-simplicial-interval-lifting` for the fixed-object category and its generating cofibrations, and `lem-coef-fixed-object-free-arrow-adjunction` for the attaching maps. Step 2 uses the free-arrow adjunction and `lem-coef-small-object-cell-factorization`; the finite boundary of each standard simplex gives the required smallness. Step 3 uses the small-object factorization and `lem-coef-scat-fixed-object-pushout-comparison` to realize each attachment with the same object set. Step 4 uses the exact word filtration statement `lem-coef-scat-arrow-cell-word-filtration`, the free-arrow adjunction, and `lem-coef-kan-quillen-right-proper`; the nondecreasing grading ensures forbidden mapping spaces remain initial and the right map has the boundary lifting property. Step 5 is an elementary restriction of that word presentation: a word ending at grade at most `a` cannot pass through a larger grade, so the lower subcategory sees exactly the cells whose target grade is at most `a`. Step 6 uses the fixed-object generating cofibrations and free-arrow adjunction to construct a compatible lift against any objectwise trivial fibration of diagrams, cell by cell and at limit stages. Step 7 is elementary from the definition of Dwyer–Kan equivalence in `lem-coef-simplicial-inversion-universal-property`; it also checks the empty and equal-grade/loop cases.

For every cited node I opened its statement and copied the complete statement into `citations.json`; each quote contains the precise fact used by its step. I checked hypotheses at the construction points: all object sets and attaching families are small, each new arrow has nondecreasing grade, boundaries are finite, and limit stages use mapping-set colimits. I tested the edge cases `A=∅`, a one-object category with a loop, equal source and target grades, and a grading with no largest element. No statement error or hidden long sublemma remains; every proof step is under 2000 characters.
