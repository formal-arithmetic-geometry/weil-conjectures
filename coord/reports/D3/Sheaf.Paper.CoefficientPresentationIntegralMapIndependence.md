## What changed

Proved `WeilConjectures.LocallyFiniteAdicCompactSupport.coefficientPresentation_integralMap_eq`
in `Sheaf.Paper.CoefficientPresentationIntegralMapIndependence`, preserving its full signature
and public import. Constants determine each finite comparison by `sheafify_hom_ext`.
The residue equations and `limit.hom_ext` determine the integral comparison and its inverse.
The two pointwise inclusion normalizations determine the remaining composite.
Updated the item's DAG proof, proof dependencies, and proof origin to match these steps.
No other existing module changed, and no new declaration, module, or node was added.

Read Bhatt--Scholze Lemma 6.8.2 and its proof, pp. 58-59, and Definition 6.8.1.
The formal proof uses only normalization fields of the actual coefficient presentations;
it does not use a new existence or uniqueness theorem. It covers empty test schemes as
well: all pointwise equalities there are vacuous and function extensionality applies.

Searches: LeanFinder found sheafification uniqueness, including `sheafify_hom_ext`;
Loogle found the exact `CategoryTheory.sheafify_hom_ext` declaration; grep found the limit
extensionality infrastructure. Read the matching Mathlib signature and the existing
completed-coefficient extensionality proof in `IntegralCompactSupportCoefficientData`.
All searches are recorded in `searches.jsonl`.

Validation: the complete item compiled cleanly through `lcompile.py` in 7.8 seconds.
The current server queue row is an ordinary proof item with one hole; no rework row or
item build-error record was present.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.LocallyFiniteAdicCompactSupport.coefficientPresentation_integralMap_eq`
(node `lem-sf-coefficient-presentation-integral-map-independence`).
Zero holes remain in the item; zero holes added; zero split-off statements.

## No longer needed

No imports removed and no entire modules pruned. The proof needs no additional imports.
Removed `def-pur-integral-compact-support-coefficient-data` from the item's `proof_deps`:
no compact-support comparison or coefficient-change theorem is needed for this uniqueness
argument. Its unchanged statement dependency and the existing public import chain remain.
The proof uses the actual completion definition and its limit projections through the
existing realization data; no separate existence or presentation-uniqueness lemma is used.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan says to compose the final maps into the native ring with finite
quotient projections. The relevant projections instead belong to the completed integral
ring: the proof first compares the two integral identification maps into that completion,
then combines equality of their inverses with the fixed pointwise inclusions. The updated
DAG makes this distinction explicit. No statement or definition repair was required.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CoefficientPresentationIntegralMapIndependence": "e5ae37e434a0bc130ee073478f55eae3fba3a456"}, "results": {}, "time": "2026-10-28T06:40:39+0800", "transitive": 0, "version": 1}
```

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
