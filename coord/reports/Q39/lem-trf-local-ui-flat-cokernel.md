# Worker report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-local-ui-flat-cokernel.json` — item, split; no new nodes and no Mathlib leaf.
- `citations.json` — one verbatim citation for each of the three proof steps.
- `report.md` — this report.

Attachments: none.

WANTED: none.

The item is sourced from Stacks Project, Algebra Tag 058P, `lemma-ui-flat-domain`. I read the full statement and proof in `literature/stacks-project/algebra.tex`. The imported statement agrees with Tag 058P: a universally exact short exact sequence of R-modules with flat middle term has flat first and third terms; the item asks only for the third term. The existing dependency `def-weil-pbc-flat-ring-map` is the project’s definition of flatness as preservation of injections after tensoring, and it is the only non-elementary DAG fact needed.

## Review by Q39

I checked the item source and the cited dependency statement directly. Step 1 uses the item’s universal exactness hypothesis to obtain three exact tensor rows and uses the dependency’s flatness criterion for the injectivity of the middle vertical map. Step 2 uses the same criterion and the exact top row to prove injectivity on the left tensor map, hence flatness of M₁. Step 3 uses the exact left and middle columns, the surjections in the tensor rows, and an explicit diagram chase to prove injectivity of M₃⊗N→M₃⊗N′ for every injection N→N′; the dependency then identifies this with flatness of M₃. Every citation quote is copied verbatim from `def-weil-pbc-flat-ring-map`.

I searched the whole DAG and blueprint for Tag 058P, `lemma-ui-flat-domain`, and the phrase “flat cokernel”; no existing node states this lemma. The Mathlib searches were run with `msearch.py` and recorded in `searches.jsonl`: LeanFinder returned only general tensor exactness/flatness declarations, Loogle returned no match, and grep found general `Module.Flat` tensor lemmas but no universally-exact cokernel theorem. The statement was tested on split sequences (including zero modules) and on the non-flat torsion example from the source: the conclusion holds when the middle term is flat and fails when that hypothesis is removed. No statement correction, duplicate, source error, or route departure was found.
