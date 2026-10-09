# Stage 1 report: `lem-weil-pbc-quasi-coherent-algebra-affine-inclusion`

## Review by D

The item is split along Constructions Lemmas 01LN and 01LO. The statement is unchanged. The nested-affine tensor base-change assertion is isolated as the new unsplit node `lem-weil-pbc-quasi-coherent-affine-section-base-change`; the cartesian square and open-immersion conclusion use existing reviewed leaves `lem-weil-pbc-fibre-product-affine-spectra` and `lem-weil-pbc-open-preimage-fibre-product`; transitivity of the spectrum maps is elementary. The new node records LeanSearch, Loogle, and Mathlib grep searches, all finding no arbitrary nested-affine quasi-coherent tensor theorem.

Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-quasi-coherent-algebra-affine-inclusion.json` — existing item, now `status: split`.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-quasi-coherent-affine-section-base-change.json` — new statement node, `status: unsplit`, no Mathlib match.
- `coord/reports/D/lem-weil-pbc-quasi-coherent-algebra-affine-inclusion.md` — this report.

Attachments: none.

WANTED: none; `literature/stacks-project/constructions.tex` is present and cited.

No statement or blueprint error was found. The baseline `check_dag.py` also reports six pre-existing reachability warnings for unrelated nodes; it reports 0 cycles and 0 structural errors for this split. `review_split.py` passes with 1 new node.
