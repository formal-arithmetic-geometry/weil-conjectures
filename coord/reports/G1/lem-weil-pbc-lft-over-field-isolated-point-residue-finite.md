# Worker report: `lem-weil-pbc-lft-over-field-isolated-point-residue-finite`

## Changed

- Split `lem-weil-pbc-lft-over-field-isolated-point-residue-finite` into four proof steps following Stacks Algebra 00PJ (1) => (6): affine chart and finite-type ring map, the finite-type isolated-prime ring argument, residue-field identifications and action compatibility, and transport of finite-dimensionality.
- Added `lem-weil-pbc-isolated-prime-finite-type-algebra-residue-finite` as the one remaining unsplit ring-level bridge. Its source is Algebra 00PJ, with the Jacobson/Nullstellensatz steps recorded in the source and node statement.
- Recorded three Mathlib search kinds for the new node. Existing Mathlib declarations provide only separate Jacobson, quasi-finite, and residue-field ingredients, so no exact match was claimed.

## Proof status

The field-case item is marked `split` with a `split_report`; the new ring-level node is intentionally `unsplit` and has no proof or proof dependencies yet. No Lean files were changed and no `sorry` was introduced.

## Sources and checks

The proof follows Stacks Algebra Lemma 00PJ (1) => (6), Morphisms Lemma 01T2, and Schemes Lemmas 01HH, 01HV, 01HY. The affine chart, finite-type criterion, scheme/prime residue-field identification, open-immersion residue-field isomorphism, and map compatibility are cited by existing DAG nodes.

## Review by G1

I checked that the parent proof uses only existing nodes plus the newly created ring-level bridge, that `proof_deps` is the union of the step uses, and that the bridge is a genuinely narrower statement rather than a duplicate. The singleton-open hypothesis is pulled back along the affine open immersion, and the final residue-field isomorphism is stated as compatible with the `k`-action, so the conclusion is the requested finite extension rather than only an abstract field isomorphism.
