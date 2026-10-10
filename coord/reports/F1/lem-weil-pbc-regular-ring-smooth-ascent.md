# Stage 1 report: `lem-weil-pbc-regular-ring-smooth-ascent`

## Changes

Split the target node according to Stacks Project Algebra Lemma 07NF. The item now has five proof steps: Noetherianity of the target from finite presentation, flatness of a smooth map, regularity of all smooth residue-field fibres, ascent of each Serre property `(R_k)` by Lemma 033A, and the final regular-ring criterion. No Lean files were changed or compiled.

Added two public Stage 1 support nodes, both statement-only and `unsplit`:

- `lem-weil-pbc-smooth-fibre-regular-local` records smooth base change to each residue field and the regular-local conclusion of the 00TT field criterion. It cites the existing 00TT dimension node rather than duplicating that node.
- `lem-weil-pbc-regularity-rk-goes-up` records the 033A theorem for property `(R_k)` under a flat map with Noetherian source and target and `(R_k)` fibres.

Both nodes have exact `created.item` metadata, self-contained TeX statements, Stacks source locations, and three Mathlib search kinds. Their proof arrays are empty as required for newly created unsplit nodes.

## Source and dependency audit

The 07NF proof in `literature/stacks-project/algebra.tex` applies 033A for every `k`; 033A requires Noetherianity, flatness, `(R_k)` on the source, and `(R_k)` on each fibre. Smoothness supplies finite presentation and flatness, finite presentation over the Noetherian regular source supplies Noetherianity of `S`, and 00TT supplies regular local rings on smooth finite-type fibres. The final “all `(R_k)`” conclusion is exactly the 00OD regular-ring condition. Existing nodes used are `def-weil-pbc-smooth-ring-map`, `def-weil-regular-scheme`, `lem-weil-pbc-finite-type-algebra-noetherian`, `lem-weil-pbc-smooth-ring-map-flat`, and the existing 00TT dimension node.

## Review by F1

I checked the item against the downloaded Stacks Algebra source at tags 07NF, 033A, 00TT, 00TA, and 00FN. The proof follows the source’s `(R_k)` route: it establishes the Noetherian and flat hypotheses, names the fibre regularity as a reusable node, applies the named 033A ascent result for each `k`, and closes with the definition of a regular ring. The new fibre node cites the already present 00TT node, so the 00TT tag is not introduced as an uncited duplicate. The new 033A node is a separate public DAG item with no private proof text. All proof dependencies are existing or newly added DAG IDs, and no statement carries proof steps. The delivery is limited to this item, its two new nodes, and this report.

## Verification

`tools/review_split.py lem-weil-pbc-regular-ring-smooth-ascent`, `tools/check_dag.py`, and `tools/preflight_delivery.py F1 lem-weil-pbc-regular-ring-smooth-ascent` were run after the one-commit rebase; their results are recorded in the delivery message.
