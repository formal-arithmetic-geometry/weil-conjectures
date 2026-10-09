# Stage 1 report: `lemma-weil-pbc-direct-image-filtered-colimit`

## Worker report

Files written:

- `dag/nodes/sec-proper-base-change/lemma-weil-pbc-direct-image-filtered-colimit.json`: existing statement node, now `status: split`; no new nodes.
- `coord/reports/C1/lemma-weil-pbc-direct-image-filtered-colimit.md`: this report.

The imported detailed proof was expanded into four steps following Stacks Project Tag 09Z1 (the relative-colimit lemma): higher direct images are sheafified cohomology presheaves; the cohomology-colimit comparison is applied on the affine etale basis and finite fibre products; inverse image and sheaf colimits produce the sheaf-level comparison; and qcqs permanence repeats the argument after arbitrary base change. The source cohomology input is Tag 03Q5. Existing generic results from neighboring units are recorded as `tool_uses`; no reusable proof argument was hidden in a private node.

The node records LeanSearch, Loogle, and Mathlib-source grep searches. Mathlib has generic sheaf cohomology-presheaf and exact-colimit infrastructure but no higher direct-image filtered-colimit theorem, so no Mathlib leaf or Lean attachment applies. No Lean was written or compiled.

Attachments: none.

WANTED: none; the Stacks source is identified in the literature record and was read from the fetched checkout.

No statement or blueprint error was found. The statement remains the imported detailed statement, including arbitrary base change.

## Review by C1

I independently checked the node against the `sk-thm-iff` unit and Stacks 09Z1/03Q5. The four steps cover the full argument and explicitly preserve the canonical comparison maps: the first uses the reviewed higher-direct-image description, the second applies the filtered cohomology theorem to qcqs fibre products, the third accounts for inverse-image and sheafified colimits, and the fourth handles arbitrary base change through reviewed qcqs permanence. `proof_deps` is exactly the union of the step uses. The cross-unit cohomology and inverse-image results are generic black-box tools and are listed in `tool_uses`, so the route checker accepts them. No new reusable lemma was created; all cited ids exist and are either reviewed or existing route nodes.

Validation: `python3 tools/review_split.py lemma-weil-pbc-direct-image-filtered-colimit` passes; `python3 tools/check_dag.py --cycles` reports 0 cycles and 0 structural errors (with six pre-existing unrelated reachability warnings). No Lean compilation was run, per the Stage 1 contract.
