# Stage 1 report: `lem-weil-pbc-henselization-pair-g-ring`

## Worker report

Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-henselization-pair-g-ring.json`: existing statement node, now `status: split` with five proof steps.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-henselization-noetherian-completion.json`: public helper node for Stacks 0AGV.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-henselization-finite-separable-fibres.json`: public helper node for Stacks 0AH1.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-geometric-regularity-separable-extension.json`: public helper node for Algebra 07QH.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-g-ring-maximal-ideal-criterion.json`: public helper node for the maximal-ideal G-ring criterion (07PT).
- `coord/reports/C1/lem-weil-pbc-henselization-pair-g-ring.md`: this report.

The imported statement is unchanged. The proof follows Stacks Project Lemma 0AH3 with exact Tags 0AGV, 0AGX, 0AH1, 07PT, and Algebra 07QH. It first obtains Noetherianity and the unchanged adic completion from 0AGV, checks the maximal-ideal and residue-field hypotheses and applies the existing 0AGX completion lemma, applies the generic 0AH1 filtered-colimit fibre theorem to the henselization, identifies the completed local fibre as a factor, transfers geometric regularity across the separable residue extension by 07QH, and applies the 07PT maximal-ideal criterion. Each reusable fact is a separate public DAG node or an existing imported node in `proof_deps`; none is private.

The target and each helper records LeanSearch, Loogle, and Mathlib-source grep searches dated 2026-10-10. Mathlib has no G-ring, henselization, formal-fibre, or geometrically-regular theorem matching these statements. No Lean was written or compiled.

Attachments: none.

WANTED: none; the cited Stacks source is available in the fetched literature checkout.

No statement, blueprint, or source-route error was found.

## Review by C1

I independently read the source proof around Lemma 0AH3 and checked each expanded step against the cited tags. Step 1 uses 0AGV for Noetherianity, flatness, and the unchanged adic completion. For a fixed maximal $\mathfrak m^h$, Step 2 checks $\mathfrak mA^h_{\mathfrak m^h}=\mathfrak m^hA^h_{\mathfrak m^h}$ and equality of residue fields from the quotient isomorphism in the pair-henselization node, so the existing 0AGX node applies. For a prime $\mathfrak q$ and a chosen $\mathfrak q^h$, Step 3 applies the exact generic 0AH1 statement to the filtered-etale presentation of $A^h$, rather than asserting finiteness only after localization. Step 4 names both completed fibre rings, uses the completion isomorphism to identify their finite product, takes the component indexed by $\mathfrak q^h$, and uses separability before invoking 07QH. Step 5 invokes 07PT only after Noetherianity and all maximal-local fibre conditions have been established.

`proof_deps` is exactly the union of the step uses. The four new reusable facts are public Stage 1 nodes in the same chapter and unit, with TeX statements, explicit object citations, exact source tags, search records, and `status: unsplit` because Mathlib has no matching leaves. The target reuses the existing public 0AGX node instead of recreating a local-completion helper. The target's statement dependencies remain only `def-weil-pbc-g-ring` and `lem-weil-pbc-pair-henselization`.

Validation: `python3 tools/review_split.py lem-weil-pbc-henselization-pair-g-ring` passes and reports four new nodes. `python3 tools/check_dag.py --cycles` reports 0 cycles and no dependency or unit-route errors; it retains only unrelated reachability warnings from the shared DAG. No Lean compilation was run, per the Stage 1 contract.
