## Stage 1 Delivery Report

Item: `lem-weil-pbc-jacobi-zariski-quotient-smooth`

## Files Written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-jacobi-zariski-quotient-smooth.json`: repaired the returned split on the current `sheaf-dag` tip; its four proof steps cite nodes only.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-jacobi-zariski-homology-sequence.json`: statement-only Tag 00S2 node.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-jacobi-zariski-surjection-h1.json`: statement-only Tag 07BP node.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-jacobi-zariski-surjection-differentials.json`: statement-only Mathlib leaf for Tag 07BP's vanishing differential module.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-jacobi-zariski-left-term-vanishing.json`: statement-only Tag 00S2 Tor specialization.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-jacobi-zariski-differential-maps.json`: statement-only Tag 00RU map node.

## Repair

The returned reasons required every unsplit support node to have `proof: []`, exact Tags 00S2/07BP/00RU in its self-contained TeX statement, and citations for the existing Kähler-differential and naive-cotangent-complex definitions. Those citations now appear in `stmt_deps` and in each statement; the homology-sequence node also explains the canonical polynomial-ring presentations, and the left-term node cites the homology-sequence node for the Tor criterion. The item proof steps now cite only these nodes and the existing smooth/Kähler definitions. The Mathlib leaf records `KaehlerDifferential.subsingleton_of_surjective` at `Mathlib/RingTheory/Kaehler/Basic.lean:277` and retains LeanSearch, Loogle, and grep records.

## Validation

- `python3 tools/preflight_delivery.py F1 lem-weil-pbc-jacobi-zariski-quotient-smooth` passes on the current base.
- `python3 tools/review_split.py lem-weil-pbc-jacobi-zariski-quotient-smooth` passes.
- `python3 tools/check_dag.py --cycles` reports zero cycles and zero self-loops; any reachability notices are pre-existing and unrelated.
- No Lean was written or compiled.

## Review by F1

I reviewed the repair against the returned points and the cited sources. The parent now derives the short exact sequence by applying the public Tag 00S2 sequence node, the Tag 07BP quotient-H1 and vanishing-differential nodes, the Tor/projectivity specialization, and the Tag 00RU explicit-map node. Each support statement introduces its own rings, ideals, modules, quotient, canonical presentation, or Tor condition and cites the relevant existing definition node. The exact tags are in the statements rather than hidden only in source metadata. All four unsplit nodes are statement-only, while the differential-vanishing node is a Mathlib leaf with a verified source line. No duplicate node, statement weakening, route departure, or cycle was introduced.
