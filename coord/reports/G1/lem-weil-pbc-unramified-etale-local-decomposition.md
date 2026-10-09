# Stage 1 report: `lem-weil-pbc-unramified-etale-local-decomposition`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-unramified-etale-local-decomposition.json`
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-unramified-fibre-point-isolated.json`
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-local-finite-multiple-points.json`
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-unramified-one-point-closed.json`
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-unramified-base-change-open.json`

## Corrections

The returned split is repaired against the source text in `literature/stacks-project`.
The three child statements now introduce their schemes, scheme-theoretic fibres,
locally-finite-type, etale, finite, unramified, closed-immersion, residue-field,
and purely-inseparable notions explicitly through DAG citations. Their source
places identify the exact Stacks tags: 02LM for simultaneous etale localization
of isolated points, 04DG for a finite unramified one-point fibre, and 02GF/02G8
(with 02V5 for local quasi-finiteness) for isolation in an unramified fibre.
The 04DG statement uses the singleton of the underlying topological fibre, as
in Stacks, and separately identifies the corresponding scheme-theoretic fibre
point.

The new node `lem-weil-pbc-unramified-base-change-open` records the two stability
facts used by the parent proof: arbitrary base change (Tag 02GA) and restriction
to open source and target subschemes (Tag 02G6). Step 1 now forms the finite
union of the chosen unramified neighbourhoods before applying the 02GF/02G8 and
02LM nodes, and cites this stability node for the restriction and base change.
Step 2 explicitly replaces each piece by its actual base change
`V_{i,j}\times_U U'` after every shrinking of the etale neighbourhood; Tag 01JR
(`lem-weil-pbc-open-fibre-product`) identifies that base change with the required
open subscheme of the final fibre product. The parent statement and source cite
Tag 04HI.

No Lean declarations or target statements were changed. All new nodes remain
`unsplit` and record three-way Mathlib searches with no exact scheme-level match.

## Review by G1

I checked the parent statement against Etale Morphisms Tag 04HI and its proof
against the displayed proof at lines 1722-1749, including the closed-image
shrinking argument using Morphisms Tag 01W6. I checked each child statement
against its cited source: More on Morphisms Tag 02LM, Etale Morphisms Tag 04DG,
and Morphisms Tags 02GF, 02G8, and 02V5. The stability node is exactly the
base-change clause of Tag 02GA together with the restriction clause at the end
of Tag 02G6. The parent’s proof dependencies equal the union of its step uses,
and every new node has a complete self-contained statement, source, creation
metadata, and Mathlib search verdict. The repair stays within unit `sk-thm-p1`
and introduces no duplicate node or route departure.

Validation: `python3 tools/review_split.py lem-weil-pbc-unramified-etale-local-decomposition`
passes; `python3 tools/check_dag.py --cycles` reports no cycles (with the
repository’s pre-existing unrelated reachability warnings).
