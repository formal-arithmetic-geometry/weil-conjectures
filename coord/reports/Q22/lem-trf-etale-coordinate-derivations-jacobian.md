Files written:
- `dag/nodes/sec-trace-formula/lem-trf-etale-coordinate-derivations-jacobian.json`: existing item split into six proof steps; no new nodes.
- `citations.json`: 12 verbatim citation records for the item proof steps.

Attachments: none.

WANTED: none.

The item statement was retained verbatim. The old imported Mathlib-search records were retained, and the interrupted-turn searches completed in `searches.jsonl`; they found only general polynomial derivations, formal-etale differential base change, and standard-etale presentations. No existing declaration states the whole item, so this is a split rather than an attachment. I created no new node: every non-elementary input is already represented by an existing DAG node.

## Review by Q22

I read the item and its unit/chapter records, the latest blueprint text for `sk-i-curve-zero`, and the source passages for Stacks Tags 0H93, 00RX, 00RO, 02GJ, 01HV, and 07PE. I also inspected each cited DAG node. Step 1 uses the affine-space definition, the existing restriction and affine étale criterion, the formally étale Kähler differential comparison, and the polynomial-ring differential basis; these statements give exactly the affine ring map, the vanishing hypotheses, and the basis after scalar extension. Step 2 uses only the universal property of Kähler differentials, and explicitly constructs the evaluation bijection and the normalized derivations. Step 3 checks the commutator by expanding Leibniz twice; its only external input is the universal derivation statement used to conclude that a derivation vanishing on all coordinates is zero. Step 4 uses the same universal property for restriction and the existing affine-stalk localization and unique localization extension formulas from 07PE; I checked that the source and target rings and the prime localization match the affine-open hypotheses. Step 5 uses the formal partial-derivative definition and the universal derivation statement; both maps into the power-series ring have the same coordinate values, and the quotient-rule calculation is written out for germs. Step 6 checks the empty-coordinate case and the conditional nature of the formal-series assertion when an algebra map exists.

I checked edge cases $n=0$, empty affine opens, arbitrary characteristic, arbitrary field extension, zero-length iterated derivatives, and localization denominators sent to units. The commutator cancellation and the fraction quotient-rule calculation were written explicitly rather than hidden behind “standard” language. I verified every citation quote in `citations.json` is copied verbatim from the corresponding node statement. No source error or duplicate node was found; the only generic off-unit tool is the existing localization-extension node, declared in `split_report.tool_uses`.
