# Delivery report: lem-coef-relative-nerve-symmetric-family

Files written:

- `dag/nodes/sec-six-functors/lem-coef-relative-nerve-symmetric-family.json` — statement node, split into six proof steps; no new node and no Mathlib leaf.
- `citations.json` — verbatim quotations for every cited node in every step.

Attachments: none. No sorry-free declaration with this item statement was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `/home/ubuntu/weil-newtargets-master/WeilConjectures`; the source searches found only unrelated Cech nerves.

WANTED: an archival copy of Lurie HTT, Definition 3.2.5.2, Remark 3.2.5.7 and Proposition 3.2.5.21, and Higher Algebra Definition 2.3.2.10 and Proposition 2.3.2.11. The proof is recorded as agent-written because these sources are not archived under `literature/`.

## Review by Q07

I read the complete item node, the chapter `sec-six-functors`, the unit `sk-prop-sf-biduality-general`, the defining node `def-coef-symmetric-operadic-family`, the symmetric-operad convention `lem-coef-operadic-approximation-restriction`, and the full statement and proof of `lem-cbc-strict-presentation-transport-representation`. I also checked the related mapping-cylinder and operadic-family nodes for duplicates and route consistency. The source grep in both Lean trees found no declaration tagged with this item and no declaration of the relative-nerve symmetric-family theorem.

Step 1 uses only the explicit subset-indexed formula and fibre clause stated by `lem-cbc-strict-presentation-transport-representation`; I checked that reindexing subsets preserves the compatibility equations and that a constant parameter string gives exactly one fibre simplex. Step 2 takes exactly the relative-nerve theorem's cocartesian fibration, fibre, transport, and mapping-space clauses. I verified the direction of the mixed mapping equivalence (`a <= b`) and separately checked the reverse case against the absence of an edge in `Delta^m`; the pointed-map base is preserved because all transition maps are over `N(Fin_*)`.

Step 3 is the product-base horn check. I verified that each endpoint fibre is an inner fibration with inert cocartesian lifts by the symmetric-operad statement, that the transition maps commute strictly with the pointed-map projection, and that the subset equations glue the endpoint filler to the fixed initial block. I checked that the family inert-edge definition requires the simplex-coordinate edge to be an equivalence, so the claimed inert edges are exactly the within-vertex inert cocartesian lifts.

Step 4 transports the symmetric-operad Segal mapping square in `D(j)` across the Step 2 mapping equivalences. I checked both parameter inequalities, the homotopy/composition path, and the zero-arity product convention. Step 5 is a degreewise reindexing calculation for an order map `beta`; I checked that both the `N(Fin_*)` and `Delta^l` projections are preserved and that the cited strict-presentation node explicitly supplies pullback compatibility. Step 6 checks repeated vertices (identity transitions), `m=0`, empty fibres, and arity zero directly from the same formulas.

I tested edge cases before writing: `m=0`, a constant diagram with repeated vertices, a diagram with an empty fibre, arity `0`, and a reverse-parameter pair. None changes the statement. The item has no duplicate split: the nearby mapping-cylinder and operadic-collage nodes use different conclusions (cylinder contraction or nonsymmetric correspondence), while the strict-presentation node supplies the general relative-nerve construction used here. All citations in `citations.json` are copied verbatim from the cited node statements, and `proof_deps` is exactly the union of the step uses.

What was wrong or incomplete in the imported material: the item had an empty proof and an unarchived-source note, so I supplied the six-step natural-language proof and retained the WANTED note. No statement correction was necessary. No new unsplit node was created because the only non-elementary inputs are already stated by the existing strict relative-nerve and symmetric-operad nodes.

What remains unfinished: the cited HTT/HA sources still need archival acquisition for later review; this stage cannot download them and performs no Lean compilation by the human's instruction.

The strict relative-nerve theorem belongs to unit `sk-prop-sf-cbc`, so I declared it as a generic tool use in `split_report.tool_uses`; the symmetric-operad convention belongs to this item's own unit.
