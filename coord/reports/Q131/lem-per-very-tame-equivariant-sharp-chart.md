# Worker report

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-very-tame-equivariant-sharp-chart.json`: item, split with four proof steps.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-tame-unit-extension-character.json`: new statement node, unsplit, no Mathlib match.
- `citations.json`: verbatim statement quotes for every proof-step citation.

Attachments: none.

WANTED: none.

The item follows Illusie–Laszlo–Orgogozo, Exposé VI, Proposition 3.5(a) and proof 3.7(a), pp. 74–75. I checked the imported hypotheses clause by clause: the characteristic monoid is the sharp quotient of the fs chart at the geometric point, only the stabilizer order is required to be invertible in the residue field, and no log-regularity or stratum-triviality hypothesis is added. The source's cocycle argument is isolated as `lem-per-tame-unit-extension-character`; it is a strictly smaller algebraic assertion about an equivariant extension of a free lattice by local units, and its Mathlib searches found no match.

## Not duplicates

`lem-per-tame-unit-extension-character` vs `lem-trf-log-regular-sharp-chart`: the new node concerns finite-group equivariant splittings of a unit extension and characters; the existing node concerns nonequivariant sharp chart existence under log regularity, with no group action or cocycle conclusion.

## Review by Q131

I read the complete item source in `literature/illusie-laszlo-orgogozo-travaux-de-gabber_arXiv-1207.3648.pdf`, Exposé VI 3.4–3.7(a), and the statements of every cited DAG node. Step 1 uses the fs-log definition for the stalk pushout and `lem-trf-fs-face-sharpening` for finite saturated sharpness and finite free group completion; the exact sequence is then the elementary group-completion sequence of the quotient by units. Step 2 uses the new unit-extension statement exactly for the character-valued equivariant section, with the positive cone preserved by its hypotheses. Step 3 uses `lem-trf-fine-log-stalk-chart-spreading` for the pointed affine etale chart. I checked the finite shrinking argument explicitly: stalk equalities for finitely many generators and group elements hold on a common neighborhood, and intersecting its finitely many translates gives an H-stable neighborhood. Step 4 uses the new node for fixed roots and `lem-sbc-strict-local-roots-of-unity` for cyclicity and the distinct-root unit property; this gives the diagonal monoid-ring description.

I tested the edge cases H trivial, Q=0, and n=1: the character is trivial, the chart reduces to the ordinary sharp chart, and the localization at n is vacuous. I also checked that the statement does not claim log regularity, quotient existence, or trivial action on the stratum. I corrected the earlier draft by preserving the positive cone in the new algebraic node, removing an unsupported citation to the etale-definition node, and adding the fixed-roots citation and quote to `citations.json`.
