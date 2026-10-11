Files written:

- `dag/nodes/sec-algebraic-groups-lie-algebras/lem-wf-mixed-commutator-tangent.json`: statement split into three proof steps; no new nodes.
- `citations.json`: verbatim citations for each proof-step dependency.

Attachments: none.

WANTED: none.

The imported item had no proof and omitted the existing subgroup-scheme definition needed for closure under multiplication and inversion. I added `def-sc-group-scheme-subgroup` to the statement and proof dependencies. The source's phrase that the inclusion eta mapping to epsilon delta gives the final tangent point was made explicit by coefficient extraction from the defining equations; this also avoids treating membership descent as a generic injectivity claim.

## Review by C1

I read the item source in Milne, *Algebraic Groups* (2017), Chapter 10, and checked the matching project source theorem `commutator_mem_mixedPoints` in `WeilConjectures/AlgebraicGeometry/GroupScheme/Lie.lean`; that theorem is still sorry-based, so this is a split rather than an attachment. I read `def-sc-dual-numbers` and `def-sc-group-scheme-subgroup`: the former states the square-zero dual-number relation used in the matrix expansion, and the latter states that points of a closed subgroup scheme over every algebra are a subgroup, which supplies base-change closure and inverses in step 1 and the defining-equation interpretation in step 3. Step 1 uses those statements for the two algebra maps into A and subgroup closure. Step 2 is an elementary expansion from epsilon-squared and delta-squared equal to zero. Step 3 uses the same dual-number basis and the closed-subscheme defining equations to compare the coefficient of epsilon delta with the coefficient of eta, then verifies the inverse explicitly. I checked the small cases X=0 or Y=0 (the commutator is the identity) and G=GL(V) (the calculation reduces to ordinary matrix multiplication). The required Mathlib searches were rerun for the item; they found only general DualNumber commutation lemmas and no exact algebraic-group commutator theorem.

## Second reading by C1

- Item statement: checked against Milne, *Algebraic Groups* (2017), Chapter 10 and `commutator_mem_mixedPoints` in `WeilConjectures/AlgebraicGeometry/GroupScheme/Lie.lean` (lines 610–614); hypotheses and conclusion agree, with the mixed algebra basis made explicit.
- Step 1: checked the base-change maps and subgroup closure against `def-sc-dual-numbers` and `def-sc-group-scheme-subgroup`; the inverse factors are `1−εX` and `1−δY` by square-zero.
- Step 2: checked multiplication term by term using `ε²=δ²=0`; it is elementary.
- Step 3: checked coefficient descent in the basis `1, ε, δ, εδ`; the defining equations have the same coefficients after replacing `εδ` by `η`, and the subgroup definition supplies the inverse.
- New nodes: none; existing definition nodes were searched by id and keywords in `dag/nodes`.
- Small cases: `X=0` or `Y=0`, `G=GL(V)`, and zero-dimensional `V`.
- Mathlib searches: recorded `leanfinder`, `loogle`, and source-grep queries were rerun through `msearch.py`; no exact theorem was found.

Changes made: added `[def-sc-group-scheme-subgroup]` and the mixed-ring basis to the statement, and corrected `created.item` metadata to this item.
