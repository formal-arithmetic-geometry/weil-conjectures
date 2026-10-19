# Stage-1 report: lem-coef-tower-trace-rectification

Files written:

- `lem-coef-tower-trace-rectification.json`: existing statement, now split with five proof steps; no new node and hence no Mathlib leaf.
- `citations.json`: verbatim statement excerpts for every cited node in every step.
- `report.md`: this report.

Attachments: none. I searched the read-only slopmaster2 `WeilConjectures/` tree for the item id and its trace/tower terminology; no exact sorry-free project declaration was found.

WANTED: none.

No statement error was found. I retained the imported hypotheses and the distinction between finite coefficient objects, the completed base ring, and the strict tower. I searched the whole DAG for tower trace, counit compatibility, and ringed-sequence terms before deciding that no additional node was needed; the existing ringed-site and semilinear-section nodes already state the required framework. The recorded Mathlib searches were rerun for the item (`leanfinder` query `compatible counit maps from derived compact-support tower to quotient coefficient tower`, `loogle` query `DerivedCategory Tow evaluation counit compatible`, and `grep` query `counit.*tower|evaluation.*compact support` in `Algebra/Homology`); they found no matching Mathlib theorem, so the item remains a project statement rather than a Mathlib leaf.

## Review by Q101

I read the complete item node, its unit `sk-prop-sf-biduality-general`, the chapter record, and the source proof paragraph in `literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/prop-coef-integral-dualizing.md`. I also opened every cited node and checked its statement against the step that uses it.

Step 1 uses `lem-coef-finite-dualizing` for the finite pro-etale dualizing comparisons, their quotient cocycle/unit, and the counit identity; it uses `def-coef-normalized-dvr-tower` only for the tensor/restriction adjunct and strict transition meaning. The hypotheses are exactly the item’s fixed finite-field, quotient-ring, and separated finite-type setup, and the strict complex `Q_\bullet` is assumed by the item rather than constructed from an existence claim.

Step 2 uses `def-coef-ringed-sequence-site` for the actual quotient ringed site and exact evaluation, `lem-weil-pbc-diagram-site-realization` for the product-site/module equivalence, and `lem-coef-semilinear-derived-sections` for simultaneous derived open extension, proper direct image, point sections, and their evaluation compatibility. I checked that this step uses the cited nodes’ operation/evaluation clauses and does not assume that evaluation of a K-injective tower is K-injective.

Step 3 uses the finite dualizing node’s explicit finite pro-etale realization clause to replace the represented level `Q_n` by `\omega_n`; this gives exactly `ev_n B_\omega = \Gamma(s,F_n\omega_n)` with the stated restriction of scalars. No extra comparison or inverse-limit assertion is hidden here.

Step 4 uses the semilinear-section node’s statement that evaluation, composition, and adjunction transposes preserve the specified constructions and their coherence homotopies. Together with the counit-defined transition from step 1 and the finite dualizing comparison, this gives the stated compact-support transition followed by coefficient restriction for every `m >= n`; the quotient cocycle supplies the strict compatibility.

Step 5 uses the finite dualizing counit identity and the semilinear node’s preservation of counits under evaluation and composition. Applying these to compact support and point sections gives `epsilon_n t_{m,n} = q_{m,n} epsilon_m` in `D(R)`, so the finite counits form the required compatible family. I checked that every map is taken in the constant-base `R`-module category and that no test object `K` enters the construction.

I found no duplicate node to create, no source discrepancy, no SGA citation, and no hidden long sublemma beyond the cited framework statements. The proof dependency set equals the union of the step uses, and `citations.json` records a verbatim quote for every use.

What remains unfinished: nothing in the split; the required dry run and delivery are the next steps.
