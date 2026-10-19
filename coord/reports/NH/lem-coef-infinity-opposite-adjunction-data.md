1. Files written:

- `lem-coef-infinity-opposite-adjunction-data.json` — statement item, split with five proof steps and no new nodes; Mathlib searches found no exact coherent infinity-categorical match.
- `citations.json` — verbatim statement quotations for every cited node at every step.

2. Attachments: none.

3. WANTED: the Kerodon pages 02EK and 003L are online sources cited by the imported node and are not archived in `literature/`; no local source was available for those exact infinity-categorical constructions.

4. The imported node had no proof and stale ownership metadata from an earlier group. I retained its statement, dependencies, blueprint ancestry and recorded searches, changed ownership to NH, and supplied the proof. I checked the three dependency statements directly. The proof follows the literal simplex reversal: it first constructs the opposite functors, then reverses unit/counit edges, reverses both specified triangle 2-simplices, identifies the two comma pullbacks and transports initial/terminal objects, and finally checks parameter restrictions and involutivity. No non-elementary fact beyond the existing mapping-reversal statement is introduced, so no new node is warranted.

## Review by NH

I read `def-cbc-enhanced-diagrams-cones` in full for the internal functor simplicial sets and the explicit coherent comma pullback, `def-coef-coherent-adjunction-data` for the exact unit/counit orientations, triangle long edges, and initial/terminal universal-arrow clauses, and `lem-coef-infinity-op-mapping-reversal` for natural mapping comparisons, composition/identity reversal, triangle witnesses, and parameter compatibility. Step 1 uses the internal-functor definition and the reversal identities. Step 2 verifies the endpoint directions of `eta^op` and `epsilon^op` against the adjunction definition. Step 3 checks that the original right (respectively left) triangle reverses to the new left (respectively right) triangle with degenerate long edge. Step 4 unfolds the comma pullbacks and verifies that an opposite turns initial into terminal and terminal into initial, with the displayed objects and arrows. Step 5 checks faces, degeneracies, restriction of parameter simplices, and reversal twice. I tested the directions on the identity adjunction, a one-arrow poset, and empty quasicategories; all give the stated reversed data. Every step's cited statements were quoted verbatim in `citations.json`, and every proof dependency is present in the item.
