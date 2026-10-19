1. Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-adic-scalar-extension-tor-bound.json` — statement, split proof, no new nodes; existing Mathlib searches retained and refreshed with msearch.
- `citations.json` — verbatim statement excerpts for every cited node and proof step.

2. Attachments: none.

3. WANTED: none.

4. The imported item had an empty proof. I checked the current main-20261015 scalar-extension route and found that all required ingredients already exist in the DAG, so I created no duplicate node. The proof now identifies cofinal reductions using the finite-free completed comparison, tests each arbitrary intermediate F-level against degree-zero modules using the Tor-amplitude definition and derived tensor balancing, and reconstructs the normalized tower via the effectivity node. The statement and hypotheses were not changed. The existing broader node `lem-coef-integral-finite-extension` is recorded as a same-form blueprint reference, but the proof below does not assume its conclusion.

5. Nothing remains unfinished.

## Review by NI

I read the item source in the master purity-transport unit and the corresponding main-20261015 scalar-extension proof. For Step 1 I checked that `lem-weil-finite-free-completed-scalar-comparison` really supplies finite freeness and the completed-to-derived-tensor identification, while `lem-pur-derived-change-of-rings` and `def-weil-integral-derived-reduction` supply the K-flat derived reduction calculation. For Step 2 I checked the exact definition of Tor amplitude in `def-weil-proetale-tor-amplitude` and the finite-free coefficient statement in `lem-coef-finite-free-extension`; restriction of scalars turns every degree-zero F-level test module into an E-level test, so the assumed [a,b] vanishing applies. I explicitly checked the edge case m not divisible by the ramification index and verified that no flatness of the quotient map is used. For Step 3 I read `lem-coef-normalized-dvr-effectivity`, `lem-weil-integral-scalar-extension-constructible`, and `def-weil-derived-complete-integral-detailed`; together they say the compatible levelwise system reconstructs the completed scalar extension, is derived complete, and has the required bounded constructible uniform interval. I checked every citation quote against the node text and recorded all proof dependencies. No statement correction or new node was necessary.
