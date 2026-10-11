Files written:

- `dag/nodes/sec-curve-estimates/lem-sc-pic-affine-base-change-compatibility.json`: split item; no Mathlib match.
- `dag/nodes/sec-curve-estimates/lem-sc-pic-restriction-boundary.json`: statement-only unsplit node; no Mathlib match.
- `citations.json`: verbatim citations for every proof-step dependency.

Attachments: none.

WANTED: none.

The source item had no sorry-free declaration in `WeilConjectures/`; the source search found only unrelated Jacobian declarations. The imported item had no proof. I retained its statement and existing blueprint ancestry. The existing `lem-sc-pic-affine` node gives the quotient identification but does not state that the quotient map is the restriction map or identify its kernel, so I added `lem-sc-pic-restriction-boundary` rather than citing it for a fact it does not state. The existing `lem-sc-affine-unit-divisor-base-change` supplies the boundary-point and divisor pullback fact used in the final compatibility step.

## Review by K1

I read the item, the affine-extension blueprint proof in `thm-sc-constant-invariance`, and the statements of `lem-sc-base-change-curve`, `lem-sc-compactification`, `lem-sc-pic-affine`, `lem-sc-genus-invariant`, `lem-sc-affine-unit-divisor-base-change`, and `thm-sc-jacobian-representability`. Step 1 uses only the base-change stability and compactification statements, with the residue-field observation for a closed point over an algebraically closed field written out as an elementary argument. Step 2 uses the new restriction-kernel statement, the existing affine quotient statement, and the genus/Jacobian compatibility statement; these supply surjectivity, the boundary kernel, the quotient presentation, and the identification of the Jacobian map. Step 3 uses the existing boundary-divisor base-change statement to check the generators and the genus-invariant Jacobian compatibility to descend the map to quotients. I checked the hypotheses in each application: both fields are algebraically closed, the curves are smooth affine connected, and the chosen compactifications are smooth proper connected with finite boundary. I ran the required LeanFinder, Loogle, grep, and LeanSearch searches for the item and the new node; LeanSearch was unavailable and recorded as such. I tested the boundary claim on the basic cases of the affine line and a punctured proper curve: the boundary points remain single points and the generated subgroup maps as asserted.
## Second reading by K1

- Item statement and steps checked against the blueprint proof and all cited node statements.
- Corrected `created.item`, source metadata, and divisor line-bundle citation.
