1. Files written:

   - `dag/nodes/sec-curve-estimates/lem-sc-units-quotient-base-change.json` (statement, split proof, blueprint metadata, searches).
   - `dag/nodes/sec-curve-estimates/lem-sc-affine-unit-divisor-base-change.json` (new unsplit statement node; Mathlib no match).
   - `citations.json` (verbatim step citations).

2. Attachments: none. The declaration `AlgebraicGeometry.IsConnectedCurve.finite_units_quotient` in `AlgebraicGeometry/Curve/Affine.lean:121` is not an attachment because it states finiteness, not base-change invariance.

3. WANTED: none.

4. What was checked: the item source is the affine unit quotient paragraph of the blueprint theorem `thm-sc-constant-invariance`. The existing nodes `lem-sc-compactification` and `lem-sc-global-functions` were read in full and their statements supply, respectively, the compactification with finite boundary and the fact that global functions on a proper connected curve are exactly the base field. The new node isolates the non-elementary comparison that principal boundary divisors of units are unchanged after algebraically closed base change; its statement introduces both compactifications, boundaries, divisor groups, and unit groups. Step 1 checks the compactification and its base change. Step 2 uses exactly the new comparison node and the global-functions statement to identify the divisor-map kernels with constants. Step 3 uses the same comparison and global-functions statement; the remaining passage to n-th powers is the two-line algebraically closed-field argument. I searched the DAG and blueprint for duplicate divisor/base-change statements and ran LeanFinder, Loogle, grep, and LeanSearch for both the item and the new node; no Mathlib declaration states either result (LeanSearch was unavailable). Small cases checked: $C=\\mathbf A^1_k$ gives trivial quotient on both sides, and $n=1$ gives the zero quotient.

5. What could not be finished: the new principal-divisor comparison is intentionally statement-only for the next stage.

## Review by J1

I read the imported item and its blueprint source, checked the exact existing Lean theorem, and verified that it proves only finiteness. I read the cited compactification and global-functions nodes and matched each use in the three proof steps to their statements. I also checked that the new node is strictly narrower than the item, searched for duplicates before creating it, recorded all required Mathlib searches, and quoted only verbatim portions of cited statements in `citations.json`. The proof uses no unsupported hypothesis beyond algebraic closedness, smooth affine connectedness, and the chosen compactification; the boundary comparison is isolated as the sole unsplit child.

## Second reading by J1

- Item statement: checked against the affine unit-quotient paragraph of `thm-sc-constant-invariance`; the algebraically closed extension, smooth affine connected curve, and `n >= 1` hypotheses and the pullback isomorphism all agree.
- Step 1: checked `lem-sc-compactification`, `lem-sc-base-change-curve`, and `def-sc-field-extension`; base change stability and the boundary/divisor-group setup are now explicitly cited, with the non-elementary stability step marked accordingly.
- Step 2: checked the statement of `lem-sc-affine-unit-divisor-base-change` and `lem-sc-global-functions`; these give the subgroup identification and the constants kernel exactly as used.
- Step 3: checked the same two cited statements; the remaining n-th-root and quotient argument is a short algebraically closed-field calculation and is marked elementary.
- New node `lem-sc-affine-unit-divisor-base-change`: checked self-contained hypotheses and notation against the compactification and divisor definitions; tested on `A^1_k` and on an empty boundary, where both principal-divisor subgroups are zero. Its recorded searches were checked against `searches.jsonl`.
- Changed the new node's notation to TeX, removed unused divisor-class/Jacobian dependencies, and retained only definitions used by its statement.
- Added `lem-sc-base-change-curve` to step 1 and to `citations.json`, because preservation of smoothness, properness, and affineness under base change is not elementary from the field-extension definition.
