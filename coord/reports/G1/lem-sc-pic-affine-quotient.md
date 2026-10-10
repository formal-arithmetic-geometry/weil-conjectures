Files written:
- `dag/nodes/sec-curve-estimates/lem-sc-pic-affine-quotient.json`: statement split, no new nodes, no Mathlib leaf.
- `citations.json`: verbatim quotations for all cited steps.

Attachments:
- None. `AlgebraicGeometry.IsConnectedCurve.exists_addEquiv_pic_quotient` still has `sorry` in `WeilConjectures/AlgebraicGeometry/Curve/Affine.lean:247-255`.

WANTED:
- None.

What was wrong or incomplete:
- The imported item had no proof and was unsplit even though its blueprint proof paragraph gives the quotient route. I supplied the missing argument and kept the universal statement (fixed compactification and arbitrary boundary point) unchanged.
- No duplicate node states the restriction quotient, so I used the existing divisor-class and proper-decomposition statements directly rather than creating a restatement node.

What I could not finish:
- No Lean proof was written at stage 1; the source theorem remains sorry-backed and is therefore not an attachment.

## Review by G1
I read the item source and Lean docstring in `WeilConjectures/AlgebraicGeometry/Curve/Affine.lean`, including the displayed restriction, splitting, and Jacobian paragraphs. Step 1 was checked against the exact statements of `lem-sc-proper-affine-finite` and `def-sc-curves`: an empty boundary would make the connected one-dimensional curve both proper and affine, hence finite and zero-dimensional. Step 2 was checked against `lem-sc-divisor-class-curve`; its isomorphism from divisor classes to Picard classes supplies the divisor restriction argument, and the kernel is explicitly the divisors supported on the deleted finite set. Step 3 was checked against `lem-sc-pic-proper-decomposition`; subtracting the degree-one boundary point gives precisely the differences `[P]-[P0]` in the degree-zero factor. Step 4 was checked against `def-sc-jacobian` and `thm-sc-jacobian-representability`, whose statements identify the degree-zero Picard group with the Jacobian's `k`-points. I ran the required LeanFinder, Loogle, grep, and LeanSearch queries; they found no Mathlib statement of this geometric quotient (LeanSearch was unavailable). I also checked the small boundary case conceptually: one boundary point gives the zero subgroup and recovers `Pic(C) = Pic^0(C-bar)`.

## Second reading by G1

- Step 1 checked against `lem-sc-proper-affine-finite`, `def-sc-curves`, and `lem-sc-compactification`; the empty-boundary contradiction has all hypotheses and is correct.
- Step 2 checked against `lem-sc-divisor-class-curve` and divisor restriction; the argument now explicitly gives extension by zero, the boundary kernel, and principal-divisor compatibility, and is elementary.
- Step 3 checked against `lem-sc-pic-proper-decomposition`; the `(1,0)` and `(1,[P]-[P0])` generator calculation explicitly proves the quotient identification and is elementary.
- Step 4 checked against `def-sc-jacobian` and `thm-sc-jacobian-representability`; transport along the canonical group isomorphism gives exactly the stated subgroup and quotient.
- The item statement was checked against the blueprint quotient paragraph and the Lean docstring, including arbitrary compactification and `P0`; it agrees hypothesis by hypothesis.
- No new nodes are present; the existing nodes were searched in `dag/nodes`, and no Mathlib declaration states this geometric quotient.
- Small cases checked: an empty boundary contradicts dimension one; a one-point boundary gives `Lambda = 0` and `Pic(C) = Pic^0(C-bar)`; the construction is vacuous for no `n` parameter.

Changes: rewrote steps 2 and 3 to include the previously implicit divisor-kernel and degree-splitting calculations, marking only those short derivations elementary; no statements or nodes were added or weakened.
