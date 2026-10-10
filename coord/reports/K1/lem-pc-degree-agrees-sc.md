1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-degree-agrees-sc.json`: statement split into two direct definitional steps; no new nodes.
- `citations.json`: verbatim statement excerpts for every cited node at every step.

2. Attachments:

None. The slopmaster2 declaration `AlgebraicGeometry.Scheme.IdealSheafData.IsInvertible.degree_dual_toModules_eq_one` proves only the rational-point special case in IdealSheafData language, not the full target statement, so I did not attach it as an exact declaration for the item. Its three transitive open declarations are not used by the definition-level route.

3. WANTED:

None.

4. What was wrong in the imported node:

The imported proof reconstructed additivity of divisors and an exact sequence already handled by the Riemann–Roch node. The corrected proof uses `lem-sc-riemann-roch` for the substantive equality between Euler characteristic and divisor degree, `def-sc-pic0` for `deg[O(D)] = deg D`, and `lem-pc-divisor-line-bundle-agrees-sc` for the canonical isomorphism of the two line-bundle constructions. The target's algebraically-closed qualification is retained because `def-sc-pic0` requires it.

5. What I could not finish:

Nothing. I checked edge cases `D=0` (both degrees are zero), a single rational point (degree one), and sums of effective point divisors against Riemann–Roch. The source node and all cited DAG statements were read. The imported Lean audit remains marked `rests_on_sorry`.

## Review by K1

I read the item node, its unit `sk-prop-picard-pic-split`, the source text recorded at blueprint order 812, and the statement of Riemann–Roch at `lem-sc-riemann-roch` (Stacks Tag 0BS6). For step 1, `lem-sc-riemann-roch` explicitly gives `chi(L)=deg_SC(L)+1-g` and `chi(O)=1-g`; `def-sc-pic0` explicitly says `deg[O(D)] = deg D`; `lem-pc-divisor-line-bundle-agrees-sc` explicitly says the divisor-theoretic and invertible-module constructions of `O_C(D)` are canonically isomorphic; and `def-pc-degree-line-bundle` defines the PC degree as `chi(L)-chi(O)`. Subtraction is elementary. Step 2 uses the same canonical-isomorphism statement and the explicit `def-sc-pic0` clause that a rational point has degree 1.

I verified the hypotheses at the point where they are used: the algebraically closed smooth connected proper-curve qualification is stated before invoking `def-sc-pic0`; effectiveness is part of the item statement and is the hypothesis of `def-pc-degree-line-bundle`; and the canonical-isomorphism node assumes a smooth connected curve and an effective Cartier divisor. I searched the DAG for the statement, for the relevant definitions, and for the canonical-isomorphism result before deciding that no new node was required. I checked the zero divisor and rational-point cases explicitly. The correction was to remove the imported Euler-characteristic reconstruction and replace it with the two cited definitional steps; no source statement was weakened.

The canonical-isomorphism lemma and Riemann–Roch are declared as tool uses because they belong to unit `sk-thm-picard-rr`, while this item belongs to `sk-prop-picard-pic-split`. The first identifies the compared bundles; the second supplies the substantive degree comparison. A prior dry run passed mechanically with a weaker proof, but I caught its invalid identification of two independent degree maps before pushing and added the Riemann–Roch step.
