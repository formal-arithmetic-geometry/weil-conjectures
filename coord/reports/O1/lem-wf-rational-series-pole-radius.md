## Files written

- `lem-wf-rational-series-pole-radius.json`: split the existing statement into one elementary Cauchy-product contradiction step; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim quotations for all five statements used by step 1.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the blueprint tag, the item terminology, and likely radius/pole declarations. No sorry-free project declaration states this item. The nearby `AlgebraicGeometry.WeilSheaf.l2Weight_eq_of_isReal` declaration has a sorry proof and is not an attachment.

## WANTED:

None.

## What was wrong or corrected

The imported statement is well-typed and agrees with the current main-20261015 blueprint and its master predecessor. I retained all hypotheses and the conclusion, including the (unused but source-prescribed) condition $Q(0)\\ne0$. The imported node had no proof; its parent proof's phrase “the Taylor radius is at most $R$” hides the direct analytic evaluation argument. I wrote that argument in the item itself. No new dependency node is needed: finite Cauchy-product expansion, absolute convergence at a point strictly inside the radius, and the final contradiction are a short consequence of the cited power-series and radius definitions. No duplicate node or blueprint statement was found.

## What I could not finish

Nothing remains for this stage-1 split. No Lean code was written or compiled, as required.

## Review by N1

I read the item node, the `sec-deligne-laumon-a1` chapter and `sk-l-dl-a1-energy` unit records, and the current main-20261015 proof at its final Taylor-radius paragraph. The item statement matches that source clause and the older master proof. I also read every statement quoted in `citations.json`: `d-real-series` supplies absolute convergence for every modulus strictly below the radius; `def-weil-formal-power-series` supplies finite coefficient convolution; `def-weil-polynomial-as-power-series` identifies the polynomial with its formal series and preserves coefficients; `def-weil-polynomial-ring` supplies finite support of $Q$; and `def-weil-complex-absolute-value` supplies the modulus used in the radius comparison. Step 1 uses exactly these statements: under the negation $R(f)>|a|$, absolute convergence permits evaluation of $f$ at $a$; finite support permits rearranging the Cauchy product; the formal equality then evaluates to $P(a)=Q(a)f(a)=0$, contradicting the stated nonvanishing of $P(a)$. The condition $Q(0)\\ne0$ is retained but not needed for this implication, as the source statement gives it.

I checked edge cases $a=0$, a polynomial $f$, the sharp example $f=(1-T)^{-1}$ with $Q=1-T$, and a cancelled root with $P=Q$ (which is correctly excluded by $P(a)\\ne0$). I also checked that $R(f)=0$ and $R(f)=+\\infty$ cause no gap in the contradiction argument. All proof text is below the 2000-character long-step review threshold. The existing Mathlib searches were read and show no exact or one-line generalization of this polynomial-times-series obstruction, so no Mathlib attachment is claimed.
