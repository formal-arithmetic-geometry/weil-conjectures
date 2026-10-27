# Delivery report: lem-per-completed-monomial-transverse-parameter

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-completed-monomial-transverse-parameter.json`: existing item completed as a five-step split proof; no new nodes.
- `citations.json`: verbatim citations for every proof-step dependency.

## Attachments

None. No sorry-free project declaration states this item, and no new node was created.

## WANTED

None. The ILO volume is present and was read at VI 1.6 and VIII 3.4.13.

## Not duplicates

No new nodes were created, so there are no new-node duplicate pairs.

## What was checked and corrected

The imported item statement is retained. I read the current blueprint ancestor `lem-per-artin-gabber-affine-curve` and the current unit `sk-p-dl-a1-perverse`, then read ILO Exposé VI 1.6 (printed p. 70) and Exposé VIII Lemma 3.4.13 (printed pp. 112–113). I also searched the whole DAG and blueprint for completion, monoid-series, transverse-parameter, and monomial-quotient statements. The existing coefficient-family completion lemma, positive grading and bounded-degree lemmas, finite monoid-ideal generation lemma, and PID-Noetherian lemma were checked statement-by-statement and cited where used. The six required Mathlib searches were rerun and recorded in the item.

Step 1 checks that the fine saturated sharp monoid has a finite-free group completion and a positive grading, forms the product monoid with the transverse variables, and applies the existing completion coefficient-family theorem over a field or Cohen ring. Step 2 groups coefficients into multivariate power series and proves that the completed monomial ideal is exactly the family support on `H`, using the finite ideal generators. Step 3 performs the source's lowest-monoid-degree argument: at a minimal surviving exponent, the coefficient of a product with nonzero free term is the product of two nonzero power series. I wrote out the domain argument by ordering exponent tuples by total degree and lexicographically. Step 4 specializes this to `t_1`. Step 5 checks the mixed-characteristic equation quotient directly: evaluation at `t_1=0` has kernel `t_1N`; the reduced equation has nonzero free coefficient, so it is regular by Step 3, and then Step 4 cancels the remaining `t_1`. I checked `n=0`, `H=empty`, `H=Q`, and `Q={0}` separately.

The item is a lower lemma imported for the parent associated-points proof. Its proof uses generic monoid/completion statements from the trace-formula unit as tool lemmas; these are listed in `split_report.tool_uses` with the reason each is needed. No statement was weakened, and no new node merely restates a clause of the item.

## Review by Q61

I checked every hypothesis against the item and cited definitions: `Q` is fine saturated and sharp, `H` is an arbitrary monoid ideal including the two extremes, the completion ideal has the stated field/Cohen maximal-ideal convention, and the Cohen equation is congruent to `p` modulo the monomial and variable ideal. The completion coefficient theorem applies because the product monoid is finitely generated, has a positive grading, and the coefficient ring is complete Noetherian local; a Cohen ring is a complete DVR and hence a Noetherian PID. For each proof step I opened each cited node and verified that its quoted sentence supplies exactly the claimed grading, bounded-degree finiteness, coefficient-family description, finite ideal generators, or Noetherianity. The quotient-support calculation and the reduction modulo `t_1` are written inline from those statements and the definitions. I tested the argument in the edge cases `Q={0}`, `H=empty`, `H=Q`, `n=0`, and `n=1`; the Cohen argument also works when the reduced variable list is empty. The Mathlib hits were only ordinary univariate/multivariate power-series declarations, so the item remains a project statement rather than a Mathlib leaf.

## What could not be finished

Nothing; the required dry run remains to be executed.
