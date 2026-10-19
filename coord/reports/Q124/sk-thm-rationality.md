# Worker report: sk-thm-rationality

## Files written

- `dag/nodes/sec-zeta-weil/sk-thm-rationality.json`: repaired the prior split by replacing its 3112-character Step 4 with three cited steps; statement and hypotheses unchanged.
- `dag/nodes/sec-zeta-weil/lem-zl-constant-weil-datum.json`: new unsplit statement-only lemma; Mathlib searches found no match.
- `dag/nodes/sec-zeta-weil/lem-zl-constant-sheaf-lseries.json`: new unsplit statement-only lemma; Mathlib searches found no match.
- `citations.json`: 32 verbatim statement quotations, one for every cited node use in the repaired ten-step proof.
- `report.md`: this report.

## Attachments

No attachment. `AlgebraicGeometry.Scheme.zetaSeries_rational` in `WeilConjectures/Statement.lean:80–87` has the matching type but its body is `sorry`; the trace-datum corollary in `ZetaLinearAlgebra/Rationality.lean:104–109` has additional hypotheses and does not close this item.

## WANTED

None. The current blueprint, Stacks citations already recorded by the prior split, and Milne's lecture notes suffice. No SGA source is used.

## Source error and repair

The imported unit proof starts from a smooth-proper trace theorem although the current item is for every quasi-compact locally finite-type scheme. The existing split already reports this scope error and repairs it by a finite affine partition and compact supports; that route and the item statement are unchanged here. The human repair handoff identified only the 3112-character constant-sheaf Step 4 as too long and lemma-hiding. I kept its mathematical content, made the compatible constant Weil datum and the local-factor/L-series identification explicit as two statement-only nodes, and replaced the long step by three shorter applications.

## Review by Q124

I read the current item, its unit and chapter, the current blueprint section and proof, the prior Q33 report, the repair handoff in `coord/returns/Q124.md`, and every node cited by all ten proof steps. Steps 1–3 still use exactly the existing finite-type permanence, affine partition, point-count, exponential finite-sum and Euler-product statements; their hypotheses are checked for the finite field, the separated affine strata, and the empty partition. Steps 4–6 now expose the hidden argument: `lem-zl-constant-weil-datum` states the levelwise rank-one $\mathbf Z_\ell/\ell^n$ tower, identity Frobenius, reduction compatibility and rationalized $E_Y$ object, while `lem-zl-constant-sheaf-lseries` states the identity local determinant and coefficientwise zeta product. I checked that both new statements introduce their objects and cite their defining nodes, and that their Mathlib searches were actually run and recorded in each node's search log. Step 6 then applies clause (b) of `sk-thm-trace-transport` and the existing compact-cohomology finiteness statement to form the finite odd/even determinant products with constant term one. Steps 7–10 retain the prior finite multiplication, field-extension rank comparison, rationality criterion and integral Fatou normalization; each use is quoted verbatim in `citations.json`.

I checked the long-step rule: the largest repaired proof step is now 1434 characters. I checked C1/C4 by opening every cited node statement, and no quote relies on a node's proof. The new lemmas are strictly smaller than the item and do not restate its integral rationality conclusion. I checked for duplicate DAG or blueprint statements and found none. The only Mathlib candidates were generic Witt-vector, constant-sheaf and classical L-series declarations, so neither new node is a Mathlib leaf. Edge cases from the prior review remain valid: the empty scheme gives empty products equal to one, $\operatorname{Spec}\F_q$ gives $(A,B)=(1,1-T)$, nilpotent thickenings have the same field-valued points, and the affine line and doubled-origin line demonstrate why the compact-support partition route is needed. No dependency path returns to the item.

## Unfinished work

None. This is the requested stage-1 repair; no Lean file was written and no compiler or build tool was run.
