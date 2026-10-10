# Delivery: lem-weil-pbc-dimension-at-point-local-ring-trdeg

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-dimension-at-point-local-ring-trdeg.json`: split item, following Stacks Algebra Tag 00P1.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-type-domain-dimension-trdeg.json`: new statement node for Tag 00P0; unsplit; no Mathlib match after LeanSearch, LeanFinder, Loogle, and source grep.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-dimension-at-point-components.json`: new statement node for Tag 00OT; unsplit; no Mathlib match after LeanSearch, LeanFinder, Loogle, and source grep.
- `coord/reports/E1/lem-weil-pbc-dimension-at-point-local-ring-trdeg.md`: this report.

## Attachments

None.

## WANTED

None.

## Errors found

The imported item had the correct Tag 00P1 statement and existing three-kind Mathlib search, but no proof. Its exact source proof depends on Tags 00P0 and 00OT, for which no exact DAG nodes existed; those are now explicit new unsplit nodes. The assigned unit `sk-thm-p1` concerns proper base change for the projective line and does not mathematically route to this dimension-theory lemma; this pre-existing unit assignment appears administrative, so no unit record was changed.

## Unfinished

The two new dependency nodes are intentionally unsplit Stage 1 items. No Lean was written or compiled.

## Review by E1

I read Algebra Lemmas 00P1, 00P0, and 00OT in `algebra.tex`. The item states 00P1 without changing its field, finite-type algebra, prime, local dimension, or residue-field hypotheses. The 00P0 child states both the dimension/transcendence-degree equality and the maximal-local-ring clause found in the source; the 00OT child states all three equal quantities, so neither is a restatement of the item. In Step 1, 00P0 applies to the domain $S/\mathfrak p$ and 00OS supplies maximal-chain length. Step 2 uses Noetherianity and the minimal-prime/localization correspondence for exactly the primes below $\mathfrak p$. Step 3 computes $\dim S_{\mathfrak p}$ from those chains. Step 4 uses 00OT for the components through $x$ and concatenates maximal chains below and above $\mathfrak p$; 00OS makes their lengths equal to the dimensions of the finite-type domains $S/\mathfrak q_j$. I checked the generic prime of a domain and a closed point as edge cases; both reduce to the expected specializations. Each new node introduces its objects, has an exact Stacks tag/label, no proof fields, and recorded LeanSearch, LeanFinder/Loogle, and Mathlib grep searches. The DAG search by 00P0/00OT and the statements found no existing exact node. The delivery is one item-only commit, with no cycle or route change; no correction was sent back.
