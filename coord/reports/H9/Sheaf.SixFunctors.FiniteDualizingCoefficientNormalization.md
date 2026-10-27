## What changed

The parent module now imports two proof-only split modules and proves its original
conjunction by combining their statements.  The split modules are
`Sheaf.SixFunctors.FiniteDualizingCompactSupportIdentity` and
`Sheaf.SixFunctors.FiniteDualizingQuotientNormalization`.  The original public
statement and its `FiniteDualizingData` public import are unchanged.

## Proved and sorry left

No original theorem clause was closed.  The parent theorem is reduced by a real
conjunction introduction to two strictly smaller named theorems.  The two new
public theorem holes are
`WeilConjectures.finiteDualizing_compact_support_identity` (node
`lem-coef-dualizing-compact-support-identity`) and
`WeilConjectures.finiteDualizing_quotient_normalization` (node
`lem-coef-dualizing-quotient-normalization`).  The first contains the identity
compact-support clause; the second contains the regular-unit clause and both
successive-quotient clauses.  No definition contains `sorry`.

## No longer needed

No dependency module or declaration was pruned.  The parent uses the two split
modules and `FiniteDualizingData`; the three declared proof dependencies remain
the source of the two split proof plans.  The Mathlib searches found no exact
replacement theorem.

## Where the brief, the DAG or earlier work was wrong

The existing generic compact-scalar coherence and coefficient-mate declarations
do not identify the concrete finite-dualizing compact-support map with the
`normalizedOriginScalarUnit` appearing in the identity clause.  A direct
simplification leaves precisely that categorical mate equation as a goal.  The
same missing identification is needed before the regular-unit and quotient
cocycle clauses can be assembled.  These are therefore recorded as two genuine
lower-level mate-pasting statements rather than asserted by an alias or a
weakened theorem.

## New nodes

`lem-coef-dualizing-compact-support-identity` records the identity quotient
compact-support mate equation and its proof plan.

`lem-coef-dualizing-quotient-normalization` records the regular scalar-unit
normalization and the two successive-quotient composition equations.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.FiniteDualizingCoefficientNormalization": "d754437e54ddc9eeacfe3a363e7f243a495ddcd3", "Sheaf.SixFunctors.FiniteDualizingCompactSupportIdentity": "7faf3229ce8840326a7bb704b6f344cc42893949", "Sheaf.SixFunctors.FiniteDualizingQuotientNormalization": "bfb5f86144a22dc56fae60d0b32a73f5e6a3fc14"}, "results": {}, "time": "2026-10-28T00:49:27+0800", "transitive": 0, "version": 1}
```

## Second reading by H9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
