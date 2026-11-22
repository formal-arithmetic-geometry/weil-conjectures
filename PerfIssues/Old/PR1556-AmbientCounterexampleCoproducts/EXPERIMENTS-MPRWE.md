# Mismatch Provenance and Recursive Workload Report

Case: PR1556-AmbientCounterexampleCoproducts
Lean / mathlib: Lean 4.35.0, source snapshot 1ef1fddac73; earlier IM/AD
measurements with READY2-4.35.0.
Root: final generated congruence proposition domain, `NatTrans.app` major
argument 6.
Snapshots: `OriginalNatTrans`, `MatchedNatTrans`, `AlignedNatTrans`,
`RestoredNatTrans` in `probes/mprwe/`.

## 1. Root mismatch

Both outer heads are `NatTrans.app`. Arguments 0--5 match; argument 6 is the
first major-premise divergence and argument 7 is a `Functor.obj` descendant.
The exact printed terms are not retained by READY2, so the report uses the
recorded head/argument path rather than inventing a pretty-printed term.

## 2. Matched baseline

Baseline level: **A1 diagnostic**. `MatchedNatTrans` keeps the application
consumer and application pair, reconstructing both major premises through one
provider. It is non-structural and takes 2,074.191 ms with 284,842 calls and
1,055.447 ms exclusive comparison (earlier IM/READY2 measurement). It does not
preserve the complete original dependent telescope, so it is not A0.

## 3. Provenance distribution

Earlier O trace: 6,670,198 calls, 34,922.251 ms comparison-exclusive,
38,267.345 ms reduction-exclusive, depth 213. The trace captured 3,428,653
distinct and 1,571,347 repeated expression pairs, but no parent IDs or local
context.

| Provenance | Calls | Exclusive comparison | Share |
|---|---:|---:|---:|
| M0 | 1 root entry (inferred) | not separable | 0% attributable |
| M1 | not classifiable | not classifiable | Unclassified |
| M2 | not classifiable | not classifiable | Unclassified |
| Matched descendants | not classifiable | not classifiable | Unclassified |
| Unclassified | 6,670,197 recursive calls (inferred) | 34,922.251 ms measured total | 100% of attributable trace |

Dependent timers were 27,807.890/30,338.311 ms and proposition timers
7,063.879/7,858.518 ms (comparison/reduction); they overlap and are not added.

## 4. Newly exposed divergences

The major-premise descent into nested `NatTrans.app`, projections, and the
`Functor.obj` argument is visible in the source snapshots. READY2 cannot say
which reduction first exposed a distinct representation difference, so no M2
node or fan-out is claimed.

## 5. Selective descendant alignment

| Variant | Result |
|---|---|
| O | Earlier IM root: 73,189.597 ms, 6,670,198 calls. |
| O1/O2/O12/O-all | Unavailable as valid C controls. `AlignedNatTrans` replaces major argument 6, removing M0 and changing the root obligation. |
| R | Earlier restored root: 70,107 ms direct application comparison. It restores M0 but is not selective. |

The matched diagnostic is a valid A1 replacement, not a C intervention.
The restored source snapshot keeps the original declaration context; its R
number is the earlier direct pair restoration from the meta probe.

## 6. Conclusion

The matched application itself costs about 2.07 s, while O/R cost about
67--70 s in direct checks. This establishes a strong mismatch-sensitive effect,
but the READY2 trace cannot split it into M1 versus M2 or matched descendants.
Outcome **E** (insufficient provenance), with a substantial known matched
floor and an unclassified mismatch amplification.
