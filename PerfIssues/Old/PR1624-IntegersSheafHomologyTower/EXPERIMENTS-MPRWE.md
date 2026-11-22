# Mismatch Provenance and Recursive Workload Report

Case: PR1624-IntegersSheafHomologyTower
Lean / mathlib: Lean 4.35.0, source snapshot 1ef1fddac73; earlier IM/AD
measurements with READY2-4.35.0.
Root: complete dependent `Iso.trans` endpoint, with two `Functor.comp`
descendants.

## 1. Root mismatch

The endpoint `Functor.comp` arguments 2 and 3 are the first recorded
representation divergence. The original dependent endpoint consumer is retained
only in O/R snapshots; exact terms are not serialized by READY2.

## 2. Matched baseline

`MatchedDiagnostic`/`MatchedGeneric` are **A3 diagnostic** controls. The exact
old endpoint consumer could not be replayed with the available olean closure;
the same-family `Functor.comp` pair is non-structural and measured 0.050 ms,
one call, depth 0 (earlier IM round 2). It is not evidence for an A0 root.

## 3. Provenance distribution

Earlier O trace root: 6,598,545 calls, 37,377.645 ms comparison-exclusive,
29,061.999 ms reduction-exclusive, depth 88; 3,361,091 distinct and 1,638,909
repeated pairs. READY2 lacks parent IDs and reduction links.

| Provenance | Calls | Exclusive comparison | Share |
|---|---:|---:|---:|
| M0 | 1 root entry (inferred) | not separable | 0% attributable |
| M1 | not classifiable | not classifiable | Unclassified |
| M2 | not classifiable | not classifiable | Unclassified |
| Matched descendants | not classifiable | not classifiable | Unclassified |
| Unclassified | 6,598,544 recursive calls (inferred) | 37,377.645 ms measured total | 100% of attributable trace |

## 4. Newly exposed divergences

The two isolated endpoint checks were 17,942 and 30,066 ms (earlier IM), but
there is no parent-to-child trace proving whether they are M1, M2, or matched.

## 5. Selective descendant alignment

| Variant | Result |
|---|---|
| O | Earlier root: 53,520.575 ms, 6,598,545 calls. |
| O1/O2/O12/O-all | Unavailable. The broad aligned endpoint changes the dependent endpoint and removes M0; no child-only source type-checks under the original telescope. |
| R | No separately measured restored endpoint was available in the existing AD/IM artifacts; the restored source snapshot is retained for a future compatible replay. |

The available aligned endpoint was 5.256 s / 456,393 calls, but it is an
invalid C control for this question.

## 6. Conclusion

The standalone matched diagnostic is cheap, while the dependent endpoint is
expensive and alignment removes most work. The endpoint context was historically
labeled **D/E**; that label is superseded by the round-5 READY3.2 partition and
uniform outcome **C** below.
The restored source snapshot retains the original declaration context; no
separate restored endpoint timing was available.

## MPRWE round 2 (superseded historical table)

## MPRWE round 4 (superseded by round 5)

The earlier “source failed before expensive root” result was caused by the
round-4 execution setup selecting a stale/unavailable instrumented 4.35.0
binary while the source worktree had advanced. It is not a current source
obstruction.

## MPRWE round 5 (READY3.2; current)

The source probe snapshot is `1ef1fddac73`; the read-only current-case worktree
revision used for this run is `2e92d5989ff`. The available READY3.2
instrumented binary was used with one Lean thread and `timeout 3600`. The
counter run selected root **22078** with **6,598,545** calls, depth 88, and
**25,760.364 ms** comparison-exclusive time. The pinned trace selected the
same root and call total, with **40,168.150 ms** aggregate
comparison-exclusive time; the increase is trace hash/path bookkeeping. Raw
coverage is 1,483/6,598,545 calls (0.022%), and the analyzer is READY3.2.

| Provenance | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.035 | 0.000% |
| M1 | 5,215,138 | 40,089.547 | 99.804% |
| M2 | 287 | 2.919 | 0.007% |
| Matched | 1,383,111 | 75.412 | 0.188% |
| Unclassified | 8 | 0.237 | 0.001% |

Top-five aggregate paths reviewed for each non-empty label are recorded below
(exclusive milliseconds). M1: `__other__` 11,733.955; `root/argument[3]/argument[5]/binder_body[3]/argument[5]/argument[8]/*`
6,039.649; `root/argument[2]/argument[7]/proposition_type/binder_body[5]/argument[2]/*`
5,163.531; `root/argument[2]/argument[7]/proposition_type/binder_body[5]/argument[0]/*`
3,825.495; `root/argument[2]/argument[5]/binder_body[3]/argument[2]/argument[2]/*`
1,902.248. M2: `__other__` 0.620; `root/argument[2]/argument[4]/binder_body[1]/argument[0]/argument[0]/*`
0.473; `root/argument[2]/argument[7]/proposition_type/binder_body[5]/argument[2]/*`
0.231; `root/argument[2]/argument[5]/binder_body[3]/argument[2]/argument[2]/*`
0.166; `root/argument[2]/argument[7]/proposition_type/binder_body[5]/argument[1]/*`
0.128. Matched: `__other__` 23.170; the corresponding five leading paths
are 9.941, 9.845, 6.646, and 3.641 ms. Unclassified: six buckets total,
led by `__other__` at 0.090 ms.

The top raw M1 representatives are `LinearMap.proj` and `LinearMap.mk` at
depths 61–79. The top raw M2 representatives are `Functor.comp/Functor.comp`,
`HasSheafify/HasSheafify`, `HMul.hMul/HMul.hMul`, and the corresponding
`Functor.comp` and `HMul.hMul` paths; their preceding exposure records are
the `initial_whnf` and `projection_whnf` reductions on `Functor.comp` to
`Functor.mk`, `HasSheafify`, and `Subtype.mk`.

The broad aligned endpoint was rerun as the C attempt. It type-checks only
after changing the dependent telescope and removing M0, and its selected root
has **456,393 calls** and **1,480.487 ms** counter comparison-exclusive time.
It is therefore invalid as a descendant-only C control. The O and R source
snapshots are byte-identical, so restoration is the original 6,598,545-call
root. With M2 0.007% and Matched 0.188%, the uniform round-5 rule gives
Outcome **C**.

## MPRWE round 3 (READY3.2; superseded historical table)

Shares are M1 99.809%, M2 0.006%, Matched 0.185%, Unclassified 0.001%.
The endpoint alignment remains root-changing and invalid for C.
