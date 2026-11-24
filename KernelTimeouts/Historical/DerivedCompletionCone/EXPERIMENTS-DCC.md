# Derived-Completion Cone: Cache Effectiveness and Repeated DefEq Work

## 10.1 Cache implementation and lifetime

The pinned Lean 4.33.1 source has `type_checker::state` caches for positive
DefEq (`m_success`), the regular-head failure shortcut (`m_failure`), WHNF,
cheap WHNF-core, inference (two maps for infer-only/check), and definition
unfolding. DefEq keys are unordered expression pairs; the other keys are
expressions. The state is allocated by `type_checker(environment, ...)`, shared
by checkers constructed from `type_checker::state&`, and destroyed with the
owning checker. It is not process-global. No reset occurs between recursive
calls; declaration/checker construction creates a new state in the normal
path. Cheap WHNF-core lookups are eligible, but cheap modes do not insert.
Unfolding is cached only for universe-parameterized constants.

| Cache | Exists | Key | Lookup / insert | Lifetime | Eligible modes |
|---|---|---|---|---|---|
| Positive DefEq | yes | unordered Expr pair | `succeeded_before` / `cache_success` | checker state | successful comparisons |
| Failure | yes | unordered Expr pair | `failed_before` / `cache_failure` | checker state | regular-head argument shortcut only |
| WHNF | yes | Expr | `whnf` lookup / reduction insert | checker state | non-easy WHNF requests |
| WHNF-core | yes | Expr | `whnf_core` lookup / insert | checker state | insert only when both cheap flags false |
| Infer type | yes | Expr, infer-only split | `infer_type_core` lookup / insert | checker state | closed expressions |
| Unfold | yes | Expr | `unfold_definition_core` lookup / insert | checker state | constants with universe levels |

Lifetime diagram:

```text
Process
  Kernel checker instance(s)
    shared type_checker::state
      DefEq, failure, WHNF, WHNF-core, infer-type, unfolding caches
Root conversion entry -> existing state contents
Root conversion exit  -> entries remain until state destruction
State reused by      -> checkers explicitly built from the same state
State reset at       -> new checker state; no in-root reset observed
```

## 10.2 Pair repetition census

The compact census ran over the complete 12,220,822-call root. It used
collision-checked structural Expr equality and the local-context object
identity (`local_ctx.raw()`) in the contextual key. Pair order was
canonicalized for the census while the original order remained in the
comparison. The complete run measured:

| Pair class | Calls | Unique contextual pairs | Repeated invocations | Pairs 2+ | Pairs 10+ | Pairs 100+ |
|---|---:|---:|---:|---:|---:|---:|
| All DefEq entries | 12,220,822 | 8,690,612 | 3,530,210 | 1,646,052 | 56,405 | 0 |
| M1 / M2 / Matched / proposition / projection / application / dependent-body | not separately retained by compact census | not separately retained | not separately retained | not separately retained | not separately retained | not separately retained |

Top repeated contextual keys (hashes are identifiers, not printable
expressions) by repeated subtree time were:

| Rank | First call | Invocations | Left hash | Right hash | Repeat subtree |
|---:|---:|---:|---:|---:|---:|
| 1 | 11,761,391 | 8 | 2,911,607,547 | 503,261,367 | 1.318 ms |
| 2 | 10,198,471 | 3 | 866,375,896 | 3,360,132,705 | 1.188 ms |
| 3 | 10,185,784 | 3 | 2,859,243,880 | 851,497,486 | 1.161 ms |
| 4 | 9,382,884 | 8 | 951,063,028 | 362,188,382 | 1.053 ms |
| 5 | 9,199,428 | 2 | 3,129,642,882 | 1,242,489,102 | 1.050 ms |

Separate normalized-pair and reversed-order totals were not emitted by this
compact build; they require recording the pre/post-WHNF pair in the same
event record. The old five-million-event JSON trace was not reused.

## 10.3 Cache hit/miss report

| Cache | Lookups | Hits | Misses | Hit rate | Inserts |
|---|---:|---:|---:|---:|---:|
| Positive DefEq | 17,188,411 | 2,688,584 | 14,499,827 | 15.64% | 8,215,090 |
| Failure shortcut | 74,390 | 0 | 74,390 | 0.00% | 0 |
| WHNF | 9,669,592 | 889,859 | 8,779,733 | 9.20% | source does not count aggregate inserts |
| WHNF-core | 104,653,433 | 19,210,284 | 85,443,149 | 18.36% | 20,934,042 |
| Inference | 25,498,560 | 15,919,341 | 9,579,219 | 62.43% | 9,579,219 |
| Unfolding | 25,821,810 | 25,821,514 | 296 | 100.00% | 296 |

Positive hits were attached to 2,688,584 DefEq invocations. The cache lookup
time itself was not separately timed in READY4.2; it is included in the
comparison counters. Descendant work avoided by each hit therefore remains a
counterfactual estimate, not an observed additive time.

## 10.4 Repeated versus unique workload

| Work category | Calls | Exclusive/direct time | M1 calls / time | Main transition |
|---|---:|---:|---:|---|
| Unique contextual pairs | 8,690,612 first invocations | 123,445.370 ms including reduction | M1 dominates overall | projection and application descent |
| Repeated pairs, direct invocation | 3,530,210 repeats | 1,370.118 ms | not separately retained | mixed |
| Repeated-pair originating subtrees | non-overlapping origin view | 1,370.118 ms observed in this instrumentation | not separately retained | mixed |
| Same Expr under different contexts | included in contextual key | not separately isolated | not separately retained | dependent descent |
| Unclassified | 3 calls in accepted READY4.1 aggregate | 0.121 ms | negligible | other |

The repeat direct-time share is about 1.1% of the 124.815 s instrumented
root wall time. Inclusive descendant totals are not summed across ancestors.
The compact attribution assigns each repeat's direct cost to that invocation;
the top repeated subtree was 1.318 ms. The accepted complete transition
aggregate separately shows 9,356,262 M1 calls and 86,910.655 ms root
exclusive time, led by projection-to-projection (2,951,994 calls,
38,999.493 ms) and application-argument (4,542,956 calls, 21,805.155 ms).

## 10.5 Cache-bypass controls

Each variant used a separate process and the unchanged full inline root. All
returned the same deterministic kernel-timeout diagnostic and the same
declaration warnings.

| Variant | Root wall | Recursive calls | Result | Interpretation |
|---|---:|---:|---|---|
| K0 baseline | 124.815 s | 12,220,822 | timeout unchanged | reference |
| K1 instrumented | 124.815 s | 12,220,822 | timeout unchanged | compact counters |
| K2 positive-read bypass | 73.634 s | 25,851,433 | timeout unchanged | positive cache suppresses repeated traversal |
| K3 WHNF-read bypass | 147.121 s | 12,096,848 | timeout unchanged | more reduction time, similar call count |
| K4 WHNF-core-read bypass | 122.087 s | 10,633,864 | timeout unchanged | traversal shifts under timeout boundary |
| K5 failure-read bypass | 154.293 s | 12,220,822 | timeout unchanged | zero failure hits; overhead/traversal cost only |

The timeout-boundary variants cannot be compared by wall time alone; call
counts and semantic result are the controlled evidence.

## 10.6 Conclusion

1. The pinned Kernel has positive DefEq caching: **Demonstrated**.
2. It serves 2,688,584 positive lookups (15.64% of 17,188,411): **Demonstrated**.
3. The failure cache matters for this root: **Not observed** (0 hits).
4. WHNF work is reused (WHNF 9.20%, WHNF-core 18.36% hit rates), but exact avoided DefEq descendants are **Unknown** without per-hit subtree snapshots.
5. Repeated cache-miss comparison direct time is 1,370.118 ms, about 1.1% of instrumented wall time; an exact exclusive-time partition against cache lookup time is **Unknown**.
6. Unique contextual first invocations account for 8,690,612 of 12,220,822 entries and dominate the measured direct time: **Strongly supported**.
7. Repeated pairs generate only small observed repeated subtrees; the largest was 1.318 ms: **Strongly supported** for low observed repeated cost.
8. Bypassing positive reads changes traversal to 25.85M calls while preserving the result: **Demonstrated**.
9. Decision: **Cache-protected repetition**. Repeated pairs are frequent, but positive cache reuse suppresses most potential repeated recursive work; the remaining expensive workload is unique M1 expansion. Evidence level: **Strongly supported**.
10. Unmeasured: normalized-pair/reversed-order census, per-transition contextual breakdown, cache lookup-exclusive time, and non-overlapping per-hit descendant savings. These require a compact binary event stream carrying pre/post-reduction expressions, context identity, cache event IDs, and subtree close records; the available JSON stream exceeded 2 GB and was deleted.

