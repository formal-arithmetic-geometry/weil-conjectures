# M1P kernel audit

This is the source audit for the exact release trees used by READY4. The
instrumentation is observational: it records existing recursive calls and
does not alter transparency, reduction order, cache operations, shortcuts,
or the root obligation.

## B1: comparison branches

The 4.35.0 source is `<leank-root>/mprwe35/src/kernel/type_checker.cpp`; the
4.33.1 source is `<leank-root>/mprwe33-r3/src/kernel/type_checker.cpp`.
The relevant functions have the same control-flow topology in both trees;
the line numbers differ because 4.33.1 has the native-reduction helper.

| Function / branch | 4.35.0 | 4.33.1 | propagation role |
|---|---:|---:|---|
| `is_def_eq_binding` | 1479 | 1512 | compares binder domains, then instantiated dependent bodies |
| `quick_is_def_eq` | 1544 | 1577 | cheap structural/cache path; enters binding comparison |
| `is_def_eq_args` | 1572 | 1605 | reverse argument congruence optimization |
| `try_eta_expansion_core` / `try_eta_struct_core` | 1586 / 1602 | 1619 / 1635 | eta body and structure field/type paths |
| `is_def_eq_app` | 1628 | 1661 | function head followed by each application argument |
| `is_def_eq_proof_irrel` | 1652 | 1685 | infer Prop types and compare proposition types |
| `lazy_delta_reduction_step` | 1735 | 1768 | compare reducibility hints; expose one or both definitions |
| `lazy_delta_reduction` | 1826 | 1859 | reduction continuation and exposed-body comparisons |
| `lazy_delta_proj_reduction` | 1857 | 1896 | reduce projection components, then compare them |
| `is_def_eq_core` | 1909 | 1948 | main branch sequence and recursive dispatch |
| `whnf` / `whnf_core` entry points | 1432 / nearby | 1462 / nearby | WHNF, beta/iota/zeta and native/Nat exposure |
| `failed_before`, `cache_failure`, `succeeded_before`, `cache_success` | 1669--1713 | 1702--1746 | memoized failed/successful pair checks |

The `is_def_eq_core` sequence is: quick check; initial WHNF; proof
irrelevance; lazy delta; same constant/free-variable checks; projection
handling; second WHNF; application congruence; eta and structure eta; string
and unit-like fallbacks; then failure. The branch names in the transition
matrix are emitted at these existing recursive call sites, rather than
inferred from expression heads.

## B3: reducibility audit

`lazy_delta_reduction_step` reads each side's actual `is_delta` metadata and
`get_hints()`. If only one side is delta-reducible, the opposite projection
application is exposed first when possible (`try_unfold_proj_app`); otherwise
that side is unfolded through `unfold_definition` and `whnf_core`. If both
are reducible, `compare(d_t->get_hints(), d_s->get_hints())` chooses the
side with the lower hint ordering. Equal regular hints attempt
`const_levels` and `is_def_eq_args` before unfolding both sides; a failed
attempt is memoized by `cache_failure`. Thus the instrumentation's
`reduction_since_parent`, `reduced_side`, and `exposed` fields describe
actual hint decisions and projection exposure, not source-level attributes.

In the selected roots, reductions before child calls are common in the
`second_whnf`, `projection`, and `application -> function-head` transitions.
The transition rows also report the reduction time accumulated by the child
subtree. No change was made to hint comparison or declaration-height use.

## B4: historical comparison

The READY4 NativePullTensor root and the full historical Derived-Completion
Cone root share the same high-level families: application function-head and
argument congruence, projection descent, proof proposition-type checks,
lazy-delta argument/body checks, and WHNF fallback. They differ in where the
cost concentrates:

* NativePullTensor is mixed deep/wide. Its largest rows are application
  function-head (189,446 calls, 6,702.805 ms), application argument (693,554,
  6,407.333 ms), lazy-delta argument (887,573, 3,146.107 ms), and projection
  argument/projection (787,570 combined, 3,609.994 ms).
* The full Cone is also deep/wide, but projection descent dominates:
  projection -> projection is 2,951,993 calls and 38,983.983 ms;
  application -> argument is 4,542,955 calls and 21,618.337 ms; and
  second-WHNF fallback is 1,053,662 calls and 11,712.799 ms.
  Dependent-body and proposition-type rows are visible but cheaper.
* The historical Slow Derived Tensor control has the same projection and
  application families. Its READY3.2 profile recorded 1,103,968 projection
  branch calls, 1,264,606 application calls, 1,468,972 lazy-delta calls, and
  79,290 proposition comparisons. This agrees with the READY4 family map;
  the Cone's much larger projection-to-projection chain is the main
  workload-specific difference.

The shared sequence is therefore application/projection descent, occasional
lazy-delta or WHNF exposure, then proposition/dependent checks. This is
consistent with mixed propagation: broad congruence fan-out repeatedly
feeds long recursive chains.

## Interpretation boundary

The reports provide branch and topology evidence. They do not claim that a
transition alone proves the original source mismatch, and no M2 causal
interpretation is made here. The only intervention attempted for the Cone
was the existing type-correctness check described in the experiment report;
no valid M0-preserving descendant replacement was available.
