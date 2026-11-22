# Intrinsic vs. Mismatch-Induced DefEq Report: Slow Derived Tensor

Lean 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, historical source
`bdab171985a`.  Runs used one Lean thread, the validated READY2-4.33.1
release/counters binaries, `timeout 3600`, and `/usr/bin/time -v`.

## Experiment 1: `tensorObj` provider ladder

### 1. Variants

* **M (matched diagnostic):** `imTensorMatched` compares two `tensorObj`
  expressions in the same derived category.  Each side has an independent
  `let` provider with the same `MonoidalCategoryStruct` construction.
* **O (original):** `probes/im/original.lean` is the established equality
  whose left side uses the ordinary derived-category provider and whose right
  side uses the `DerivedMonoidal Qh` representation.  The selected root is
  argument 2, the `MonoidalCategoryStruct` provider.
* **A (aligned diagnostic):** `imTensorAligned` reverses the two same-category
  `let` providers while retaining the `tensorObj` consumer.
* **R (restored):** the O probe was rerun after M/A.

The M/A declarations use `debug.skipKernelTC` only to defer the exact equality
comparison to the explicit `Kernel.isDefEq` call.  They are diagnostic
comparisons because the original cross-representation type cannot be retained
with a matched provider without changing the category argument.

### 2. Expression pairs

The O root is the exact argument-2 pair printed by the probe:
`inferInstance/2` versus `inferInstance/2`, sizes `1785/11973`, under the
12-binder `tensorObj` context.  The outer `tensorObj` consumer and equality
obligation are unchanged; the first divergence is the representation/provider
inside argument 2.

M and A print `letE` versus `letE`, sizes `2770/2770`, `Expr.equal=false`,
and result `true`.  The two lets are independently elaborated and therefore
avoid an identity shortcut while reducing to the same provider path.

### 3. Kernel cost

| Variant | Uninstrumented process wall | Counter root | Calls | Comparison / reduction | Max depth | Expr proxy | RSS proxy | Result |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| M | 2.22 s | 0 ms | below trace threshold | below 1 ms threshold | not reported | not reported | 3,568,196 kB process peak | true |
| O | 46.73 s | 44.428 s | 6,269,622 | 23.981 / 20.446 s | 96 | 238,999,955 / 7,986,065,736 B | 3,529,113,600 B delta | true |
| A | 2.22 s | 0 ms | below trace threshold | below 1 ms threshold | not reported | not reported | 3,569,948 kB process peak | true |
| R | not rerun uninstrumented | 42.013 s | 6,269,622 | 23.016 / 18.997 s | 96 | 238,999,955 / 7,986,065,736 B | 3,524,263,936 B delta | true |

The O root had 18,804,316 WHNF requests, 10,639,573 Delta unfolds,
9,414,298 Beta reductions, 1,409,880 projections, 79,290 proposition
comparisons, and 46,522 Pi-domain comparisons.  Dependent labels were
18.879 s comparison plus 16.970 s reduction; proposition labels were 5.102 s
plus 3.476 s.  The direct Delta time was 0.819 s.  Pair capture was disabled
in this fresh counters run; the validated prior trace captured 3,333,872
distinct and 1,666,128 repeated ordered pairs, with 79,290 distinct
proposition pairs.  M/A had no root above the 1 ms reporting threshold.

O/R have exactly the same call count, depth, branch family, and provider pair
sizes.  Their time difference is runtime variation, not a changed expression.

### 4. Operation-specific analysis

The immediate `tensorObj`/provider comparison is the entry point.  Its
exclusive cost is in the dependent proposition subtrees reached after the
provider unfolds: projection, application, second-WHNF, and proof-irrelevance
branches dominate.  The largest proof-position groups in O were
`instAddHomFunctor._proof_2` (14.664 s),
`functorCategoryPreadditive._proof_4` (3.465 s), and
`functorCategoryPreadditive._proof_1` (2.721 s), all inclusive descendants.
The direct provider operation is therefore a path marker; the costly work is
the dependent structure it exposes.

M/A are cheap non-identical conversions while O/R are 44-second roots with
the same consumer.  This is strong **H2 (mismatch-induced cost)** evidence.
The repeated dependent proof comparisons mean the mismatch also amplifies a
pre-existing dependent comparison pattern (**H3**), but this matched control
does not show meaningful intrinsic cost for the full provider family (**H1**
is not supported here).

## Unif_hint

No genuine unification problem can be isolated in the imported Tensor theorem.
The critical provider is already elaborated in the stored declaration; adding
a hint would change that provider or its category argument.  U1/U2 are
therefore unavailable and no Kernel optimization claim is made.

## Context control

M/A keep the `tensorObj` consumer and its local category context but use a
same-category diagnostic pair.  O/R are the same argument-2 pair under the
original 12-binder context and have identical call counts and depth.  The
matched pair is not the exact O pair, so the comparison supports mismatch
induction without claiming a pure standalone context effect.

## Experiment 2: shared-provider control (IM §6)

No valid S0/S1/S2 matrix exists in the historical source.  The previous
same-path and shared-provider probes add an explicit `MonoidalCategoryStruct`
parameter.  That changes the inferred/declared telescope and removes the
original conversion: the original sizes were `5361/18817`, while the shared
variant was `2283/3917`; its direct final checks were millisecond-scale after
elaboration.  The same-path expression was structurally equal rather than an
independently rebuilt provider.  These are invalid fixed-root controls, so no
sharing or pointer-identity causal estimate is assigned.

## Conclusion

Directly measured: the O/R argument-2 pair is `inferInstance`/`inferInstance`
at sizes `1785/11973`, costs about 42--44 s, and performs 6,269,622 recursive
calls; M/A use independent `let` providers at `2770/2770`, are non-identical,
and complete below 1 ms; and most O time is in dependent proposition
descendants rather than direct Delta unfolding.  Inferred: the original
representation mismatch induces nearly all measured cost, with an interaction
through the already expensive dependent proof pattern.  A falsifying control
would preserve the cross-category telescope while replacing only the provider;
the historical source has no type-correct way to do that.
