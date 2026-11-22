# Intrinsic vs. Mismatch-Induced DefEq Report: Derived-Completion Cone

Lean 4.33.1 (`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, historical source
`9ba4d01f55c`.  Runs used one Lean thread, the validated READY2-4.33.1
release/counters binaries, `timeout 3600`, and `/usr/bin/time -v`.
Probe files are under `probes/im/`.  Process-local root IDs are not used as
cross-run identities.

## Experiment 1: Cone conversion ladder

### 1. Variants

* **M (matched diagnostic):** `matchedCone` keeps the `Cone` consumer and
  compares `Cone (matchedLeft J I K)` with `Cone (matchedRight J I K)`.  Both
  wrappers reduce to the named `DerivedCategory.derivedCompletionDiagram`, but
  they are independently elaborated constants.
* **O (original):** `probes/im/original.lean` is the historical inline
  `Cone (quotPowFunctor J I ⋙ tensorLeft K)` declaration.  Its inferred and
  declared types are the known eight-binder root conversion.
* **A (aligned diagnostic):** `alignedCone` keeps the same `Cone` consumer and
  uses two independently elaborated wrappers around the named diagram, the
  validated alignment used by the historical fix.
* **R (restored):** the original inline probe was rerun after M/A.

M/A use `debug.skipKernelTC` only to defer the final comparison to the
explicit `Kernel.isDefEq` call in the probe.  This preserves the root
obligation while avoiding declaration checking before the pair is printed; it
does not change the compared expressions.

### 2. Expression pairs

The O pair is the inferred value type versus the declared type of
`inlineCone`; the source-level heads are both `Cone`, with the first
structural divergence in the inline functor/derived monoidal provider
arguments.  READY2 identifies it as root 482 in these runs.

For M and A, the probe printed `Expr.equal=false`, outer `forallE` heads, and
inferred/declared sizes `1169/1493`.  The relevant consumer remains `Cone` and
the two sides are definitionally equal.  M is therefore a matched diagnostic
analogue of O, not a strict replay of the historical inline provider pair: the
named diagram boundary is necessary to make a cheap non-mismatched control.

### 3. Kernel cost

| Variant | Uninstrumented process wall | Counter root | Calls | Comparison / reduction | Max depth | Expr proxy | RSS proxy | Result |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| M | 2.16 s | 0 ms | below trace threshold | below 1 ms threshold | not reported | not reported | 3,763,260 kB process peak | equal |
| O | 120.05 s | 102.215 s | 12,220,822 | 51.019 / 51.196 s | 111 | 602,995,532 / 20,134,518,928 B | 10,189,537,280 B delta | deterministic timeout |
| A | 2.16 s | 0 ms | below trace threshold | below 1 ms threshold | not reported | not reported | 3,763,260 kB process peak | equal |
| R | not rerun uninstrumented | 107.031 s | 12,220,822 | 52.614 / 54.417 s | 111 | 602,995,532 / 20,134,518,928 B | 10,183,639,040 B delta | deterministic timeout |

O branch counts were quick 5,535,266; projection 3,115,313; application
2,133,228; second-WHNF 1,053,662; proof-irrelevance 187,630; and exception
76.  It made 43,167,510 WHNF requests, 25,821,810 Delta unfolds, 24,729,507
Beta reductions, 4,248,404 projections, and 187,634 proposition comparisons.
The disjoint dependent labels were 38.372 s comparison plus 39.678 s
reduction; proposition labels were 12.647 s plus 11.518 s.  The trace pair
capture was disabled for the fresh counters run, so exact/structural repeat
counts are unavailable there; the validated prior trace captured
3,416,239 distinct and 1,583,761 repeated ordered pairs, with no repeated
proposition pair.  M/A had no root above the 1 ms reporting threshold.

The O/R call identity and branch counts match exactly; their exclusive times
vary with runtime load.  This is the required reversibility check.

### 4. Operation-specific analysis

The direct `Cone`/functor application branch is not the measured bottleneck.
The prior component trace for this same root measured an inclusive
`tensorLeft`/`Functor.obj` path of 122.069 s, including a nested
`DFunLike.coe`/`NatTrans.app` subtree of 105.417 s.  Those are inclusive path
subtrees, not additive operation costs.  The direct Delta time was only
2.061 s in O.  The expensive work is the dependent body and generated
equality-proposition descendants under the application path.

M/A are cheap while O is timeout-scale, with the same consumer and a valid
non-identical pair in M.  This supports **H2 (mismatch-induced cost)** for the
historical root, with an interaction component in the dependent proposition
descendants (**H3**) because the original provider divergence opens the wide
path.  M does not establish intrinsic cost for the full inline provider
pattern: its named-boundary analogue is below timer resolution.

## Experiment 2: `Functor.obj` / `Functor.map` diagnostics

The probe compares two independently named wrappers around the same named
diagram at object `op 0` and identity morphism `𝟙 (op 0)`.

| Operation | Left/right heads | Sizes | Exact pair? | DefEq time | Result |
| --- | --- | ---: | --- | ---: | --- |
| `Functor.obj` | `CategoryTheory.Functor.obj` / same | 995 / 995 | false | 0 ms | true |
| `Functor.map` | `CategoryTheory.Functor.map` / same | 1043 / 1043 | false | 0 ms | true |

These are matched, nontrivial conversions in the same functor family, but they
are diagnostic component comparisons rather than the full inline root.  No
READY2 root exceeded the 1 ms threshold and no descendant timer was entered.
The historical slow trace therefore identifies `Functor.obj` as a path marker;
its descendants, especially the dependent `NatTrans.app`/`DFunLike.coe`
subtree, own the cost.

## Unif_hint

No genuine unification problem remains at this imported historical root.  A
hint would change the already selected provider or named diagram, so U1/U2
would not preserve the same elaborated pair.  No Kernel optimization claim is
made.

## Context control

M/A and O/R retain the `Cone` consumer and the binder telescope, but M/A use a
named-diagram diagnostic pair rather than the exact inline provider pair.  The
direct `Functor.obj`/`Functor.map` pairs are standalone component checks and
are not the same ordered pair as the in-situ descendants.  The context
difference is recorded explicitly; no standalone-to-in-situ causal ratio is
claimed.

## Experiment 3: shared-provider control (IM §6)

No valid S0/S1/S2 historical matrix exists.  The Tensor candidate adds a
shared `MonoidalCategoryStruct` binder, changing the theorem telescope and the
root obligation; its inferred/declared sizes changed from `5361/18817` to
`2283/3917`.  The Cone explicit-instance and named-diagram candidates likewise
change either the telescope or the diagram consumer.  The resulting fast
controls do not compare the original fixed root, so they cannot distinguish
provider sharing from the changed trigger.  No shared-provider timing is
claimed and no synthetic benchmark is substituted.

## Conclusion

Directly measured: O/R are deep, mixed comparison/reduction roots; M/A and
the matched `Functor.obj`/`Functor.map` pairs are below 1 ms; O/R have the
same 12,220,822 calls and depth 111; and the expensive path is in dependent
application descendants.  Inferred: the inline representation mismatch
induces most of the additional work, while the application family is a path
marker rather than an intrinsically expensive branch.  A falsifying control
would be a strict same-inline-provider matched pair retaining the exact
historical telescope; source history supplies no valid construction of it.
