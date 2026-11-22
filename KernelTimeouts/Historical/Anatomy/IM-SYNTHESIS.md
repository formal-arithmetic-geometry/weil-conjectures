# Intrinsic vs. Mismatch-Induced DefEq: Cross-Case Synthesis

This synthesis combines the two historical probes in this directory with the
published KernelTimeouts and PerfIssues IM records.  Historical runs use Lean
4.33.1 / READY2-4.33.1; current runs use READY2-4.35.0 and current revision
`a2ec460045b`.  Values below are measured unless explicitly marked inferred.
Inclusive path samples are not treated as exclusive operation time.

## Historical cases

| Case | M | O / R | A | Main evidence | Classification |
| --- | --- | --- | --- | --- | --- |
| Slow Derived Tensor | independent `let` providers, `2770/2770` nodes, non-identical, 0 ms | provider pair `1785/11973`; 44.428 s counter root, 6,269,622 calls, depth 96; R 42.013 s, same calls | reversed same-category provider, 0 ms | direct `tensorObj` provider branch is cheap only when the category representation is matched; O spends 23.981 s comparison and 20.446 s reduction in dependent proof descendants | **H2**, with H3 amplification in dependent proofs |
| Derived-Completion Cone | independent named-diagram wrappers, `1169/1493`, non-identical, 0 ms | inline root 102.215 s, 12,220,822 calls, depth 111; R 107.031 s, same calls | named-diagram wrappers, 0 ms | `Functor.obj`/`Functor.map` direct pairs are 0 ms, while the in-situ `tensorLeft` path contains a 105.417 s inclusive `DFunLike.coe`/`NatTrans.app` subtree | **H2** for the inline mismatch; H3 in the dependent descendant path |

The historical matched controls are diagnostic analogues because a strict
same-inline-provider pair cannot be constructed without restoring the provider
divergence.  They nevertheless preserve the `Cone` or `tensorObj` consumer,
are non-syntactically identical, and perform real conversion.  The shared
provider S0/S1/S2 experiment is invalid in both cases: adding a provider binder
or naming the diagram changes the telescope or consumer, so it removes the
root rather than changing only sharing.

## Operation-family matrix

| Operation family | Matched cost | Original cost | Aligned cost | In-situ vs standalone | Exclusive owner / verdict |
| --- | --- | --- | --- | --- | --- |
| `NatTrans.app` and endpoint components | PR1556 matched diagnostic 2.074 s / 284,842 calls; PR1625 matched nested application 0 ms; historical direct component pairs 0 ms | PR1556 73.190 s / 6.670M; PR1625 114.240 s / 11.758M; Image 50.730 s; Finite 661.952 s | PR1556/1625/Image remove roots; Finite aligned setup removes the selected root | application-level pairs are cheap or moderate alone; in-situ descendants are large | `.app` is a path marker. **H3 + H2** for PR1556/1625; **H2** for endpoint bundles |
| `DFunLike.coe` | no strict fixed-provider M in current records; historical component controls 0 ms | F66 29.544 s; Etale 24.140 s; RealPurity 53.956 s; RealPushforward 52.072 s | F66/Etale aligned roots below threshold; polynomial/ring alignments vary by case | cost appears below coercion in dependent propositions, continuous-map composition, and matrix paths | descendant comparison owns cost. **H2** for F66/Etale; **H1 downstream + H2 trigger** for real cases |
| `Functor.obj` / `Functor.map` | NativePullTensor regular-provider M 1 ms; historical Cone object/map pairs 0 ms; no strict M for Ordered | NativePullTensor 22.805 s; Image 6.360M calls; Ordered 51.962 s | NativePull/Image/Ordered complete or remove selected roots; NativePull abbrev M remains 14.134 s | standalone matched object/map is cheap; dependent `Exists`/`Quiver.Hom` and endpoint contexts are expensive in situ | **H2** for provider mismatch, residual **H1/H3** when the context remains costly |
| `CategoryStruct.comp` / `LinearMap.comp` | no strict same-root M for PR1563 or Finite; PR1556/1625 matched application controls are cheap | PR1563 23.415 s; Finite 661.952 s; Integral 73.839 s | PR1563 remains 20.699 s; Finite selected root disappears; Integral first-leaf alignment remains expensive | nested compositions reach `.app` and dependent proposition bodies; direct composition branch is not isolated | **H1/H3** for PR1563 and Integral; **H2** for Finite’s endpoint bundle |
| `Matrix.charmatrix` | no strict polynomial M | RealPurity 53.956 s; RealPushforward 52.072 s | ring alignment does not remove Purity; polynomial alignment removes Pushforward selected root | the comparison-heavy `ContinuousMap`/`DFunLike.coe` family persists below the matrix operation | matrix branch is a path marker. **H1 downstream + H2/H3 trigger**, exact pair identity unresolved |
| dependent propositions / generated fields | strict M generally unavailable; PR1627, PR1624, PR2122 controls change the telescope or recursor context | PR1627 29.454 s; PR1624 53.521 s; PR2122 25.836 s; F66/Etale/Finite roots above | broad transports remove or reduce roots, but PR1563/RealPurity/Integral negative controls remain expensive | same-looking proposition work is more expensive in the fully instantiated parent; isolated proof-position checks can be cheap | dependent body and proposition comparison own cost. **H2** when alignment removes the tree; **H1/H3** for residual parent work |

The historical `Functor.obj`/`Functor.map` measurements are particularly
useful: both exact non-identical matched pairs completed below 1 ms, while the
Cone root’s in-situ path was timeout-scale.  This directly rules out assigning
the inclusive path sample to the operation branch itself.

## Per-dataset evidence

### KernelTimeouts

The current KernelTimeouts records classify ImageHomCounit, EtaleHom,
FiniteBaseChange, and F66Adj as mismatch-sensitive endpoint or dependent
bundles.  IntegralComparison is the clearest interaction case: aligning the
first visible leaf leaves a 73.839 s downstream root and a measured 46.686 s
inclusive nested `.app` descendant.  OrderedSpectralRawLattices restores the
domain route to about 35.939 s with the same approximately 18.945M calls,
showing that the route bundle is causal while the dependent `Functor.obj`
family still has substantial context cost.  RealPurity and RealPushforward
remain comparison-heavy under partial alignments, so they support intrinsic
downstream comparison plus a mismatch trigger rather than a pure H2 claim.

### PerfIssues

PR1556 and PR1625 provide the strongest application-level matched evidence:
matched application comparisons are 2.074 s or below timer resolution, while
original roots are 73.190 s and 114.240 s and restored roots return.  Native-
PullTensor gives the clearest `Functor.obj` result: a regular-provider matched
pair is 1 ms, the original is 22.805 s, and an abbrev provider remains 14.134
s, separating mismatch cost from residual context cost.  PR1563, PR1624,
PR1627, and PR2122 have no valid strict matched pair that preserves their
dependent telescope; their aligned controls therefore support H1/H3 only for
the residual endpoint pattern.  PR2122 was not freshly replayable because its
required imported olean was unavailable.

## `unif_hint`

No record demonstrates a Kernel optimization caused by `unif_hint`.  The
FiniteBaseChange probe contains a genuine `Site .ordinary X ≟ X.ProEt` hint,
but the mismatch is selected after elaboration and no fixed-expression U1
Kernel cost is claimed.  OrderedSpectral, EtaleHom, F66Adj, PR1627, the
historical Tensor, and the historical Cone have no safe U0/U1/U2 control that
preserves the imported provider, telescope, and root obligation.  Where a hint
would change an instance/provider, that is an elaboration representation
change; it must not be attributed to Kernel cost itself.

## Answers to IM §7 and §10

1. **Intrinsic matched cost:** a nontrivial matched application can have
   meaningful cost (PR1556), and residual dependent endpoints remain costly in
   PR1563/PR1624/RealPurity.  Historical `tensorObj`, `Cone`, and direct
   `Functor.obj`/`Functor.map` matched analogues are below timer resolution.
   There is no single project-wide H1 classification.
2. **Mismatch-induced work:** the historical Tensor and Cone controls change
   roughly 44 s and 102 s roots to below 1 ms, with identical O/R call counts;
   NativePullTensor changes 22.805 s to 1 ms; PR1556/1625 change 73/114 s to
   2.074 ms-scale or zero.  These are call and exclusive-time comparisons,
   not wall-time-only inferences.
3. **Operation versus descendant:** `NatTrans.app`, `DFunLike.coe`,
   `Functor.obj`, `CategoryStruct.comp`, and `Matrix.charmatrix` are usually
   path markers.  Exclusive ownership is in dependent proposition bodies,
   projections, nested applications, and continuous-map or generated-field
   descendants; the current instrumentation does not expose per-branch
   exclusive operation timers.
4. **Context sensitivity:** isolated matched components can be cheap while
   the same family is expensive in a fully instantiated parent.  PR1563 and
   PR1624 retain substantial cost after broad alignment; the historical roots
   show the strongest in-situ amplification.
5. **`unif_hint`:** measured evidence supports an elaboration/unification
   effect only.  No run proves a Kernel cost change with identical elaborated
   expressions.
6. **Shared providers:** no valid historical or current S0/S1/S2 matrix keeps
   the exact root, consumer, and telescope fixed.  Fast explicit-provider or
   named-diagram controls are therefore trigger-removal controls, not sharing
   experiments.

Overall, the data support three mechanisms rather than one: mismatch-induced
extra work is dominant for the historical roots and several endpoint bundles;
matched application or dependent endpoint comparisons show intrinsic cost in
some current cases; and the mismatch amplifies those patterns through deeper,
wider dependent descendants.  Operation names in inclusive traces should be
read as entry paths until branch-exclusive timing is available.
