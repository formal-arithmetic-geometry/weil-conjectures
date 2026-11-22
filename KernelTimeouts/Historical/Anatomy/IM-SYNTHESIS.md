# Intrinsic vs. Mismatch-Induced DefEq: Cross-Case Synthesis

This synthesis combines the two historical probes in this directory with the
published KernelTimeouts and PerfIssues IM records.  Historical runs use Lean
4.33.1 / READY2-4.33.1; current runs use READY2-4.35.0 and current revision
`03f2a41973c`.  Values below are measured unless explicitly marked inferred.
Inclusive path samples are not treated as exclusive operation time.

## Historical cases

| Case | M | O / R | A | Main evidence | Classification |
| --- | --- | --- | --- | --- | --- |
| Slow Derived Tensor | diagnostic M: `letE`/`letE`, `2782/2782`, non-identical; 0.259 ms, 34 calls, depth 7 | provider pair `1785/11973`; 44.428 s counter root, 6,269,622 calls, depth 96; R 42.013 s, same calls | reversed same-category diagnostic pair; below 1 ms | direct `tensorObj` provider branch is cheap in the diagnostic match; O spends 23.981 s comparison and 20.446 s reduction in dependent proof descendants | **H2** for the measured root, with H3 amplification; full-root H1 is inconclusive because M is diagnostic |
| Derived-Completion Cone | diagnostic M: `forallE`/`forallE`, `1169/1493`, non-identical; 0.259 ms, 34 calls, depth 7 | inline root 102.215 s, 12,220,822 calls, depth 111; R 107.031 s, same calls | named-diagram diagnostic pair; below 1 ms | `Functor.obj`/`Functor.map` direct pairs are cheap, while the in-situ `tensorLeft` path contains a 105.417 s inclusive `DFunLike.coe`/`NatTrans.app` subtree | **H2** for the measured root, with H3 in descendants; full-root H1 is inconclusive because M is diagnostic |

Both historical M controls are **diagnostic**, not strict: they retain the
consumer and operation family but replace the original provider divergence and
full dependent obligation.  Fresh READY2 counters nevertheless show real
conversion in each M (34 recursive calls, depth 7, proposition comparisons,
and nonzero reduction work), so neither is an identity or pointer shortcut.
The shared-provider S0/S1/S2 experiment is invalid in both cases: adding a
provider binder or naming the diagram changes the telescope or consumer, so it
removes the root rather than changing only sharing.

## Operation-family matrix

| Operation family | Matched cost | Original cost | Aligned cost | In-situ vs standalone | Exclusive owner / verdict |
| --- | --- | --- | --- | --- | --- |
| `NatTrans.app` and endpoint components | historical diagnostic M 0.259 ms / 34 calls; current round-two diagnostics 0.03--5.933 ms | PR1556 73.190 s / 6.670M; PR1625 114.240 s / 11.758M; Image 48.566 s; Finite 612.036 s | PR1556/1625/Image remove roots; Finite aligned setup removes the selected root | application-level pairs are cheap or moderate alone; in-situ descendants are large | `.app` is a path marker. **H2** for endpoint bundles; **H3** where downstream work remains; full-root M claims are diagnostic |
| `DFunLike.coe` | no strict fixed-provider M; round-two diagnostic M rows are 0.03--5.933 ms | F66 29.649 s; Etale 24.301 s; RealPurity 53.575 s; RealPushforward 52.021 s | F66/Etale aligned roots below threshold; polynomial/ring alignments vary by case | cost appears below coercion in dependent propositions, continuous-map composition, and matrix paths | descendant comparison owns cost. **H2** support from O/A/R; strict H1 remains untested |
| `Functor.obj` / `Functor.map` | historical diagnostic M 0.259 ms / 34 calls; current diagnostics 0.309--4.680 ms; NativePullTensor has a 1 ms regular-provider component M | NativePullTensor 22.805 s; Image 6.360M calls; Ordered 36.145 s | NativePull/Image/Ordered alignments remove or reduce the selected route | standalone matched object/map is cheap; dependent `Exists`/`Quiver.Hom` and endpoint contexts are expensive in situ | **H2** for provider/route mismatch; residual **H1/H3** is context-sensitive; full-root round-two M is diagnostic |
| `CategoryStruct.comp` / `LinearMap.comp` | round-two diagnostic M: PR1563 1 ms, Finite 4.627 ms; no strict same-root M | PR1563 28.755 s; Finite 612.036 s; Integral 73.267 s | PR1563 remains costly after broad alignment; Finite selected root disappears; Integral first-leaf alignment remains expensive | nested compositions reach `.app` and dependent proposition bodies; direct composition branch is not isolated | **H2** support for the selected mismatch; **H1/H3** for residual PR1563/Integral work |
| `Matrix.charmatrix` | diagnostic M 0.029--0.030 ms / 15 calls; no strict polynomial M | RealPurity 53.575 s; RealPushforward 52.021 s | ring alignment does not remove Purity; polynomial alignment removes Pushforward selected root | the comparison-heavy `ContinuousMap`/`DFunLike.coe` family persists below the matrix operation | matrix branch is a path marker. **H2** for the removable polynomial route; **H1/H3** for residual downstream work |
| dependent propositions / generated fields | round-two M controls are diagnostic and cheap; strict full-root M generally unavailable | PR1627 29.454 s; PR1624 53.521 s; PR2122 25.836 s; F66/Etale/Finite roots above | broad transports remove or reduce roots, but PR1563/RealPurity/Integral negative controls remain expensive | same-looking proposition work is more expensive in the fully instantiated parent; isolated proof-position checks can be cheap | **H2** when alignment removes the tree; **H1/H3 or inconclusive** for residual parents |

The historical `Functor.obj`/`Functor.map` measurements are particularly
useful: the direct non-identical matched pairs are cheap, while the Cone root
performs timeout-scale in-situ work.  The historical M counters likewise show
real but diagnostic conversion.  This directly rules out assigning the
inclusive path sample to the operation branch itself.

## Round-two scope and validity

The fresh T3/P3 M rows are diagnostic controls: they retain the named
operation family and data-bearing type but use a smaller obligation than the
original consumer root.  They are useful for showing that the matched family
does real work and for exposing the O-versus-M branch shape, but a cheap M
does not establish that the full original root would be cheap.  The historical
M rows above have the same limitation, with the added READY2 validity result
that each performs 34 recursive conversions rather than an identity shortcut.

The strongest round-two mismatch evidence is therefore the reversible O/A/R
comparison.  Historical Tensor and Cone change 44.428 s / 102.215 s O roots
to sub-millisecond A controls and restore the same call counts in R.  In the
current cases, F66, Etale, Image, Finite, and Ordered show the same cheap
diagnostic M versus large O branch shape; Integral and RealPurity retain an
expensive aligned parent, so their full-root verdict remains interaction or
inconclusive rather than pure H2.

## Per-dataset evidence

### KernelTimeouts

The current KernelTimeouts records classify ImageHomCounit, EtaleHom,
FiniteBaseChange, and F66Adj as mismatch-sensitive endpoint or dependent
bundles.  IntegralComparison is the clearest interaction case: aligning the
first visible leaf leaves a 73.267 s downstream root and a measured 46.686 s
inclusive nested `.app` descendant.  OrderedSpectralRawLattices restores the
domain route to about 35.939 s with the same approximately 18.945M calls,
showing that the route bundle is causal while the dependent `Functor.obj`
family still has substantial context cost.  RealPurity and RealPushforward
remain comparison-heavy under partial alignments, so they support intrinsic
downstream comparison plus a mismatch trigger rather than a pure H2 claim.

### PerfIssues

PR1556 and PR1625 provide the strongest application-level matched evidence: matched application comparisons are 2.074 s or below timer resolution, while original roots are 73.190 s and 114.240 s and restored roots return. Round-two diagnostic M rows across both datasets are cheap but smaller than the original roots, so they do not upgrade those observations to strict full-root M controls.
Native-
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

1. **Intrinsic matched cost:** the historical M controls are nontrivial (34 calls, depth 7, 0.259 ms) but diagnostic, not strict full-root matches. Current evidence includes a meaningful matched application (PR1556) and residual dependent endpoints (PR1563/PR1624/RealPurity), while most round-two diagnostic M rows are cheap. There is no single project-wide H1 classification.
2. **Mismatch-induced work:** the historical Tensor and Cone controls change roughly 44 s and 102 s roots to 0.259 ms diagnostic conversions, with identical O/R call counts; NativePullTensor changes 22.805 s to 1 ms; PR1556/1625 change 73/114 s to millisecond-scale or zero. These are call and exclusive-time comparisons, not wall-time-only inferences.
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
