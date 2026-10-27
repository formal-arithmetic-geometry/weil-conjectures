## What changed

Proved `divisorRealization_iso`: a section-preserving equivariant torsor isomorphism
preserves the normalized integral extension, and applying the existing scalar and
pro-etale realization functions preserves that equality.

`FramedIntegralExtension` specializes the existing canonical relative-extension
predicate and construction. Naturality identifies its objectwise sheafification-unit
fibre formula with the previous restriction-of-one formula. Added proved invariance
and positive forget-support API lemmas. No source-library module or target signature
is changed. Change record: `coord/changes/E7-framed-integral-extension-canonical.md`.
Target semantic review should be refreshed for the transitive definition use.

## Proved and sorry left

Closed one of the five original holes:
`WeilConjectures.PurityFiniteSetting.divisorRealization_iso`
(node `lem-pur-divisor-normalized-realization`).

Four original holes remain in that same node:

- `WeilConjectures.PurityFiniteSetting.divisorRealization_additive`.
- `WeilConjectures.PurityFiniteSetting.divisorRealization_pullback`.
- `WeilConjectures.PurityFiniteSetting.divisorRealization_enlarge`.
- `WeilConjectures.PurityFiniteSetting.divisor_normalized_realization`.

No holes were added or split off. The supporting integral module contains no sorry.
The larger retained proof draft is kept in the sandbox scratchpad, outside delivery.

## No longer needed

No module is withdrawn. The invariance proof uses only the canonical integral
extension and congruence of the existing realization functions. The original DAG
route for the four unfinished assertions is retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The earlier attempt reported all five
holes closed before the delivery check succeeded. Its new scalar realization APIs
repeatedly exceeded the 60-second compile limit through concrete choice and Ext
kernel conversion. Profiling and several constructor/API repairs did not make that
full packet pass, so this delivery retains the proved invariance clause and the
compiling canonical integral-extension repair. The four other original holes are
reported honestly and left available for subsequent work.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
