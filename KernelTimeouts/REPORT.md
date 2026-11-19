# Kernel timeout diagnosis report

Lean/Mathlib 4.35.0, single-threaded Lean, synchronous elaboration
(`-DElab.async=false`), and the master build tree were used for the controls.
Kernel-skipped runs use `-Ddebug.skipKernelTC=true` only as a diagnostic.
Times are wall seconds; peak RSS is in the case README files.

| Case | Phase gate (Before on / skipped) | Exact Kernel component | Primary / contributing | Evidence | Before / After |
|---|---:|---|---|---|---|
| [RealPushforward](RealPushforward/CLASSIFICATION.md) | 54.73 s timeout / 3.00 s | final `exact this`: `charpolyRev` versus `localPolynomial` equality | A / E | confirmed site; strong mechanism | 54.94 s timeout / 2.80 s |
| [ImageHomCounit](ImageHomCounit/CLASSIFICATION.md) | 54.53 s / 2.90 s | final `exact h` over concrete derived-category wrapper | E / A, C | confirmed | 55.53 s / 2.60 s |
| [IntegralComparisonPullbackRealizationShifts](IntegralComparisonPullbackRealizationShifts/CLASSIFICATION.md) | 105.67 s / 11.11 s | `change` after localization, wrapper endpoint to `DerivedCategory.Q` | A / E, C | confirmed | 102.27 s / 23.61 s |
| [F66Adj](F66Adj/CLASSIFICATION.md) | 116.48 s / 4.30 s | `homIso_naturality_of_counit` application at concrete `NatTrans.app` | E / A, C | confirmed | 116.47 s / 3.40 s |
| [FiniteBaseChangeRestrictionMateTransport](FiniteBaseChangeRestrictionMateTransport/CLASSIFICATION.md) | 577.08 s / 4.70 s | `hb` argument conversion into `transport_from_unit` | A / C, E | confirmed | 577.08 s / 4.10 s |
| [EtaleHomComparisonReversedExact](EtaleHomComparisonReversedExact/CLASSIFICATION.md) | 109.87 s / 3.40 s | concrete `hv` argument to `derivedTensorHomShiftComparison_component` | E / A, C | confirmed site; strong mechanism | 110.07 s / 3.50 s |
| [RealPurity](RealPurity/CLASSIFICATION.md) | 58.94 s timeout / ~7.4 s | final `exact h` in `hreal'` after stalk equivalence rewrite | unclassified; B/C/E candidates | confirmed site; mechanism plausible | 58.94 s timeout / 6.10 s Master |
| [OrderedSpectralRawLattices](OrderedSpectralRawLattices/CLASSIFICATION.md) | 45.73 s timeout / 13.11 s | `small_spectral_raw_lattices` target application | E / A | confirmed site; strong mechanism | 45.73 s timeout / 13.91 s |

## Diagnosis paths

### RealPushforward

The type-only and prefix-with-`sorry` controls are cheap. Only checking the
old final equality reproduces the timeout. The printed heads are
`LinearMap.charpolyRev` and `FrobeniusModule.localPolynomial`; the fixed
generic lemma avoids reducing that concrete representation.

### ImageHomCounit

The concrete `conjugateEquiv_counit` result is cheap when discarded and slow
only when checked against the declaration. The inferred type is over an
expanded sheaf-derived category, while the goal uses `DerivedCategoryModule`;
diagnostics show 842,612 `Add.add` unfolds. The fixed direct theorem avoids the
wrapper conversion.

### Integral comparison

The localization setup and generator goal are cheap. The explicit `change`
from a localized endpoint to `DerivedCategory.Q.obj P.obj` triggers 1,193,814
`Add.add` and 1,047,896 `PresheafOfModules.obj` unfolds. Later proof terms are
not needed to reproduce the cost. The fixed wrapper definitions preserve the
endpoint vocabulary.

### F66Adj

The type is cheap, but applying the abstract helper to concrete global-Hom
and restriction functors already costs 35.32 seconds and 511,948 Kernel
unfolds. Its result carries an abstract `GT.map` application; the goal expands
the concrete global-Hom path. Binding coefficient variance `γ` makes these
expressions line up.

### Finite-base transport

The direct helper application is slow even when its result is discarded.
Replacing only the `hb` right-square argument makes the reduced-budget probe
cheap; replacing `hγ` does not. The expensive argument conversion unfolds
concrete equivalence, functor, and module instance paths. The fixed helper
abstracts these records first.

### Etale Hom comparison

The generic component application is the first hotspot: 29.02 seconds and
421,348 Kernel unfolds with the final handoff discarded. Replacing its `hv`
transpose-premise argument reduces the probe to about 3.3 seconds, isolating
that argument conversion. Its result is stated using a derived-category
shift, while the goal uses the `DerivedCategoryModule` wrapper.
`transport_exact` closes the small endpoint conversion in the fixed proof.

### RealPurity

The constituent equivalence and the final purity calculation are cheap in
isolation. The final `exact h` in `hreal'` is the only operation that restores
the 59-second timeout. The printed equality has the same mathematical
polynomial on both sides but carries different stalk/representation proof
arguments after transport. The exact hidden mismatch has not been isolated.
The historical split remains insufficient on this
toolchain; current Master passes in 6.10 seconds.

### Ordered spectral raw lattices

The declared type and a separately named helper result both take 13.91
seconds. The final `exact h` reproduces a 48.73-second Kernel timeout, so the
expensive check is the inferred type of
`exists_stratified_lisse_integral_lattice` against the folded
`RawStratifiedLattices` goal. The printed result expands the `∀ L` lattice
predicate while the goal retains the private wrapper. The historical fix
scopes three local-ring/domain instances so both sides use matching proofs;
target diagnostics show 23,580 `Functor.obj` reductions.

## Cross-case observations

Observed: all eight Before forms have a large synchronous Kernel-on versus
Kernel-skipped gap. The isolated hotspots are conversions at application or
endpoint boundaries; no case was localized to recursive computation. The
diagnostic counters are dominated by routine `Add.add`, `Functor.obj`, or
module-instance unfolds after the high-level conversion starts.

Interpretation: the recurring mechanism is representation alignment. Abstract
helpers, explicit instance paths, and endpoint transport reduce the amount of
dependent structure that Kernel must unfold. Proof abstraction is primary in
RealPurity remains unclassified at the mechanism level because the exact
expression difference has not been isolated.

## Part 2: additional candidate sweep

The historical kernel-fix inventory was searched for candidates that could be
ported and measured in under twenty minutes. Three older commits were
inspected and measured where their retained source could run on current
master. The previously attempted candidates are listed separately below:

| Candidate | Result |
|---|---|
| `eea424dc3a7` locally-bijective instance alignment | Current parent and fixed sources were measured, but both still hit current API/type errors before a valid target result. Not added. |
| `ad9cebd0557` EssentiallySmall instance alignment | Current parent and fixed sources were measured, but both still hit current API/type errors before a valid target result. Not added. |
| `f4946fdb6b6` OrderedSpectralLattices instance alignment | Added as [OrderedSpectralRawLattices](OrderedSpectralRawLattices/CLASSIFICATION.md); one current API rename was applied to both source forms. |
| `77a08aac58b`, `6e654a169f7`, `2f3ec5f4a16`, `5e80d330d08`, `a8c848cdde3`, `5b0d50455a6`, `8afc7df6d06`, `d6a6682d7e7`, `b94d64de19a`, `9460df68701`, `c3af60ee018` | Already attempted in the prior rounds; current parent prefixes fail before the target or do not produce a valid Kernel result. Reasons are listed in `README.md` and `CANDIDATES.md`. |

No additional case is added without a faithful Before declaration and a
Kernel-on/skipped measurement. The dataset therefore has eight real cases,
with the exact diagnosis requested by Round 4 recorded above.

## Reproduction

Each case directory contains `Before.lean`, `After.lean` (and `Master.lean`
for RealPurity), the classification record, and the cited probes. Run a probe
from the master build tree with:

```text
LEAN_NUM_THREADS=1 /usr/bin/time -v timeout 1800 nice -n 10 lake env lean \
  -DElab.async=false -Ddebug.skipKernelTC=false \
  /path/to/dataset/KernelTimeouts/<Case>/probes/<Probe>.lean
```
