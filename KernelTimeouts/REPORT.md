# Kernel timeout classification report

Lean/Mathlib 4.35.0 on the Weil server, single-threaded Lean, `timeout 1800`, `nice -n 10`. Baseline times are wall seconds and peak RSS in MiB (the source READMEs retain exact KB). Phase controls used `-DElab.async=false -Ddebug.skipKernelTC=true`; Kernel-on controls used the same synchronous setting. Kernel skip is diagnostic only. The branch is based on the reviewed `dataset/kernel-timeouts` checkout; no library file is changed.

The measurement tree `the master build tree` is at revision `1ef1fddac73e` with Lean 4.35.0 and its built Mathlib; the host reports 80 logical cores and 308 GiB RAM. Load varied during runs, so CPU and RSS together with the synchronous controls carry more weight than wall time alone. Each run had `LEAN_NUM_THREADS=1`; at most five of our Lean runs overlapped, below the six-process limit.

| Case | Phase gate (Before on / skipped) | Cost site | Primary; contributing | Strength | Before / After on 4.35.0 |
|---|---|---|---|---|---|
| [RealPushforward](RealPushforward/CLASSIFICATION.md) | 54.73 s timeout / 3.00 s ok | value, final concrete local-polynomial rewrite; exact conversion unresolved | A; E | strongly supported | 54.94 s timeout, 4,606 MiB / 2.80 s ok, 3,053 MiB |
| [ImageHomCounit](ImageHomCounit/CLASSIFICATION.md) | 54.53 / 2.90 s | value, concrete `conjugateEquiv_counit` application | E; A, C | strongly supported | 55.53 s ok, 7,291 MiB / 2.60 s ok, 2,729 MiB |
| [IntegralComparisonPullbackRealizationShifts](IntegralComparisonPullbackRealizationShifts/CLASSIFICATION.md) | 105.67 / 11.11 s | value, localization/comm-shift endpoint conversion; exact prefix unresolved | A; E, C | plausible site, strong phase | 102.27 s ok, 9,166 MiB / 23.61 s ok, 3,789 MiB |
| [F66Adj](F66Adj/CLASSIFICATION.md) | 116.48 / 4.30 s | value, coefficient-variance/`NatTrans.app` handoff | E; A, C | strongly supported | 116.47 s ok, 12,343 MiB / 3.40 s ok, 2,769 MiB |
| [FiniteBaseChangeRestrictionMateTransport](FiniteBaseChangeRestrictionMateTransport/CLASSIFICATION.md) | 577.08 / 4.70 s | value, direct `transport_from_unit` application to concrete records | A; C, E | strongly supported | 577.08 s ok, 23,346 MiB / 4.10 s ok, 2,269 MiB; 400,000-heartbeat probe: 88.46 s timeout, 5,597 MiB |
| [EtaleHomComparisonReversedExact](EtaleHomComparisonReversedExact/CLASSIFICATION.md) | 109.87 / 3.40 s | value, direct tensor-Hom shift theorem at concrete `derivedHom` endpoints | E; A, C | strongly supported | 110.07 s ok, 12,195 MiB / 3.50 s ok, 3,122 MiB |
| [RealPurity](RealPurity/CLASSIFICATION.md) | 59.44 s timeout / 7.40 s ok | value, large constituent/subquotient proof; exact child unresolved | B (plausible); C, A hypotheses | strong phase, plausible mechanism | 58.94 s timeout, 5,459 MiB / 58.84 s timeout, 5,454 MiB; Master 6.10 s ok |

## Observations

- All seven case Before files show a large Kernel-on versus Kernel-skipped difference; five current Before forms succeed slowly and two reproduce a deterministic timeout (RealPurity and RealPushforward). The FiniteBaseChange reduced-budget probe also times out.
- The fixed RealPurity revision still times out on 4.35.0. Its current master form passes, so the 2026-11-07 split alone is insufficient in this environment.
- The cost cases have Kernel-skipped times near their fixed forms. The integral comparison file has a larger common elaboration floor, about 11 seconds.
- Per-declaration profiling attributes 53.8 s, 53.6 s, 95.2 s, 117 s, 85.3 s, 110 s, and 52.2 s to type checking of the seven cases in table order. The RealPushforward and ImageHomCounit checks spend less than 0.4 s in tactics and 0.04 s in elaboration. ImageHomCounit diagnostics report 604,574 Kernel `Functor.obj` unfolds and 842,612 `Add.add` unfolds; counts identify activity, not the exact conversion pair.
- `8ca2e912b93` required only the anonymous derived-monoidal instance rename in a local attribute. `0676f555de6` required the current prefix/statement to host the historical direct proof body.

## Interpretations

- The common pattern in the successful repairs is a smaller Kernel conversion at an application boundary: abstract functors or exact endpoint transport keep dependent types syntactically aligned. This is a mechanism inference from controlled source changes and phase gates; exact elaborated expression pairs were not dumped.
- The RealPurity failure suggests the proof abstraction boundary remained expensive after splitting. No claim is made about the exact generated `_proof_n` subterm without a typed-sorry bisect.
- Source size and wall time alone were not used as Kernel evidence; the synchronous skip controls are the phase evidence.

## Unreproduced Candidates

These are not case-table rows because no valid target Kernel check was obtained on current master. The complete exclusion inventory is in [README.md](README.md) and [CANDIDATES.md](CANDIDATES.md).

| Candidate | Reason |
|---|---|
| `d6a6682d7e7` `restrictionTensor_mate_model` | Full historical Before and After fail before the target on missing `HSMul` instances and rewrite/type mismatches; 2:57.41 / 1:38.16. |
| `77a08aac58b` `derivedTensorHomShiftComparison_component` | Both forms fail in shared `normalized_transpose_aux` at line 42: current `Functor.map_comp_assoc` cannot match the changed shift-composition type; the one-line `map_comp` port also fails. |
| `8ca2e912b93` OrderedExchange rho/lambda split | The selected étale transpose component is a measured case; the larger OrderedExchange split has not been isolated into a declaration-level target on current master. |
| `f66ad18a9ed` `imageHomIso_counit` | Both historical forms reach a current `simp`/representation mismatch before the target; the separate `ImageHomCounit` case comes from `212f97dd22a`. |
| `6e654a169f7` `etaleScalarConstantPullback` | Current scalar-coefficient `change` no longer matches; the fixed body also reaches a `simp` mismatch. |
| `2f3ec5f4a16` `DiagonalLocalChernPullbackData` | Parent prefix reaches a missing current `Additive` instance before target. |
| `5e80d330d08` `CanonicalOrdinaryTensorInverseAssociativity` | Parent prefix reaches a current representation mismatch. |
| `a8c848cdde3` `DiagonalTraceFiniteEtaleIntegralBoundary` | Parent prefix reaches a representation mismatch after 4:35.48 / 14,350,036 KB RSS. |
| `77a08aac58b` `finiteEtaleDiagonalClass_postcomp_injective`, `geoP1Cohomology`, `purCoefficientRoosShiftNormalization` | Current application, `simp`, or rewrite mismatches before the target. |
| `7cef97103d4` split-coefficient map | Missing current `HasTensor₄ObjExt` instances before target. |
| `9460df68701` integral reduction counit | Parent hits three current API type mismatches before target. |
| `b94d64de19a` point-fiber colimit | Current derived-category composition and `CommShift` mismatches before target. |
| `5b0d50455a6` diagonal boundary | Current stuck typeclass, type, and rewrite errors in the parent prefix. |
| `8afc7df6d06` point-fiber integral family | Parent split file did not complete during the earlier shared-server probe; no valid target result. |
| `c3af60ee018` smooth-purity descent | Both forms hit current unsolved-goal/`simp` mismatches before target. |
| Zulip #621/#624 `PerfectOverlapObjectRealizationCoreData` | Historical declaration/source attachment unavailable in the dumps; no faithful Before term. |

Heartbeat-only changes and elaborator-only Zulip reports are excluded separately in [README.md](README.md).
