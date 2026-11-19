# Kernel-timeout candidates

Collected from merged project history and the dumped Zulip discussions. `real` means the change appears to alter what the kernel checks and is a reproduction target; `excluded` is recorded here for the top-level README rather than built as a case.

- `212f97dd22a` (2026-11-05), `IndEtaleDerivedImageHomCounit.lean`: global-Hom counit naturality; explicit abstract functor/counit arguments remove a kernel timeout. **case: ImageHomCounit (cost)**.
- `b400b43ec29` (2026-11-05), `IntegralComparisonPullbackRealizationShifts.lean`: comm-shift localization; wrapper vocabulary avoids kernel unfolding. **case: IntegralComparisonPullbackRealizationShifts (cost)**.
- `f66ad18a9ed` (2026-11-05), `IndEtaleDerivedImageHom{Adjunction,Comp,Counit}.lean`: image-Hom naturality; **F66Adj is a cost case; Comp is equal-cost; Counit is current-master incompatible**.
- `6e654a169f7` (2026-11-05), `EtaleScalarConstantPullback.lean`: **current-master representation mismatch before a valid target result**.
- `0676f555de6` (2026-11-02), `FiniteBaseChangeRestrictionMateTransport.lean`: **case: FiniteBaseChangeRestrictionMateTransport (high Kernel cost at the historical budget; reduced-budget probe times out)**.
- `f4946fdb6b6` (2026-11-02), `OrderedSpectralLattices.lean`: **case: OrderedSpectralRawLattices (hard Kernel timeout after a one-line current API port)**.
- `2f3ec5f4a16` (2026-11-05), `DiagonalLocalChernPullbackData.lean`: consistent endpoint types cut kernel memory. **candidate; parent source hits a later missing `Additive` instance under current master**.
- `77a08aac58b` (2026-11-05), four heavy modules: **attempted; `derivedTensorHomShiftComparison_component` still fails in a shared helper after the instance rename, and the other modules have current application/instance/rewrite mismatches before target**.
- `5e80d330d08` (2026-11-05), `CanonicalOrdinaryTensorInverseAssociativity.lean`: split proof and avoid abstracted-proof mismatches. **candidate; parent source hits a later representation mismatch under current master**.
- `a8c848cdde3` (2026-11-05), finite etale integral boundary: split shared terms to bound kernel memory. **candidate; current parent source reaches a later representation mismatch before the target can be measured**.
- `8ca2e912b93` (2026-11-05), OrderedExchange and Etale transpose components: **case: EtaleHomComparisonReversedExact (cost) after current instance rename; OrderedExchange remains unported**.
- `5b0d50455a6` (2026-11-05), diagonal trace/coefficient modules: **representative boundary probe reaches current typeclass/type/rewrite errors before the target**.
- `8afc7df6d06` (2026-11-05), pod-reindexing/projection/point-fiber/reduction modules: **representative point-fiber probe did not complete within the shared-server budget**.
- `d6a6682d7e7` (2026-10-28), `IntegralTensorRestrictionMateModel`: **complete historical Before and After fail before target on current `HSMul` and rewrite/type mismatches (2:57.41 / 1:38.16)**.
- `b94d64de19a` (2026-10-27), `PointFiberAlgClosed`: **current derived-category composition and `CommShift` mismatches before the target**.
- `9460df68701` (2026-10-26), TraceFormula integral reduction-counit: **fixed form passes; parent has current API type mismatches before the target**.
- `c3af60ee018` (2026-10-31), SmoothPurityOpenDescentNormalization: **both forms hit current unsolved-goal/`simp` mismatches before the target**.
- `ed3d39ddb5d` (2026-11-05), RealPushforward: fixes a kernel timeout in `isReal_higherLowerShriek_one`. **case: RealPushforward (hard failure)**.
- `e2d8b540cba` (2026-11-07), real-purity proof: **case: RealPurity (hard failure; historical After also times out on 4.35.0; Master passes)**.
- `9439ba41195` (2026-11-05), padic split base change: scoped kernel-check budget. **excluded** if only a heartbeat budget change remains.
- `7cef97103d4` (2026-11-05), split coefficient change: **missing current `HasTensor₄ObjExt` instances prevent the target**.
- `d89eb25ab20`, `a9bedd44ffd`, `8219abe7709` (#2654/#2657/#2667): heartbeat-only cleanup batches; **excluded** unless a constituent diff also changes kernel workload.
- Zulip #2185 (`BoundedOpenForget`, `BoundedProperProjectionSquare`, earlier `SmoothPurity`): `whnf`/`isDefEq` elaborator timeouts, not kernel cases; **excluded**.
- Zulip #1719/#1732 (`finiteSemilinearTraceEquation`): explicitly requested kernel-skipped diagnostic; classify separately after the 2x2 test, not a confirmed kernel case from the dump alone.
- Zulip #621/#624 (`PerfectOverlapObjectRealizationCoreData`): a kernel deterministic timeout fixed with `@[no_expose]`; **real candidate** if the old declaration can be reconstructed.
