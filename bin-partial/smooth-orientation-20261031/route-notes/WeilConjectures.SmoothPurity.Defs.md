## HANDED TO HOUYI (2026-10-31, Zulip #1325)
`smoothOrientation` and `smoothOrientation_baseChange` are now constructed upstream by Houyi. Do NOT fill or restate
`smoothOrientation` here and do not build orientation base change. The priority root def-route-smooth-orientation is
removed (Weil coord/priority-roots.txt) and the node is paused on Codex. Still ours in WeilConjectures.SmoothPurity.Defs:
`isIso_smoothPurityMap`, `boundedConstructible_tateTwistDerived`, the smoothPurityIso open-immersion lemmas.
The text below is the earlier plan, kept as the route record for the handover.

## TOP PRIORITY (owner order 2026-10-29): fill `smoothOrientation` first

The first sorry to close in this module is `AlgebraicGeometry.ProEtale.CondensedRing.smoothOrientation` (~line 165,
@[no_expose], DAG node def-route-smooth-orientation). Since 54b34df8f73 `smoothTrace` is
`Rf_!(smoothOrientation) >> counit` (blueprint def-pur-smooth-trace), so every trace property here, Houyi's
exists_iso_smoothTrace_baseChange (trace formula) and batches 3/4 wait on it. Then isIso_smoothPurityMap (~1707), which
is the statement that the orientation is an iso (comes with the construction), then the open-immersion lemmas
(~1857, ~1905).

Construction (node statement of def-route-smooth-orientation; blueprint sec-smooth-purity: def-pur-smooth-trace,
sk-prop-sp-orientation, sk-thm-purity-transport Steps 1-2): finite orientations phi_n (diagonal + deformation to the
normal cone, normalized by integration on A^1) -> strict integral tower -> completed integral -> rational -> Qbar_l
condensed; alpha = G(u) o c_0 o a~^{-1}.

Sorry-free pieces to assemble (do not rebuild):
- step 1 phi_n: Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothAdjunctionGeneralBase`;
- step 2 towers: Sheaf.Paper.CondensedTateIntegralTower `AlgebraicGeometry.Scheme.PurityIntegralTower.condensedTateIntegralTower`,
  `ReconstructionResult` (already imported here);
- step 3 c_0: Sheaf.Paper.CondensedExceptionalReconstruction `WeilConjectures.CondensedExceptionalReconstruction.condensed_exceptional_reconstruction`;
- step 4 a, u: Sheaf.Paper.CondensedTateRealization `AlgebraicGeometry.ProEtale.CondensedTateRealization.condensed_tate_realization`;
- Sheaf.Paper.FinitePuritySourceUnitReduction (imported);
- possibly already the same map: Sheaf.Paper.TowerTracePurityComparisonData (`orientation`), Sheaf.Paper.NormalizedOrientationPerfectDuality
  (`SfPackageIntegralOrientation`, `SfPackageCommonOrientation`), Sheaf.Paper.OrientationIntegralCoefficientTwists;
- A^1 / vector-bundle normalization (finite level): Sheaf.AlgebraicGeometry.VectorBundleIntegration, FiniteRingBundleSectionOrientation,
  Sheaf.Paper.StandardAffineSectionOrientation, Sheaf.AlgebraicGeometry.ProjectiveLineTrace.

Lean: the step results are Prop (exists / Nonempty / exists-unique); define via Classical.choose and prove in this module a
characterizing lemma `smoothOrientation_spec` (alpha = G(u) o c_0 o a~^{-1}) plus `IsIso (smoothOrientation ...)`, so
downstream never unfolds the @[no_expose] body. Keep names and types of smoothOrientation / smoothTrace unchanged.
New imports are fine if they create no cycle.


---
Added 2026-10-29 18:05 CST (lead; Houyi, Zulip #1255): together with `smoothOrientation`, prove its base-change property as a named lemma `smoothOrientation_baseChange` (gamma_f commutes with base change, blueprint sk-prop-sp-orientation). Houyi's proof of `exists_iso_smoothTrace_baseChange` uses exactly this one statement, currently a named sorry in his separate file on top of our branch sheaf/smooth-trace-orientation (PR #1821). Look at his branch for `smoothOrientation_baseChange` and state ours identically.
