## HANDED TO HOUYI (2026-10-31, Zulip #1325)
`smoothOrientation` and `smoothOrientation_baseChange` are now constructed upstream by Houyi. Do NOT fill or restate
`smoothOrientation` here and do not build orientation base change. The priority root def-route-smooth-orientation is
removed (Weil coord/priority-roots.txt) and the node is paused on Codex. Still ours in WeilConjectures.SmoothPurity.Defs:
`isIso_smoothPurityMap`, `boundedConstructible_tateTwistDerived`, the smoothPurityIso open-immersion lemmas.
The text below is the earlier plan, kept as the route record for the handover.

## TOP PRIORITY (owner order 2026-10-29): the normalized smooth orientation gamma_f

Why: since commit 54b34df8f73 `smoothTrace := Rf_!(smoothOrientation) >> counit` (blueprint def-pur-smooth-trace:
Tr^sm_f = Tr_f o Rf_!(gamma_{f,Lambda_Y})). `AlgebraicGeometry.ProEtale.CondensedRing.smoothOrientation`
(@[no_expose], lean/WeilConjectures/SmoothPurity/Defs.lean, ~line 165) is still `sorry`, and this node is the root of the
whole smooth-trace route. It gates the trace formula (Houyi proves exists_iso_smoothTrace_baseChange from it) and
batches 3/4. Nothing on this route matters more right now.

### The construction (keep the node statement; it already follows the current blueprint)
Blueprint: literature/blueprint/latest/blueprint/sec-smooth-purity/
- sk-def-sp-trace/def-pur-smooth-trace.md (gamma_{f,Lambda_Y}),
- sk-prop-sp-orientation/ (finite orientation omega_f ~ Z/l^n(d)[2d] via diagonal + deformation to the normal bundle +
  vector-bundle purity; sk-prop-sp-orientation-charts: on an etale chart U -> A^d_Y it IS integration on A^d, i.e. the
  normalization by integration on the affine line),
- sk-thm-purity-transport/ (Steps 1-2: finite levels -> strict integral tower -> completed integral -> rational ->
  Qbar_l condensed coefficients).
Steps, as in the node statement:
1. finite orientations phi_n = gamma_{n,L_n} : A_n(d)[2d] ~ Rf_n^! A_n with their quotient comparisons
   [lem-pur-finite-smooth-adjunction-general-base];
2. strict towers L_n, M_n, R lim, canonical normalized reductions [lem-pur-condensed-tate-integral-tower];
3. adjunction comparison c_0 : U_X M ~ G(U_Y L), case (b), r = -2d [lem-pur-condensed-exceptional-reconstruction];
4. Tate realization a : U_X M ~ B_X(d)[2d] and unit u : U_Y L ~ 1_Y [lem-pur-condensed-tate-realization];
5. alpha = G(u) o c_0 o a~^{-1} : T_d -> G 1_Y.  This is smoothOrientation.

Stage 1 for this item: check that statement against the current blueprint, add the stage-1 record (searches, review
fields); a definition needs no proof steps, but if the "it is an isomorphism" sentence needs more than the
composition-of-isos remark, add one short step. New nodes only if a step really hides a lemma: statement-only,
status unsplit, NO `lean` field (Lean names in lean_candidates / split_report.lean_declarations).

### Library pieces already sorry-free on the server (reuse them, do not rebuild)
- Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase: `AlgebraicGeometry.Etale.FiniteSmoothPurity.finiteSmoothAdjunctionGeneralBase`
  (FiniteSmoothAdjunctionDatum, FiniteSmoothSystem; Nagata compactification) -- step 1.
  Behind it: Sheaf.Paper.FiniteSmoothLevelOfOrientation (`finiteSmoothLevelOfOrientation`),
  Sheaf.SecSmoothPurity.FiniteGeneralRingOrientation / FiniteGeneralRingOrientationAssembly (`assembleOrientation`),
  Sheaf.SecSmoothPurity.ReductionOrientation, Sheaf.Paper.FiniteCoefficientSmoothPurity
  (`WeilConjectures.PurityFiniteSetting.isIso_smoothPurityMap`), Sheaf.Paper.SmoothTrace (finite-coefficient
  `WeilConjectures.PurityFiniteSetting.smoothTrace`, `coefficientValuedSmoothTrace`).
- Sheaf.Paper.CondensedTateIntegralTower: `AlgebraicGeometry.Scheme.PurityIntegralTower.condensedTateIntegralTower`,
  `ReconstructionResult` (normalized towers M, L with eM, eL, ProjectionNormalized, Reconstructed,
  IdentifiesExceptional) -- step 2. Already imported by WeilConjectures.SmoothPurity.Defs.
- Sheaf.Paper.CondensedExceptionalReconstruction: `WeilConjectures.CondensedExceptionalReconstruction.condensed_exceptional_reconstruction`
  (Nonempty Family; comparison = `chosenComparison`) -- step 3.
- Sheaf.Paper.CondensedTateRealization: `AlgebraicGeometry.ProEtale.CondensedTateRealization.condensed_tate_realization`
  (exists-unique normalized realization `shiftedComparison`) -- step 4.
- Sheaf.Paper.FinitePuritySourceUnitReduction (`finitePuritySourceUnitReduction`), imported by Defs.
- Normalization by integration on A^1 / vector bundles (finite level, all sorry-free): Sheaf.AlgebraicGeometry.VectorBundleIntegration
  (`vectorBundleIntegration`), FiniteRingBundleSectionOrientation(+Data), BundleSectionOrientationMapExt,
  BundleSectionPurityUnitNormalization, Sheaf.Paper.StandardAffineSectionOrientation, Sheaf.Paper.OrientationCoordinateBoundaryPullback,
  Sheaf.AlgebraicGeometry.ProjectiveLineTrace. Use them only if a step needs the normalization explicitly; the phi_n
  of step 1 already carry it.
- Comparable tower orientation already written: Sheaf.Paper.TowerTracePurityComparisonData (`orientation`, `counitTrace`,
  tower/rational components), Sheaf.Paper.NormalizedOrientationPerfectDuality (`SfPackageIntegralOrientation`,
  `SfPackageRationalOrientationTrace`, `SfPackageCommonOrientation`), Sheaf.Paper.OrientationIntegralCoefficientTwists.
  Check whether one of these already is (or directly gives) alpha before assembling it by hand.
- Downstream consumer: Sheaf.SmoothPurity.TraceExistence `existsUnique_smoothTrace` takes any orientation iso gamma.

### Lean advice
The four step lemmas are Prop-valued (exists / Nonempty / exists-unique). Build the def from their data with
`Classical.choose`/`.some`, and ALSO state and prove the characterizing lemma (e.g. `smoothOrientation_spec`: alpha =
G(u) o c_0 o a~^{-1} for the specified maps, and `IsIso (smoothOrientation ...)`) in the same module, so
`isIso_smoothPurityMap`, the open-immersion lemmas and Houyi's base-change theorem can use it without unfolding the
@[no_expose] body. Keep the declaration name and type of smoothOrientation exactly. Adding imports of
CondensedExceptionalReconstruction / CondensedTateRealization to Defs is fine (check no cycle). Compile one file at a time.


---
Added 2026-10-29 18:05 CST (lead; Houyi, Zulip #1255): together with `smoothOrientation`, prove its base-change property as a named lemma `smoothOrientation_baseChange` (gamma_f commutes with base change, blueprint sk-prop-sp-orientation). Houyi's proof of `exists_iso_smoothTrace_baseChange` uses exactly this one statement, currently a named sorry in his separate file on top of our branch sheaf/smooth-trace-orientation (PR #1821). Look at his branch for `smoothOrientation_baseChange` and state ours identically.
