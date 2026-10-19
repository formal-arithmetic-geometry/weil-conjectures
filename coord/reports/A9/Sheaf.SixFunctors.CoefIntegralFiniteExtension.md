## What changed

In `lean/Sheaf/SixFunctors/CoefIntegralFiniteExtension.lean`, proved
`WeilConjectures.IntegralFiniteExtension.completion_isIso`,
`WeilConjectures.IntegralFiniteExtension.dualizingDatum_nonempty`, and
`WeilConjectures.IntegralFiniteExtension.extension_complete`.

The completeness proofs use finiteFreeCompletedScalarComparison after transporting
between intrinsic and unrestricted completeness through purCoefficientModel.
Three proved private helpers establish invariance under isomorphism and this
predicate comparison. Added the proof-only import
`Sheaf.Paper.CompletedCoefficientPresentationTransport`.

The dualizing datum is extracted from prop_coef_integral_dualizing after obtaining
a finite dimension bound. Its reductions are the normalized counit comparisons
followed by the finite origins; their coherence follows from the two existing
transition equations.

The required initial dry run returned a Lean diagnostic in complete_iso. Repaired
its parenthesization before changing association explicitly. The resulting module,
including all three proofs, compiled successfully in the resumed session (exit 0,
23.8 seconds). Subsequent attempts to validate three exploratory private helpers
received no answer from the compile server: exit 124 after 190, 201 and 208 seconds.
The unused exploratory helpers have been removed, restoring that validated version.
No push was attempted and no delivery commit exists.

## Proved and sorry left

Three of the five original holes are closed and were compiled together:

- `WeilConjectures.IntegralFiniteExtension.completion_isIso`.
- `WeilConjectures.IntegralFiniteExtension.dualizingDatum_nonempty`.
- `WeilConjectures.IntegralFiniteExtension.extension_complete`.

Two original holes remain, both attached to `lem-coef-integral-finite-extension`:

- `WeilConjectures.IntegralFiniteExtension.u_existsUnique`.
- `WeilConjectures.coef_integral_finite_extension`.

No holes were added. This is an interrupted working state, not a completed delivery.

## No longer needed

None. No original imports, modules or nodes were pruned. The remaining main theorem
retains its original proof plan and its declared dependencies. Unused exploratory
private helpers have been removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction has been made. Progress is blocked by repeated lack of a
response from the remote compile server; lcompile.py reports busy or unreachable,
not a Lean per-file timeout. The most recent three completed retries returned exit
124 after 190, 201 and 208 seconds. Earlier server failures remain recorded in
`compile-resume.log`.

For continuation: u_existsUnique needs a coherent map of the normalized coefficient
systems and faithfulness on these constructible mapping groups. The available
sequentialTowerEvaluation_full supplies existence of a coherent derived map but
not uniqueness from its evaluations. The latter requires the finite mapping-group
Mittag-Leffler argument from the node. For the main theorem, existing
scalarHomOrdinary_isIso and scalarHomCompleted use a differently normalized closed
tensor presentation. Their identification with the explicit evaluation transpose
in this module remains to be proved; neither equality of arbitrary derived maps
from their level evaluations nor an arbitrary choice of comparison is justified.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
