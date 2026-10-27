# Scheduled upstream sync 58206abfd -> 8bd69aede (2026-10-23T09:09:26Z)

## Reason

Routine sync with slopmaster2 (104 commits; ~/cc1/upsync-quick.py, the human 2026-10-20).

## Old

upstream base 58206abfd09baceb7eef474507b256fe55a951b0

## New

upstream base 8bd69aede181d65fe0934e5c23e246bd06b68b42; merge deleted-here 8, same 4, source-proof 1, take 215

Still quarantined, the tip's text written to the quarantined copy:

- `WeilConjectures.PoincareDuality.Poincare`
- `WeilConjectures.PoincareDuality.Verdier`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekBaseChange`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekInterchange`
- `WeilConjectures.SmoothPurity.Defs`
- `WeilConjectures.TraceFormula.Basic`

## Users

216 Lean file(s) changed by the merge and the canonical migration; 1084 node record(s) re-pointed by the migration.

## Status

landed

## Quarantine, round 1 (2026-10-23T10:18:46Z)

The global build of 9f8657e65e failed in 4 module(s); they and their importers, 9 module(s), were moved to quarantine/ (tools/rework.py, coord/rework.tsv):

- `Sheaf.Paper.FiniteReductionRestrictTensor`: error: Sheaf/Paper/FiniteReductionRestrictTensor.lean:54:30: failed to synthesize | changed by the upstream sync (upstream text, keep it; adapt our code): WeilConjectures.AlgebraicGeometry.Cohomology. (nodes lem-pur-finite-reduction-restrict-tensor)
- `Sheaf.SixFunctors.EvaluationDualityCompletion`: error: Sheaf/SixFunctors/EvaluationDualityCompletion.lean: bad import 'Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction' | changed by our landings (fix our code): 20261023T090235-ND-602192-223  (nodes lem-sfb-evaluation-duality-completion)
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek`: error: WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/OpenImmersionUpperShriek.lean: bad import 'WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriekIndependence' | changed

Importers taken out with them (6): `Sheaf.Paper.FiniteReductionConstructibility`, `Sheaf.Paper.FiniteReductionDerivedExtension`, `Sheaf.Paper.FiniteReductionEtaleConstructibility`, `Sheaf.Paper.FiniteReductionFlatExtension`, `Sheaf.Paper.FiniteReductionSystemCoherence`, `Sheaf.Paper.FiniteReductionSystemExistence`

## Quarantine, round 2 (2026-10-23T10:20:02Z)

The global build of 0e459b0412 failed in 2 module(s); they and their importers, 2 module(s), were moved to quarantine/ (tools/rework.py, coord/rework.tsv):

- `Sheaf.Paper.AdicPuritySourceFiniteness`: error: Sheaf/Paper/AdicPuritySourceFiniteness.lean: bad import 'Sheaf.Paper.AdicPuritySourceReduction' | changed by the upstream sync (upstream text, keep it; adapt our code): WeilConjectures.Algebrai (nodes lem-pur-adic-source-finiteness-reductions)
- `Sheaf.Paper.LineKummerFieldRealization`: error: Sheaf/Paper/LineKummerFieldRealization.lean: bad import 'Sheaf.AlgebraicGeometry.CartierKummerMap' | changed by the upstream sync (upstream text, keep it; adapt our code): WeilConjectures.Algeb (nodes lem-pur-line-kummer-field-realization)
