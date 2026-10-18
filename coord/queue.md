# Work queue

21 items; claim with `tools/claim.py next <group> [--stage N]`.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (0)


## Stage 3: modules to prove (21)

| module | distance to a target | sorry | kind |
|---|---|---|---|
| `WeilConjectures.PoincareDuality.Poincare` | 0 | 1 | disputed |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | 2 | 3 | proof |
| `WeilConjectures.ZetaFunction.TraceFormula` | 2 | 1 | proof |
| `WeilConjectures.WeilSheaf.PoincareDuality` | 3 | 1 | proof |
| `Sheaf.WeilSheaf.AdicFiniteCoefficientBound` | 4 | 1 | proof |
| `Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison` | 4 | 1 | proof |
| `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CohomologicalDimension` | 4 | 1 | proof |
| `Sheaf.WeilSheaf.AffineCurveRangePositive` | 5 | 1 | proof |
| `WeilConjectures.WeilSheaf.CurveEndpoints` | 6 | 4 | proof |
| `Sheaf.AlgebraicGeometry.AdicDenseOpenImmersionFiniteness` | 7 | 1 | proof |
| `Sheaf.AlgebraicGeometry.AdicProjectiveSpaceFiniteness` | 7 | 1 | proof |
| `WeilConjectures.WeilSheaf.DenseOpen` | 7 | 1 | proof |
| `WeilConjectures.WeilSheaf.LowerShriekOperations` | 7 | 3 | proof |
| `Sheaf.RingTheory.FiniteAlgebraExtremallyDisconnected` | 8 | 1 | proof |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | 8 | 1 | proof |
| `WeilConjectures.WeilSheaf.ArtinSchreierDual` | 8 | 1 | proof |
| `WeilConjectures.WeilSheaf.TraceIsomorphism` | 9 | 1 | proof |
| `WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromy` | 10 | 1 | proof |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | 11 | 1 | proof |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | 11 | 1 | proof |
| `WeilConjectures.WeilSheaf.FourierInversion.UpperStar` | 12 | 3 | proof |

## Stage 3: waiting for statements of proof dependencies (15)

Not items: a node in the proof dependencies has no Lean statement yet (the human, 2026-10-17).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.SmoothPurity.NormalizedWitness` | 1 | 1 | `lem-pur-finite-smooth-adjunction-general-base` |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | 3 | 1 | `det-def-sfb-constructible-local-model` |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | 3 | 1 | `det-def-sfb-constructible-local-model` |
| `Sheaf.PoincareDuality.ProperProjectionFormulaBounded` | 3 | 1 | `lem-pd-module-ringed-topos-derived-comparison` |
| `Sheaf.WeilSheaf.CohomologyGeometricConjugacy` | 4 | 1 | `def-weil-frobenius-cohomology-transport` |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | 4 | 2 | `def-wf-fundamental-representation` |
| `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` | 4 | 1 | `thm-sf-ctf-stability` |
| `Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound` | 5 | 1 | `det-ambient-ind-derived-sums` |
| `WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy` | 5 | 7 | `cor-rp-euler-product` |
| `WeilConjectures.DeligneLaumon.AffineLine.LocalDuality` | 6 | 2 | `cor-coef-verdier-weil-equivariance` |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | 7 | 1 | `d-real-cohom` |
| `WeilConjectures.DeligneLaumon.AffineLine.Exactness` | 7 | 1 | `lem-dl-a1-constructible-fibres-exact` |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | 8 | 4 | `def-wf-fundamental-representation` |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | 9 | 4 | `lem-a1-qbar-open-closed-cohomology` |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | 9 | 3 | `prop-weil-operations` |
