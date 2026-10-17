# Work queue

7 items; claim with `tools/claim.py next <group> [--stage N]`.

## Stage 1: nodes to split (0)


## Stage 2: nodes to state (0)


## Stage 3: modules to prove (7)

| module | distance to a target | sorry | kind |
|---|---|---|---|
| `WeilConjectures.PoincareDuality.Poincare` | 0 | 1 | repair |
| `WeilConjectures.PoincareDuality.ProjectionFormula` | 2 | 5 | proof |
| `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible` | 2 | 3 | proof |
| `Sheaf.CategoryTheory.DerivedPerfectSmallClassCore` | 7 | 1 | proof |
| `Sheaf.CategoryTheory.DerivedPerfectSmallClassProperties` | 7 | 1 | proof |
| `Sheaf.Paper.IntegralResidueTensorRouteModel` | 11 | 1 | proof |
| `Sheaf.Paper.IntegralResidueTensorPullCounitCore` | 14 | 1 | proof |

## Stage 3: waiting for statements of proof dependencies (4)

Not items: a node in the proof dependencies has no Lean statement yet (the human, 2026-10-17).

| module | distance to a target | sorry | waits for (first unstated node) |
|---|---|---|---|
| `Sheaf.SmoothPurity.NormalizedWitness` | 1 | 1 | `lem-pur-finite-smooth-adjunction-general-base` |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalBounded` | 3 | 1 | `sk-def-sfb-qlbar-condensed` |
| `Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` | 3 | 1 | `sk-def-sfb-dc-setting` |
| `Sheaf.AlgebraicGeometry.EllAdicProperTruncationBound` | 5 | 1 | `det-ambient-ind-derived-sums` |
