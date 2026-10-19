# PurityDiagonalOrientationCompatibility warning option

## Reason

Repair the returned landing failure at `<unattributed:39:1802>`. The source-only
hole scanner reads the `sorry` component of `warn.sorry` as a hole token. Remove
this unnecessary warning suppression so every recorded hole belongs to a named
theorem. No scanner or launcher tool is changed.

## Old

```lean
set_option autoImplicit false
set_option warn.sorry false
```

## New

```lean
set_option autoImplicit false
```

The default warning behavior now applies. All existing declaration signatures,
definition bodies, visibility, public imports, and target meanings are preserved.
The three verified auxiliary proofs are described in report.md.
No node statement or proof route changes; two original named theorem holes remain.

## Users

`python3 tools/downstream.py Sheaf.Paper.PurityDiagonalOrientationCompatibility`
reports the following eighteen downstream modules. None is edited or requires an adaptation:
Lean options are local elaboration settings and are not exported through imports.
The item module is held by R2; the table records the current claim holders.
No consumer file is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PurityDiagonalOrientationCompatibility | R2 | Warning suppression removed; three auxiliary theorems proved. |
| Sheaf.Paper.FiniteSmoothAdjunctionGeneralBase | A4 | Unchanged; no declaration type or value changes. |
| Sheaf.Paper.NoetherianPrimePowerSmoothDuality | unclaimed | Unchanged; no declaration type or value changes. |
| Sheaf.SmoothPurity.NormalizedWitness | unclaimed | Unchanged; no declaration type or value changes. |
| Sheaf.Targets.PoincareUncurry | unclaimed | Unchanged; no declaration type or value changes. |
| Sheaf.Targets.SmoothPurityQbar | unclaimed | Unchanged; no declaration type or value changes. |
| TargetsCheck | unclaimed | Unchanged; no declaration type or value changes. |
| WeilConjectures | unclaimed | Unchanged; no declaration type or value changes. |
| WeilConjectures.PoincareDuality.Poincare | unclaimed | Unchanged; no declaration type or value changes. |
| WeilConjectures.SmoothPurity.Defs | unclaimed | Unchanged; no declaration type or value changes. |
| WeilConjectures.TraceFormula.Slop.Correspondence | unclaimed | Unchanged; no declaration type or value changes. |
| WeilConjectures.TraceFormula.Slop.Dualizing | unclaimed | Unchanged; no declaration type or value changes. |
| WeilConjectures.TraceFormula.Slop.Main | unclaimed | Unchanged; no declaration type or value changes. |
| Sheaf.AlgebraicGeometry.LogSmoothTraitPunctualPurity | unclaimed | Unchanged; no declaration type or value changes. |
| Sheaf.AlgebraicGeometry.MonomialBoundaryPurityCriterion | unclaimed | Unchanged; no declaration type or value changes. |
| Sheaf.AlgebraicGeometry.MonomialTraitPunctualPurity | unclaimed | Unchanged; no declaration type or value changes. |
| Sheaf.AlgebraicGeometry.PrimeFieldPunctualPurity | unclaimed | Unchanged; no declaration type or value changes. |
| Sheaf.AlgebraicGeometry.PunctualPurityTraitTest | unclaimed | Unchanged; no declaration type or value changes. |
| Sheaf.AlgebraicGeometry.SmoothPunctualPurityAscent | unclaimed | Unchanged; no declaration type or value changes. |

## Status

landed 20261019T192823-L-1872162 2026-10-19 (merge of deliver/R2/Sheaf.Paper.PurityDiagonalOrientationCompatibility)
