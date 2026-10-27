# WeilConjectures.PurityFiniteSetting.finiteReductionSourceTrivialization_power

## Reason

Finite reduction chart independence needs the same specified scalar at both coefficient levels.
The existing `exists_finiteReductionSourceChartScalar` provides an unspecified scalar for each
setting separately and does not assert compatibility between those scalars. An explicit power
formula allows the parent proof to choose one exponent using Mathlib, commute the root powers,
and cancel the common scalar by postcomposing with an isomorphism.

## Old

No declaration named `finiteReductionSourceTrivialization_power` existed. The parent theorem
`finiteReductionSourceChart_independent` had its present signature and proof `by sorry`.

## New

New theorem in `Sheaf.Paper.FiniteSourceChartPowerTransition`:

```lean
theorem finiteReductionSourceTrivialization_power (P : PurityFiniteSetting.{u})
    (d c : ℕ) (ζ ζ' : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hζ' : IsPrimitiveRoot ζ' P.diagonalExponent) (hc : ζ = ζ' ^ c)
    {X Y : Scheme.{u}} [X.Over (Spec (.of P.field.k))]
    (f : X ⟶ Y) (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReductionSourceTrivialization f d ζ' hζ' K).hom =
      c ^ d • (P.finiteReductionSourceTrivialization f d ζ hζ K).hom
```

The ordinary coefficient-line calculation is exposed separately as
`finiteReductionRootTrivialization_inv_power` in `Sheaf.Paper.FiniteRootLinePowerTransition`:

```lean
theorem finiteReductionRootTrivialization_inv_power (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) [T.Over (Spec (.of P.field.k))] (c : ℕ) (ζ ζ' : P.field.k)
    (hζ : IsPrimitiveRoot ζ P.diagonalExponent)
    (hζ' : IsPrimitiveRoot ζ' P.diagonalExponent) (hc : ζ = ζ' ^ c) :
    (P.finiteReductionRootTrivialization T ζ' hζ').inv =
      c • (P.finiteReductionRootTrivialization T ζ hζ).inv
```

The parent imports the source-chart theorem privately for its proof. All existing signatures, public
imports and definitions stay unchanged. The helper constructs no data from existence statements.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteReductionSourceChartIndependence | M4 | Private proof import and proof replacement; signature unchanged. |
| Sheaf.Paper.FiniteSourceChartPowerTransition | new module, M4 | Private proof import of the ordinary coefficient-line theorem. |

The new theorem has no pre-existing consumers. Existing consumers of the parent see its
unchanged public interface; no consumer adaptation or target-statement review is required.

## Status

landed 20261025T143650-L-1073566 2026-10-25 (merge of deliver/M4/Sheaf.Paper.FiniteReductionSourceChartIndependence)
