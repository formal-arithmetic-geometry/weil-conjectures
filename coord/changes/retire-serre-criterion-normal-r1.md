# Ring.serreCriterionNormal

## Reason

The human-approved retirement inventory lists this duplicate for replacement by
`WeilConjectures.RingTheory.SerreCriterionNormal`. Its theorem has exactly the same
type under the canonical upstream name. Retaining both copies duplicates a complete
proof and prevents dependent twins from being retired safely.

## Old

In `Sheaf.RingTheory.SerreCriterionNormal`:

```lean
theorem serreCriterionNormal (R : Type u) [CommRing R] [IsNoetherianRing R] :
    (∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ↔
    IsSerreR R 1 ∧ IsSerreS R 2
```

## New

Withdraw the duplicate module and use the existing theorem in
`WeilConjectures.RingTheory.SerreCriterionNormal` directly:

```lean
theorem forall_isIntegrallyClosed_localization_iff_isSerreR_and_isSerreS (R : Type u) [CommRing R]
    [IsNoetherianRing R] :
    (∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ↔
    IsSerreR R 1 ∧ IsSerreS R 2
```

Only the module and theorem name change. Neither theorem statement, proof route,
definition, target statement, nor consumer signature changes. Reattach
`lem-weil-pbc-serre-criterion-normal` to the upstream module and file.

## Users

The current source scan found exactly the three direct consumers below and two
applications of the old theorem name, both in `NormalLocusAssociatedPrime`.
No current claim lock exists for these consumer modules in this checkout.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NormalLocusAssociatedPrime | unclaimed | Replace private import and two proof applications with upstream names; signatures unchanged. |
| Sheaf.RingTheory.CompleteToricBoundaryClassInjectivity | unclaimed | Replace private import only; statement and existing hole unchanged. |
| Sheaf.TraceFormula.CompleteToricKatoRecognition | unclaimed | Replace private import only; statement and existing hole unchanged. |
| Sheaf.AlgebraicGeometry.LogBlowupNormalization | not adapted | Transitive consumer; no use of the removed name, no change needed. |
| Sheaf.AlgebraicGeometry.LogSmoothInvertibleTorsionLogRegular | not adapted | Transitive consumer; no use of the removed name, no change needed. |
| Sheaf.AlgebraicGeometry.LogSmoothLogRegular | not adapted | Transitive consumer; no use of the removed name, no change needed. |
| Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart | not adapted | Transitive consumer; no use of the removed name, no change needed. |
| Sheaf.Paper.NormalLocusOpen | not adapted | Transitive consumer; no use of the removed name, no change needed. |
| Sheaf.TraceFormula.CompleteToricMonomialFactors | not adapted | Transitive consumer; no use of the removed name, no change needed. |
| Sheaf.TraceFormula.LogRegularDesingularization | not adapted | Transitive consumer; no use of the removed name, no change needed. |
| Sheaf.TraceFormula.LogRegularDivisorialStructure | not adapted | Transitive consumer; no use of the removed name, no change needed. |
| Sheaf.TraceFormula.LogRegularToricRefinement | not adapted | Transitive consumer; no use of the removed name, no change needed. |

`tools/downstream.py --uses Ring.serreCriterionNormal` lists these twelve downstream
modules. Its name-use check finds only the two applications in
`NormalLocusAssociatedPrime` and the duplicate's own declaration.

The retirement inventory's former consumers
`Sheaf.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight`,
`Sheaf.RingTheory.NormalOfFlatNormalFibers`, and `Sheaf.RingTheory.RegularRingNormal`
are already absent. Their upstream counterparts already import the upstream
criterion and need no adaptation. No upstream module is edited.

## Status

landed 20261020T132033-L-1405115 2026-10-20 (merge of deliver/R1/Sheaf.RingTheory.SerreCriterionNormal)
