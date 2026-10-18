# AlgebraicGeometry.exists_finite_purelyInseparable_geometricallyReduced_reduction

## Reason

The returned delivery duplicated the theorem
`AlgebraicGeometry.geometricallyReduced_of_schemeTheoreticallyDominant`, which is already
proved in `Sheaf.AlgebraicGeometry.RadicialReducedFlatGenericFibre`. The existing helper was
private, so this repair generalizes it in place by making that declaration public, imports the
module, and uses the existing theorem. This removes the duplicate proof while preserving the
assigned target statement. The common-field helper and its proof are unchanged.

## Old

In `Sheaf.AlgebraicGeometry.RadicialReducedFlatGenericFibre`:

```lean
private theorem geometricallyReduced_of_schemeTheoreticallyDominant
    {k : Type u} [Field k] {W X : Scheme.{u}}
    (h : W ⟶ X) (p : X ⟶ Spec (.of k))
    [IsSchemeTheoreticallyDominant h] [QuasiCompact h]
    (hred : GeometricallyReduced (h ≫ p)) : GeometricallyReduced p := by
  ...
```

The assigned module separately declared a private theorem with the same signature and proof.

## New

In `Sheaf.AlgebraicGeometry.RadicialReducedFlatGenericFibre`:

```lean
theorem geometricallyReduced_of_schemeTheoreticallyDominant
    {k : Type u} [Field k] {W X : Scheme.{u}}
    (h : W ⟶ X) (p : X ⟶ Spec (.of k))
    [IsSchemeTheoreticallyDominant h] [QuasiCompact h]
    (hred : GeometricallyReduced (h ≫ p)) : GeometricallyReduced p := by
  ...
```

`Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction` imports this module and calls
that public declaration; its duplicate private theorem is removed. No target statement or
definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.RadicialReducedFlatGenericFibre | unclaimed | Existing helper visibility is generalized from private to public so another module can reuse the existing proof. |
| Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction | G6 | Imports the existing module and uses its public helper; duplicate private theorem removed. |

## Status

landed 20261018T071153-L-1668242 2026-10-18 (merge of deliver/G6/Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction)
