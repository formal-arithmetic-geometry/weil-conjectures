# Retirement of Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiber

## Reason
The official `WeilConjectures` strict-localization closed-fibre theorem is now available. The
small-model consumers can use the existing canonical comparison theorem, so the duplicate
`Sheaf` module is no longer needed.

## Old
The withdrawn module exported these exact signatures:

```lean
theorem strictHenselizationStructuralMap_closedPoint_eq
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictHenselizationScheme s) :
    (e.hom ≫ strictHenselizationStructuralMap s) (IsLocalRing.closedPoint A) =
      s (IsLocalRing.closedPoint Ω)

theorem strictHenselizationStructuralMap_fiber_eq_closedPoint
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictHenselizationScheme s)
    (x : Spec (.of A)) :
    (e.hom ≫ strictHenselizationStructuralMap s) x = s (IsLocalRing.closedPoint Ω) ↔
      x = IsLocalRing.closedPoint A
```

Its public import was `Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap`; its
private imports were `Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison` and
`Sheaf.Paper.StrictHenselizationFunctoriality`.

## New
The duplicate module is withdrawn. The DAG nodes attach to the official upstream
strict-localization declarations, and the two small-model consumers call
`strictHenselizationStructuralMap_fiber_eq_closedPoint_compat` from
`Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison`.

The canonical small-to-full ring isomorphism and its proved structural-map equation identify
the two presentations. Both remaining small-model callers require only the forward implication,
so neither needs a replacement for the withdrawn backward theorem or equivalence. Their public
imports already provide the small structural-map API. Direct import of the official full-model
equivalence would load a competing `strictHenselizationStructuralMap_eq` declaration; the
existing private comparison bridge avoids that clash.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiber | D5 | withdrawn; both node attachments retained upstream |
| Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization | unclaimed | import comparison module and use its small-model compatibility theorem |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | unclaimed | import comparison module and use its small-model compatibility theorem |
| WeilConjectures.AlgebraicGeometry.CompatibleStrictHenselizationCoreCompletion | unclaimed | unchanged; already uses the official strict-localization theorem |

## Status
landed 20261020T233117-L-894569 2026-10-20 (merge of deliver/D5/Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiber)
