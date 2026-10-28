# WeilConjectures.AdicQbarRealization.integralScalarReindexing_composition

## Reason

Isolate the scalar-only part of the finite-stage composition calculation. The new
statement concerns arbitrary ambient integral derived modules and the balanced scalar
comparison. It has no common-stage comparison or realization-normalization hypothesis.
The parent retains its exact statement and proves all localization transport,
completion-unit cancellation and realization assembly in Lean.

## Old

No declaration of this scalar-only composition square existed.

## New

```lean
theorem integralScalarReindexing_composition
    (C : FamilyCore l D) (T U V : GeometricSpace D)
    (g : T.base.left ≅ U.base.left) (h : U.base.left ≅ V.base.left)
    (h_sections : ∀ (M : modules l V.base.left (C.data V).realization)
      (W : T.base.left.ProEtᵒᵖ)
      (x : ((modulePull l T.base.left (g ≪≫ h).hom
        (C.ring T V (g ≪≫ h))).obj M).val.obj W),
      HEq (((C.moduleComp T U V g h).hom.app M).val.app W x) x)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K : DerivedCategory (integralTowerModules l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) V.base.left)) :
    (C.integral T V (g ≪≫ h) E).derived.inv.app K ≫
      (Functor.mapDerivedCategoryNatIso (C.moduleComp T U V g h) ≪≫
        Functor.mapDerivedCategoryCompIso _ _).hom.app
          ((pbcDerivedExtend (coefficientMap l V.base.left (C.data V).realization E)).obj K) =
    (pbcDerivedExtend (coefficientMap l T.base.left (C.data T).realization E)).map
        ((podCompletedDerivedComp l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E)
          h.hom g.hom).hom.app K) ≫
      (C.integral T U g E).derived.inv.app
        ((podCompletedDerivedInverseImage l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) h.hom).obj K) ≫
      (derivedPull l T.base.left g.hom (C.ring T U g)).map
        ((C.integral U V h E).derived.inv.app K)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicReindexingCompositionCancelledStage | C2 | Private proof import; existing public statement unchanged. |

The new declaration had no previous consumers. Existing direct importers of the item
retain the same public imports and theorem signature; no adaptation is required.

## Status

landed 20261028T034709-L-3533515 2026-10-28 (merge of deliver/C2/Sheaf.Paper.AdicReindexingCompositionCancelledStage)
