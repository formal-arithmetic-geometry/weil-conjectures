# WeilConjectures.integralProjection_reduction_coordinates

## Reason

The proof uses local irreducibility attributes to avoid unfolding the coefficient
constructions while checking the operation-coordinate types. The static interface
scanner flags `attribute` commands even when they are explicitly local. This record
makes their scope reviewable. No existing definition, declaration signature, public
import, instance, simp attribute, or global reducibility attribute changes. The four
new proof imports are private. The heartbeat option is local to this theorem.

The local attributes are exactly:

```lean
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus CompactSupportFiniteProjection.partialTensor
  CompactSupportFiniteProjection.component compactSupportProjectionComponent
  compactSupportProperProjection
```

## Old

The public signature before this delivery:

```lean
theorem integralProjection_reduction_coordinates
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (d : SixFunctorOperationDatum D C E n hn) (m : ℕ) :
    ∃ t : TensorCoordinates d m,
      (∀ (X : SixFunctorSpace D)
        (K K' L : sfIntegralConstructibleCategory C.l E X.obj.left) (a : K ⟶ K'),
        (reduction d m X).map (((d.higher.integralTensor X).map a).app L) ≫
            (t X K' L).hom =
          (t X K L).hom ≫
            ((CompactSupportFiniteProjection.partialTensor (stage d m) X).map
              ((reduction d m X).map a)).app ((torReduction d m X).obj L)) ∧
      (∀ (X : SixFunctorSpace D)
        (K L L' : sfIntegralConstructibleCategory C.l E X.obj.left) (b : L ⟶ L'),
        (reduction d m X).map (((d.higher.integralTensor X).obj K).map b) ≫
            (t X K L').hom =
          (t X K L).hom ≫
            ((CompactSupportFiniteProjection.partialTensor (stage d m) X).obj
              ((reduction d m X).obj K)).map ((torReduction d m X).map b)) ∧
      (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
        [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
        (c : Compactification f.hom.left)
        (K : sfIntegralConstructibleCategory C.l E X.obj.left)
        (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
        (reduction d m Y).map
            (compactSupportProjectionComponent d.higher.integralExchange f c K L) ≫
            (targetIso d m t f c K L).hom =
          (sourceIso d m t f c K L).hom ≫
            CompactSupportFiniteProjection.component (stage d m) f c
              ((reduction d m X).obj K) ((torReduction d m Y).obj L)) ∧
      (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
        (K : sfIntegralConstructibleCategory C.l E X.obj.left)
        (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
        (reduction d m Y).map
            (compactSupportProperProjection d.higher.integralExchange f K L) ≫
            (properTargetIso d m t f K L).hom =
          (properSourceIso d m t f K L).hom ≫
            CompactSupportFiniteProjection.properComponent (stage d m) f
              ((reduction d m X).obj K) ((torReduction d m Y).obj L))
```

## New

The public signature is identical:

```lean
theorem integralProjection_reduction_coordinates
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (d : SixFunctorOperationDatum D C E n hn) (m : ℕ) :
    ∃ t : TensorCoordinates d m,
      (∀ (X : SixFunctorSpace D)
        (K K' L : sfIntegralConstructibleCategory C.l E X.obj.left) (a : K ⟶ K'),
        (reduction d m X).map (((d.higher.integralTensor X).map a).app L) ≫
            (t X K' L).hom =
          (t X K L).hom ≫
            ((CompactSupportFiniteProjection.partialTensor (stage d m) X).map
              ((reduction d m X).map a)).app ((torReduction d m X).obj L)) ∧
      (∀ (X : SixFunctorSpace D)
        (K L L' : sfIntegralConstructibleCategory C.l E X.obj.left) (b : L ⟶ L'),
        (reduction d m X).map (((d.higher.integralTensor X).obj K).map b) ≫
            (t X K L').hom =
          (t X K L).hom ≫
            ((CompactSupportFiniteProjection.partialTensor (stage d m) X).obj
              ((reduction d m X).obj K)).map ((torReduction d m X).map b)) ∧
      (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y)
        [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
        (c : Compactification f.hom.left)
        (K : sfIntegralConstructibleCategory C.l E X.obj.left)
        (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
        (reduction d m Y).map
            (compactSupportProjectionComponent d.higher.integralExchange f c K L) ≫
            (targetIso d m t f c K L).hom =
          (sourceIso d m t f c K L).hom ≫
            CompactSupportFiniteProjection.component (stage d m) f c
              ((reduction d m X).obj K) ((torReduction d m Y).obj L)) ∧
      (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
        (K : sfIntegralConstructibleCategory C.l E X.obj.left)
        (L : sfIntegralConstructibleCategory C.l E Y.obj.left),
        (reduction d m Y).map
            (compactSupportProperProjection d.higher.integralExchange f K L) ≫
            (properTargetIso d m t f K L).hom =
          (properSourceIso d m t f K L).hom ≫
            CompactSupportFiniteProjection.properComponent (stage d m) f
              ((reduction d m X).obj K) ((torReduction d m Y).obj L))
```

Only its proof, private proof imports, private proved helpers, and local elaboration
settings change. The statement continues to use the original public reduction-data
import. The new lower statements and their explicit data live in new modules.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralStageProjectionStructuralIdentities | unclaimed in the mirrored claim records | Public signature and imports are identical; no adaptation. |

This is the sole direct importer of the item. Its unchanged source is checked against
the new item and is not included in the delivery. No target statement or definition
used by a target changes meaning.

## Status

landed 20261026T222604-L-671250 2026-10-26 (merge of deliver/C7/Sheaf.Paper.IntegralProjectionReductionCoordinates)
