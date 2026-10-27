# ClosedTestKInjectiveSectionModels section and test interfaces

## Reason

The original aliases repeatedly expand module coefficients and nested fibre products. Ordinary definitions, explicit return types and local irreducibility attributes bound those reductions. The module category, test objects and all mathematical maps remain definitionally the same. `closedUnitComplex` retains its original `NatTrans.mapHomologicalComplex` construction, with an explicit return type. The new `evaluationAdditive` instance records additivity previously inferred through the alias.

`closedFibreArrow` directly reuses `ClosedTest.fiberIso`, the same canonical closed-fibre identification. This requires a public import of `ClosedTestUnitEvaluation`. The original `closedUnit` natural-transformation composition is unchanged. Its invertibility proof now proves the evaluated unit and fibre restriction invertible separately, avoiding the kernel timeout from comparing two large composite functions. No target or theorem signature changes. No arbitrary object is chosen and no hole is added.

All thirteen downstream modules are listed below. Their mathematical statements retain the same definitions up to definitional equality; no consumer source is changed. Targets that use these definitions retain their meanings; the independent interface review can verify this using the old/new bodies and the consumer compilation.

## Old

```lean
abbrev evaluation {X : Scheme.{u}} (V : X.ProEt) :=
  Mod.forget (condensedRingObj Λ X) ⋙
    sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      (CategoryTheory.evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj (op V)
```

```lean
abbrev closedMap (A : Type u) [CommRing A] (I : Ideal A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
```

```lean
abbrev liftedTest (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :=
  (Scheme.AffineProEt.toProEt _).obj ((Scheme.AffineProEt.closedSiteLift A I).obj V)
```

```lean
abbrev closedTest (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :=
  (Scheme.AffineProEt.toProEt _).obj V
```

```lean
abbrev testFibre {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.ProEt) :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V
```

```lean
def closedFibreArrow (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    closedTest A I V ⟶ testFibre (closedMap A I) (liftedTest A I V) :=
  MorphismProperty.Over.homMk
    (IsPullback.isoPullback
      ((Scheme.AffineProEt.affine_closed_site_functor_properties A I).the project server.2.2.2 V).2.1).hom
    (IsPullback.isoPullback_hom_snd
      ((Scheme.AffineProEt.affine_closed_site_functor_properties A I).the project server.2.2.2 V).2.1)
```

```lean
def pushModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) (e : DerivedCategory.Q.obj L ≅ K) :=
  (CondensedRing.lowerStar Λ f).rightDerivedFunctorUnitQ L ≫
    (CondensedRing.moduleObjectDerivedPushforward Λ f).map e.hom
```

```lean
def closedUnitComplex (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    (L : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of A))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of A)))) ℤ) :=
  (NatTrans.mapHomologicalComplex (closedUnit Λ A I V) (.up ℤ)).app L
```

## New

```lean
def evaluation {X : Scheme.{u}} (V : X.ProEt) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X) ⥤
      Ab.{u + 1} :=
  Mod.forget (condensedRingObj Λ X) ⋙
    sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1} ⋙
      (CategoryTheory.evaluation X.ProEtᵒᵖ Ab.{u + 1}).obj (op V)
```

```lean
abbrev closedMap (A : Type u) [CommRing A] (I : Ideal A) :
    Spec (.of (A ⧸ I)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
```

```lean
def liftedTest (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :=
  (Scheme.AffineProEt.toProEt _).obj ((Scheme.AffineProEt.closedSiteLift A I).obj V)
```

```lean
def closedTest (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :=
  (Scheme.AffineProEt.toProEt _).obj V
```

```lean
def testFibre {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.ProEt) : X.ProEt :=
  (MorphismProperty.Over.pullback @WeaklyEtale ⊤ f).obj V
```

```lean
def closedFibreArrow (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt) :
    closedTest A I V ⟶ testFibre (closedMap A I) (liftedTest A I V) :=
  (ClosedTest.fiberIso A I V).hom
```

```lean
def pushModel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (L : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ℤ) (e : DerivedCategory.Q.obj L ≅ K) :
    DerivedCategory.Q.obj ((complexes (CondensedRing.lowerStar Λ f)).obj L) ⟶
      (CondensedRing.moduleObjectDerivedPushforward Λ f).obj K :=
  (CondensedRing.lowerStar Λ f).rightDerivedFunctorUnitQ L ≫
    (CondensedRing.moduleObjectDerivedPushforward Λ f).map e.hom
```

```lean
def closedUnitComplex (A : Type u) [CommRing A] (I : Ideal A)
    (V : (Spec (.of (A ⧸ I))).AffineProEt)
    (L : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology (Spec (.of A))) Ab.{u + 1})
      (condensedRingObj Λ (Spec (.of A)))) ℤ) :
    (complexes (evaluation Λ (liftedTest A I V))).obj L ⟶
      (complexes (evaluation Λ (closedTest A I V))).obj
        ((complexes (CondensedRing.upperStar Λ (closedMap A I))).obj L) :=
  (NatTrans.mapHomologicalComplex (closedUnit Λ A I V) (.up ℤ)).app L
```

```lean
instance evaluationAdditive {X : Scheme.{u}} (V : X.ProEt) : (evaluation Λ V).Additive := by
  unfold evaluation
  infer_instance
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ClosedTestChainMateData | unclaimed | Direct importer; statement unchanged; unchanged source compiled against the edited item (reviewer, 2026-10-25). |
| Sheaf.Paper.ClosedTestChainExchangeNormalization | unclaimed | Statement unchanged; unchanged source compiled against the edited item (reviewer, 2026-10-25). |
| Sheaf.Paper.ClosedTestChainUnitNormalization | unclaimed | Statement unchanged; unchanged source compiled against the edited item (reviewer, 2026-10-25). |
| Sheaf.Paper.ClosedTestChainMateRestriction | S7 | Statement unchanged; unchanged source compiled successfully against the edited item. |
| Sheaf.Paper.ClosedTestChainModelMapNaturality | unclaimed | Statement unchanged; unchanged source compiled successfully against the edited item. |
| Sheaf.Paper.ClosedTestModelMapNaturality | unclaimed | Original complex construction retained; unchanged source compiled successfully against the edited item. |
| Sheaf.Paper.ClosedTestScalarComparisonMaps | unclaimed | Statement unchanged; unchanged source compiled successfully against the edited item. |
| Sheaf.Paper.ClosedTestScalarModelCoherence | unclaimed | Statement unchanged; unchanged source compiled successfully against the edited item. |
| Sheaf.Paper.ClosedTestScalarModelDiagrams | unclaimed | Statement unchanged; unchanged source compiled successfully against the edited item. |
| Sheaf.Paper.ClosedTestScalarModelSquares | unclaimed | Statement unchanged; unchanged source compiled successfully against the edited item. |
| Sheaf.Paper.ClosedTestScalarSectionCoherence | unclaimed | Statement unchanged; unchanged source compiled successfully against the edited item. |
| Sheaf.Paper.ClosedTestScalarSectionSquares | unclaimed | Statement unchanged; unchanged source compiled successfully against the edited item. |
| Sheaf.Paper.ClosedTestScalarUniversalCoherence | unclaimed | Statement unchanged; unchanged source compiled successfully against the edited item. |

Consumer validation: all ten originally listed unchanged consumers and the item compiled successfully, without warnings or errors, in launcher result `e348296dd0d53e93e4205fcc`. No consumer adaptation is delivered. The independent reviewer compiled the edited item together with all thirteen unchanged consumers, in import order, without errors (2026-10-25).

## Status

landed 20261025T164311-L-994004 2026-10-25 (merge of deliver/S8/Sheaf.Paper.ClosedTestKInjectiveSectionModels)
