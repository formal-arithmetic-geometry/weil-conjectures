# AlgebraicGeometry.ProEtale.DiagonalTrace.IsDiagonalLimit

## Reason

The kernel took about 41 seconds just to eliminate the expanded existential
presentation, and 66 seconds with the root comparison. Name its existing finite
Cartier clause by `FiniteCartierNormalization` to share that large predicate.
The module is unclaimed in the current server records. Its two existing
`backward.isDefEq.respectTransparency` options are enabled rather than disabled. This is a definitionally
equal refactor: unfolding `FiniteCartierNormalization`, `FiniteRootNormalization`
and `finiteCartierClass` gives the old clause, with the same sign, exponents,
source and target maps. No binder, datum or hypothesis is added or removed.
The target meanings are unchanged; the independent review can compare that
explicit unfolding. No source-library module is modified.

## Old

```lean
def IsDiagonalLimit (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (δ : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y) : Prop :=
  ∃ (H : DiagonalSystems ℓ (diagonalSurface Y))
    (roots : H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (c : Ext (D.ordinary.E.obj (diagonalIntegralSource Y)) H 2),
    a.hom = diagonalDerivedSingleCounit ℓ
      (diagonalScalarExtension ℓ (diagonalSurface Y)) D (diagonalIntegralSource Y) ∧
    c.hom = a.inv ≫ D.T.map (diagonalIntegralBoundary Y).hom ≫ b.hom ∧
    diagonalFiniteCycleNormalization
      (A := DiagonalMod ℓ (diagonalSurface Y))
      (D.ordinary.E.obj (diagonalIntegralSource Y)) H c
      (fun n ↦ (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
        ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))
          (diagonalImmersion Y)).obj
            (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y))))
      (fun n ↦ (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
        (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
          (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)))
      (fun n s ↦ DiagonalSourceNormalization ℓ Y D.ordinary n s)
      (fun n t ↦ HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
        (roots.hom.app (op n) ≫
          cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
            (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)
            (pow_pos (Fact.out : ℓ.Prime).pos _) (diagonalSurface_power_unit ℓ Y hY n)))
      (fun n ↦ diagonalExactFunctorExtImage (diagonalFiniteToPadic ℓ n (diagonalSurface Y))
        (cartierResidueReducedPro ℓ (Fact.out : ℓ.Prime) (n + 1)
          (diagonalImmersion Y) (diagonalImmersion_cartier Y)
          (diagonalSurface_power_unit ℓ Y hY n))) ∧
    ∃ (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
      (M : DiagonalCompletedReduction ℓ (diagonalSurface Y))
      (s₀ : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
          (diagonalCompletedSource ℓ Y) ≅
        limit (D.ordinary.E.obj (diagonalIntegralSource Y)))
      (t₀ : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
          (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅ limit H),
      let F := diagonalCompletedRestriction ℓ (diagonalSurface Y)
      let R := F.mapDerivedCategory
      let source := diagonalSingleLimitComparison F L (diagonalCompletedSource ℓ Y)
        _ _ s₀ a
      let target := diagonalShiftedSingleLimitComparison F L
        (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) _ _ t₀ b
      ((∀ n : ℕ,
        diagonalCompletedGenerator ℓ Y ≫ (diagonalForget ℓ (diagonalSurface Y)).map
          (s₀.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n)) =
        (diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
          (diagonalForget ℓ (diagonalSurface Y)).map
            ((D.ordinary.π n).app (diagonalIntegralSource Y))) ∧
      HEq ((diagonalForget ℓ (diagonalSurface Y)).map t₀.hom)
        (diagonalRootLimitComparison ℓ (diagonalSurface Y) H roots).inv ∧
      DiagonalArrowCompatibility ℓ R L.R
        (fun n ↦ M.derived.T ⋙ ((evaluation ℕᵒᵖ
          (DiagonalCompleted ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory)
        (fun n ↦ ((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj
          (op n)).mapDerivedCategory)
        M.unit L.projection (diagonalCompletedDomain ℓ Y) (diagonalCompletedCodomain ℓ Y)
        (D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)))
        (D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
          (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧))
        (D.T.map (diagonalIntegralBoundary Y).hom) source target) ∧
      R.map δ ≫ target = source ≫ L.R.map (D.T.map (diagonalIntegralBoundary Y).hom)
```

## New

```lean
def IsDiagonalLimit (ℓ : ℕ) [Fact ℓ.Prime] (Y : Scheme.{u})
    (hY : IsUnit (ℓ : Γ(Y, ⊤)))
    [HasDerivedCategory.{u + 1} (DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalMod ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalAb (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasDerivedCategory.{u + 1} (ℕᵒᵖ ⥤ DiagonalCompleted ℓ (diagonalSurface Y))]
    [HasExt.{u + 1} (DiagonalSystems ℓ (diagonalSurface Y))]
    (D : DiagonalDerivedReduction ℓ (diagonalScalarExtension ℓ (diagonalSurface Y)))
    (δ : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y) : Prop :=
  ∃ (H : DiagonalSystems ℓ (diagonalSurface Y))
    (roots : H ⋙ diagonalForget ℓ (diagonalSurface Y) ≅
      Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ (Fact.out : ℓ.Prime))
    (a : D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (D.ordinary.E.obj (diagonalIntegralSource Y)))
    (b : D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
      (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧) ≅
      ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧)
    (c : Ext (D.ordinary.E.obj (diagonalIntegralSource Y)) H 2),
    a.hom = diagonalDerivedSingleCounit ℓ
      (diagonalScalarExtension ℓ (diagonalSurface Y)) D (diagonalIntegralSource Y) ∧
    c.hom = a.inv ≫ D.T.map (diagonalIntegralBoundary Y).hom ≫ b.hom ∧
    FiniteCartierNormalization ℓ Y hY D.ordinary H roots c ∧
    ∃ (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
      (M : DiagonalCompletedReduction ℓ (diagonalSurface Y))
      (s₀ : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
          (diagonalCompletedSource ℓ Y) ≅
        limit (D.ordinary.E.obj (diagonalIntegralSource Y)))
      (t₀ : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
          (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅ limit H),
      let F := diagonalCompletedRestriction ℓ (diagonalSurface Y)
      let R := F.mapDerivedCategory
      let source := diagonalSingleLimitComparison F L (diagonalCompletedSource ℓ Y)
        _ _ s₀ a
      let target := diagonalShiftedSingleLimitComparison F L
        (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) _ _ t₀ b
      ((∀ n : ℕ,
        diagonalCompletedGenerator ℓ Y ≫ (diagonalForget ℓ (diagonalSurface Y)).map
          (s₀.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n)) =
        (diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
          (diagonalForget ℓ (diagonalSurface Y)).map
            ((D.ordinary.π n).app (diagonalIntegralSource Y))) ∧
      HEq ((diagonalForget ℓ (diagonalSurface Y)).map t₀.hom)
        (diagonalRootLimitComparison ℓ (diagonalSurface Y) H roots).inv ∧
      DiagonalArrowCompatibility ℓ R L.R
        (fun n ↦ M.derived.T ⋙ ((evaluation ℕᵒᵖ
          (DiagonalCompleted ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory)
        (fun n ↦ ((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj
          (op n)).mapDerivedCategory)
        M.unit L.projection (diagonalCompletedDomain ℓ Y) (diagonalCompletedCodomain ℓ Y)
        (D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y)))
        (D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
          (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧))
        (D.T.map (diagonalIntegralBoundary Y).hom) source target) ∧
      R.map δ ≫ target = source ≫ L.R.map (D.T.map (diagonalIntegralBoundary Y).hom)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AffineLineAdjunctionAssembly | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalCoefficientUniformizerReduction | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalCompletedClassPullback | U1 | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalCompletedPullbackCompatibility | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalCyclicCartierProjection | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalCyclicEvaluationTransport | E3 | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalNonTorsionBaseChange | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalTraceFiniteCartierChern | D4 | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalTraceFiniteDivisorAdjoint | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalTraceFiniteIntegralProjection | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalTraceFinitePretraceComponents | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalTraceIntegrationSystems | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalTraceLimitWitnessExistence | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalTraceSupportedSourceExistence | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalUniformizerCartierReduction | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalUniformizerFiniteNormalization | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.RationalP1CompletedLimitBridge | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.RationalP1KernelContractions | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.RationalP1Triangle | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalTraceSources | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalTraceFiniteAdjunctionFactorization | unclaimed | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalTraceFiniteAdjunctionGeometric | C8 | Definitionally identical finite clause; unchanged public signature. |
| Sheaf.Paper.DiagonalTraceFiniteAdjunctionSupported | C9 | Definitionally identical finite clause; unchanged public signature. |

## Status

landed 20261027T233852-L-4126810 2026-10-27 (merge of deliver/D4/Sheaf.Paper.DiagonalTraceFiniteCartierChern)
