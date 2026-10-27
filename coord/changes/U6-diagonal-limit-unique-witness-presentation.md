# AlgebraicGeometry.ProEtale.DiagonalTrace.IsDiagonalLimit

## Reason

The assembly's proof was valid but spent 96.2 seconds in kernel checking, exceeding
60 seconds. Rebuilding a large compatibility conjunction after replacing its unique
existential by a fixed witness repeatedly compared the concrete sheaf categories.
Retain the normalization and unique-existence compatibility clause as one grouped
proposition, and separately require the supplied arrow to satisfy its whole-system equation. This allows reuse of the existing
compatibility proof and retains all finite normalizations, endpoint comparisons,
completeness, uniqueness and quotient-unit reduction equations. Reuse the generic
finite-cycle, root-limit and endpoint-comparison expressions already introduced by
the landed `diagonal-generic-comparison-interfaces.md` repair. In particular, the
complete compatibility is now the same `DiagonalArrowCompatibility` application
used in `diagonalCompleteDataAssertion`, rather than its expanded copy.

For each fixed presentation, the old clause is `E δ ∧ ∀ ε, E ε → ε = δ`; the new
clause is `(∃! ε, E ε) ∧ E δ`. The old implies the new with witness δ. Conversely,
if ε₀ is the new clause's unique witness, every ε satisfying E obeys
ε = ε₀ = δ, so the original clause follows. The presentation and every other clause are identical after unfolding the shared
interfaces. `diagonalFiniteCycleNormalization` is the old finite evaluation clause;
`diagonalExactFunctorExtImage` is `Ext.mapExactFunctor`. The specialized
`diagonalRootLimitComparison` is the old `rootLimitComparison` specialization.
The local F, R, source and target are the same completed restriction, its derived
functor and the bodies of `diagonalSourceLimitMap` and `diagonalTargetLimitMap`.
`DiagonalArrowCompatibility` contains exactly the previous iso, completeness,
unique-existence and finite quotient-unit equations. Thus this is a logically equivalent definition, not an assumption about
uniqueness from finite reductions, and not a weakened normalization. The supplied δ
is tied to the whole-system equation; no arbitrary diagonal class is selected.

Existing binders, visibility, docstrings, public imports and the DAG attachment stay
unchanged. No source-library module changes. Targets whose definitions use the
predicate require the usual independent meaning review for a definition change.

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
    (∀ n : ℕ,
      ∃ (s : (D.ordinary.E.obj (diagonalIntegralSource Y)).obj (op n) ≅
          (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
            ((lowerStar (ModuleCat.{u + 1} (diagonalResidue.{u} ℓ n))
              (diagonalImmersion Y)).obj
                (geoCartierConstant (diagonalResidue.{u} ℓ n) (ProjectiveLine Y))))
        (t : H.obj (op n) ≅ (diagonalFiniteToPadic ℓ n (diagonalSurface Y)).obj
          (geoCartierLine (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
            (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y))),
        DiagonalSourceNormalization ℓ Y D.ordinary n s ∧
        HEq ((diagonalForget ℓ (diagonalSurface Y)).map t.hom)
          (roots.hom.app (op n) ≫
            cartierProRootMap (diagonalResidue.{u} ℓ n) (ℓ ^ (n + 1))
              (cartierResidue_cast ℓ (n + 1)) (diagonalSurface Y)
              (pow_pos (Fact.out : ℓ.Prime).pos _) (diagonalSurface_power_unit ℓ Y hY n)) ∧
        (Ext.mk₀ s.inv).comp
          ((c.mapExactFunctor ((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj
            (op n))).comp (Ext.mk₀ t.hom) (add_zero 2)) (zero_add 2) =
          (cartierResidueReducedPro ℓ (Fact.out : ℓ.Prime) (n + 1) (diagonalImmersion Y)
            (diagonalImmersion_cartier Y) (diagonalSurface_power_unit ℓ Y hY n)).mapExactFunctor
               (diagonalFiniteToPadic ℓ n (diagonalSurface Y))) ∧
    ∃ (L : DiagonalRlim (DiagonalMod ℓ (diagonalSurface Y)))
      (M : DiagonalCompletedReduction ℓ (diagonalSurface Y))
      (s₀ : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
          (diagonalCompletedSource ℓ Y) ≅
        limit (D.ordinary.E.obj (diagonalIntegralSource Y)))
      (t₀ : (diagonalCompletedRestriction ℓ (diagonalSurface Y)).obj
          (Scheme.purTwistZlModule (diagonalSurface Y) ℓ) ≅ limit H),
      (∀ n : ℕ,
        diagonalCompletedGenerator ℓ Y ≫ (diagonalForget ℓ (diagonalSurface Y)).map
          (s₀.hom ≫ limit.π (D.ordinary.E.obj (diagonalIntegralSource Y)) (op n)) =
        (diagonalScalarAdjunction ℓ (diagonalSurface Y)).unit.app (diagonalIntegralSource Y) ≫
          (diagonalForget ℓ (diagonalSurface Y)).map
            ((D.ordinary.π n).app (diagonalIntegralSource Y))) ∧
      HEq ((diagonalForget ℓ (diagonalSurface Y)).map t₀.hom)
        (rootLimitComparison (diagonalForget ℓ (diagonalSurface Y)) H
          (Scheme.proEtaleRootsOfUnityTower (diagonalSurface Y) ℓ
            (Fact.out : ℓ.Prime)) roots).inv ∧
      IsIso (diagonalSourceLimitMap ℓ Y D a L s₀) ∧
      IsIso (diagonalTargetLimitMap ℓ Y D H b L t₀) ∧
      (∀ P : DerivedCategory (DiagonalCompleted ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 P) → Subsingleton (P ⟶ diagonalCompletedDomain ℓ Y)) ∧
      (∀ P : DerivedCategory (DiagonalCompleted ℓ (diagonalSurface Y)),
        IsIso (ℓ • 𝟙 P) → Subsingleton (P ⟶ diagonalCompletedCodomain ℓ Y)) ∧
      (((diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map δ ≫
          diagonalTargetLimitMap ℓ Y D H b L t₀ =
          diagonalSourceLimitMap ℓ Y D a L s₀ ≫
            L.R.map (D.T.map (diagonalIntegralBoundary Y).hom)) ∧
        (∀ δ' : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y,
          ((diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map δ' ≫
          diagonalTargetLimitMap ℓ Y D H b L t₀ =
          diagonalSourceLimitMap ℓ Y D a L s₀ ≫
            L.R.map (D.T.map (diagonalIntegralBoundary Y).hom)) → δ' = δ)) ∧
      ∀ (δ : diagonalCompletedDomain ℓ Y ⟶ diagonalCompletedCodomain ℓ Y),
        (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map δ ≫
          diagonalTargetLimitMap ℓ Y D H b L t₀ =
          diagonalSourceLimitMap ℓ Y D a L s₀ ≫
            L.R.map (D.T.map (diagonalIntegralBoundary Y).hom) →
        ∀ n : ℕ,
          ∃ (s : (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj
              ((M.derived.T ⋙ ((evaluation ℕᵒᵖ
                (DiagonalCompleted ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory).obj
                  (diagonalCompletedDomain ℓ Y)) ≅
              (((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj
                (op n)).mapDerivedCategory).obj
                (D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y))))
            (t : (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).obj
              ((M.derived.T ⋙ ((evaluation ℕᵒᵖ
                (DiagonalCompleted ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory).obj
                  (diagonalCompletedCodomain ℓ Y)) ≅
              (((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj
                (op n)).mapDerivedCategory).obj
                (D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
                  (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧))),
            (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map
                ((M.unit n).app (diagonalCompletedDomain ℓ Y)) ≫ s.hom =
              diagonalSourceLimitMap ℓ Y D a L s₀ ≫ (L.projection n).app
                (D.T.obj ((DerivedCategory.singleFunctor _ 0).obj (diagonalIntegralSource Y))) ∧
            (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map
                ((M.unit n).app (diagonalCompletedCodomain ℓ Y)) ≫ t.hom =
              diagonalTargetLimitMap ℓ Y D H b L t₀ ≫ (L.projection n).app
                (D.T.obj (((DerivedCategory.singleFunctor _ 0).obj
                  (diagonalComparisonUnits Y))⟦(1 : ℤ)⟧)) ∧
            (diagonalCompletedUnderlying ℓ (diagonalSurface Y)).map
                ((M.derived.T ⋙ ((evaluation ℕᵒᵖ
                  (DiagonalCompleted ℓ (diagonalSurface Y))).obj (op n)).mapDerivedCategory).map
                    δ) =
              s.hom ≫ (((evaluation ℕᵒᵖ (DiagonalMod ℓ (diagonalSurface Y))).obj
                (op n)).mapDerivedCategory).map (D.T.map (diagonalIntegralBoundary Y).hom) ≫
                  t.inv
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

## Users

Inventory: `tools/downstream.py Sheaf.Paper.DiagonalTowerTraceLimit --uses
IsDiagonalLimit`, together with both direct importers. Existing consumers pass this
predicate as a hypothesis; none destructures its body. Their statements retain exactly
the same meaning by the equivalence above. No consumer proof adaptation is needed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.DiagonalCoefficientUniformizerReduction | unclaimed | Equivalent predicate; unchanged signature and proof. |
| Sheaf.Paper.DiagonalNonTorsionBaseChange | unclaimed | Equivalent predicate; unchanged signature and proof. |
| Sheaf.Paper.DiagonalTowerCoefficients | unclaimed | Equivalent predicate; unchanged signature and proof. |
| Sheaf.Paper.DiagonalTowerTrace | unclaimed | Equivalent predicate; unchanged signature and proof. |
| Sheaf.Paper.DiagonalTowerTraceLimit | unclaimed | Equivalent predicate; unchanged signature and proof. |
| Sheaf.Paper.DiagonalTraceIntegrationSystems | unclaimed | Equivalent predicate; unchanged signature and proof. |
| Sheaf.Paper.RationalP1KernelContractions | unclaimed | Equivalent predicate; unchanged signature and proof. |
| Sheaf.Paper.RationalP1Triangle | unclaimed | Equivalent predicate; unchanged signature and proof. |
| Sheaf.Paper.DiagonalTraceSources | unclaimed | Equivalent predicate; unchanged signature and proof. |
| Sheaf.Paper.AffineLineAdjunctionAssembly | U6 | Packages the existing complete compatibility proof and the unique arrow equation. |

## Status

landed 20261026T071239-L-3905477 2026-10-26 (merge of deliver/U6/Sheaf.Paper.AffineLineAdjunctionAssembly)
