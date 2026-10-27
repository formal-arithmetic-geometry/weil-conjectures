# ordinary normalization map aliases

## Reason

Five ordinary comparison aliases expose very large inferred types when compared with the total-complex maps. Give the same five constructors explicit morphism types and retain reducibility with `@[reducible] def`. The original bodies are unchanged. All existing theorem signatures and proofs, all other definitions and all imports remain verbatim. No hole is introduced. The module was unclaimed when adapted. Five Lean equality probes compare each complete new map with its original constructor using `rfl`; their validation is recorded in the report.

## Old

```lean
/-- The actual composite oplax tensor map: abelian inverse image followed by scalar extension.
Source: Stacks 03EL (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
abbrev normalizationInternalTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) :=
  (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal.δ M N

/-- The inverse of the actual composite oplax tensor map, supplied by its strong structure.
Source: Stacks 03EL (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
abbrev normalizationInternalTensorInv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) :=
  (CondensedRing.monoidal_upperStar Λ f).toLaxMonoidal.μ M N

/-- The actual composite oplax unit, retaining the scalar-extension multiplication map.
Source: Stacks 03EL (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
abbrev normalizationInternalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal.η

/-- The specified ringed-section adjunction mate tensor map.
Source: Stacks 03D7 and 03EL (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
abbrev normalizationSectionTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : modules Λ Y) :=
  (pullOplax Λ f).δ M N

/-- The specified ringed-section adjunction mate unit map.
Source: Stacks 03D7 and 03EL (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
abbrev normalizationSectionUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (pullOplax Λ f).η


```

## New

```lean
/-- The actual composite oplax tensor map: abelian inverse image followed by scalar extension.
Source: Stacks 03EL (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
@[reducible] def normalizationInternalTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) :
    (CondensedRing.upperStar Λ f).obj (M ⊗ N) ⟶
      (CondensedRing.upperStar Λ f).obj M ⊗ (CondensedRing.upperStar Λ f).obj N :=
  (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal.δ M N

/-- The inverse of the actual composite oplax tensor map, supplied by its strong structure.
Source: Stacks 03EL (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
@[reducible] def normalizationInternalTensorInv {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : internalModules Λ Y) :
    (CondensedRing.upperStar Λ f).obj M ⊗ (CondensedRing.upperStar Λ f).obj N ⟶
      (CondensedRing.upperStar Λ f).obj (M ⊗ N) :=
  (CondensedRing.monoidal_upperStar Λ f).toLaxMonoidal.μ M N

/-- The actual composite oplax unit, retaining the scalar-extension multiplication map.
Source: Stacks 03EL (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
@[reducible] def normalizationInternalUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (CondensedRing.upperStar Λ f).obj (𝟙_ (internalModules Λ Y)) ⟶
      𝟙_ (internalModules Λ X) :=
  (CondensedRing.monoidal_upperStar Λ f).toOplaxMonoidal.η

/-- The specified ringed-section adjunction mate tensor map.
Source: Stacks 03D7 and 03EL (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
@[reducible] def normalizationSectionTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : modules Λ Y) :
    (pullback Λ f).obj (M ⊗ N) ⟶ (pullback Λ f).obj M ⊗ (pullback Λ f).obj N :=
  (pullOplax Λ f).δ M N

/-- The specified ringed-section adjunction mate unit map.
Source: Stacks 03D7 and 03EL (blueprint: lem-pd-section-ordinary-oplax-normalization). -/
@[reducible] def normalizationSectionUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback Λ f).obj (𝟙_ (modules Λ Y)) ⟶ 𝟙_ (modules Λ X) :=
  (pullOplax Λ f).η


```

## Users

`tools/downstream.py Sheaf.Paper.SectionOrdinaryOplaxNormalization --names` lists 40 transitive importers. The table includes each one. The modification preserves the complete original data by definitional equality, so every consumer retains its meaning. No held module is adapted. Targets using these definitions are reopened for the independent statement review; the report records the Lean preservation checks.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.SectionOrdinaryOplaxNormalization` | unclaimed | Implementation changed; whole-construction preservation checked separately. |
| `Sheaf.AlgebraicGeometry.FieldScalarProjectionMateCoherence` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.CanonicalCoefficientTensorNormalization` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.CountableNormProjectionCriterion` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.FilteredFlatTensorCohomology` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.FlatScalarGeometricCoherence` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.FlatScalarUnitNormalization` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.IntegralReductionUnderlyingDirectImage` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalCanonicalTensorPullRouteModel` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalOplaxResolvingComponents` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalScalarMateProjection` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalScalarProjectionMate` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalScalarPullRouteModel` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalScalarPullTensorCounit` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalScalarPullbackNormalization` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalScalarRegularPullCounit` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalScalarTensorPullNormalization` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.InternalTensorPullRouteModel` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.ModuleRingedToposDerivedComparison` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.NormalizedScalarRestrictionPush` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.NormalizedScalarSectionFamily` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.RestrictedCoefficientPullbackData` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.ScalarChangeDirectImageUnit` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.ScalarGeometricExchangeRectangle` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionDerivedRepresentativeSquare` | U3 | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionDerivedTensorNormalization` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionOplaxTotalComparison` | D8 | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionResolutionConjugationIdentities` | G6 | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionResolvingOplaxConstraintData` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionResolvingOplaxConstraintDiagrams` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionResolvingOplaxInternalConjugation` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionResolvingOplaxModelEdges` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionResolvingOplaxUnitModels` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionScalarComputationTransport` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionTensorConjugateComputation` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionTensorNormalizationTransport` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionTensorRightComputation` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.Paper.SectionTotalOplaxComparisonData` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.IntegralDirectImageReductionCone` | unclaimed | Same data and statements by definitional equality; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.IntegralDirectImageReductionTower` | unclaimed | Same data and statements by definitional equality; no adaptation. |

## Status

landed 20261026T102357-L-347171 2026-10-26 (merge of deliver/D8/Sheaf.Paper.SectionOplaxTotalComparison)
