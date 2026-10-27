# normalizationDerivedRegularUnit and normalizationDerivedSectionUnit

## Reason

The expanded degree-zero unit composites cause repeated elaboration of the
concrete module and derived-category instances. Use the existing irreducible
`totalUnitComparison` and `sectionTotalUnit` interfaces instead. These are the
same specified maps: unfold those two definitions, apply `Functor.map_comp`
and `Functor.mapIso_trans`, and use the definition of the derived single
functor. Associativity is the only rearrangement. No arbitrary witness is chosen.
Every public signature is preserved, including the entire normalization theorem.
No axiom or hole is added, and no adopted source-library module is modified.

`Sheaf.Paper.SectionTotalOplaxComparisonData` becomes a public import because its
maps now occur in public definition bodies. The new monoidal imports are private
proof imports. The existing proved projection instances from
`Sheaf.Paper.IntegralResidueDerivedMonoidal` are registered only locally to avoid
rebuilding the same concrete category structures during proof elaboration.
Additional local irreducibility attributes prevent expanding chosen comparisons;
they install no attribute or instance for consumers. Private generic category
lemmas handle the diagram cancellations and transport of oplax coherence.
The backward elaboration settings and `synthInstance.maxSize` affect this file only.
The original proof terms retain local `letI` bindings. The source file already
has `linter.all false`; this packet retains it and additionally sets
`linter.mathlibStandardSet false`, since the project enables that set separately.
The proof was checked with the linters enabled during development; the final
file locally suppresses the instance-style, unused-variable, unused-simp and
unused-tactic diagnostics. No kernel checking, axiom check, or 60-second file
limit is disabled or increased, and no file or proof is split for compilation.
Profiling the complete proof with the explicit standard-linter setting gives
77.9 milliseconds of linting (previously about 15--20 seconds); the full file
compiles within the unchanged limit. The final conjugation-component proof uses
an explicitly instantiated generic equation followed by conversion, reducing the
full warning-free compile to 46.3 seconds. Factoring the repeated ordinary
monoidal equality and derived tensor comparison into proved private lemmas
reduces the full compile, including the delivery axiom audit, to 42.0 seconds.
The original inverse construction in `normalizationDerivedInternalMu` is retained
verbatim. Its proof API identifies the mate and canonical tensor maps using the
existing ordinary monoidal equality, then transports inverses along that equality.
Thus the final packet changes exactly the two unit construction bodies above;
no separate inverse definition repair is included.

## Old

```lean
def normalizationDerivedRegularUnit (T : Scheme.{u}) :
    tensorUnit Λ T ≅ (DerivedCategory.singleFunctor (modules Λ T) 0).obj
      (𝟙_ (modules Λ T)) :=
  sectionLocalizationComparison Λ T
      ((HomologicalComplex.single (internalModules Λ T) (.up ℤ) 0).obj
        (𝟙_ (internalModules Λ T))) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (equivalence Λ T).functor (.up ℤ) 0).app (𝟙_ (internalModules Λ T))) ≪≫
    (DerivedCategory.singleFunctor (modules Λ T) 0).mapIso (ordinaryUnitComparison Λ T)

def normalizationDerivedSectionUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPullback Λ f).obj (tensorUnit Λ Y) ⟶ tensorUnit Λ X :=
  (derivedPullback Λ f).map (normalizationDerivedRegularUnit Λ Y).hom ≫
    (pullback Λ f).mapDerivedCategoryFactors.hom.app
      ((HomologicalComplex.single (modules Λ Y) (.up ℤ) 0).obj (𝟙_ (modules Λ Y))) ≫
    DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex
        (pullback Λ f) (.up ℤ) 0).hom.app (𝟙_ (modules Λ Y))) ≫
    (DerivedCategory.singleFunctor (modules Λ X) 0).map (normalizationSectionUnit Λ f) ≫
    (normalizationDerivedRegularUnit Λ X).inv
```

## New

```lean
def normalizationDerivedRegularUnit (T : Scheme.{u}) :
    tensorUnit Λ T ≅ (DerivedCategory.singleFunctor (modules Λ T) 0).obj
      (𝟙_ (modules Λ T)) :=
  sectionLocalizationComparison Λ T (𝟙_ (CochainComplex (internalModules Λ T) ℤ)) ≪≫
    DerivedCategory.Q.mapIso (totalUnitComparison Λ T)

def normalizationDerivedSectionUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedPullback Λ f).obj (tensorUnit Λ Y) ⟶ tensorUnit Λ X :=
  (derivedPullback Λ f).map (normalizationDerivedRegularUnit Λ Y).hom ≫
    (pullback Λ f).mapDerivedCategoryFactors.hom.app
      (𝟙_ (CochainComplex (modules Λ Y) ℤ)) ≫
    DerivedCategory.Q.map (sectionTotalUnit Λ f) ≫
    (normalizationDerivedRegularUnit Λ X).inv
```

The scratch verification `UnitFormulaChecks.lean` compiled in 29.0 seconds with
no warning: it states each new definition equal to its old body verbatim.
The regular-unit equality is proved by unfolding `normalizationDerivedRegularUnit`
and `totalUnitComparison`, then `simp only [Functor.mapIso_trans]` and `rfl`.
The section-unit equality is proved by unfolding `normalizationDerivedSectionUnit`
and `sectionTotalUnit`, rewriting `Functor.map_comp`, simplifying only
`Category.assoc`, and `rfl`. This verification adds no delivered declaration.

## Users

`tools/downstream.py Sheaf.Paper.SectionDerivedTensorNormalization --uses
normalizationDerivedRegularUnit normalizationDerivedSectionUnit` finds 28
transitive module consumers, and finds textual uses of either changed definition
only in the assigned module. All downstream public statements are preserved.
The theorem still compares the same specified unit morphisms: the compact bodies
are equal to the old composites by functoriality, not new choices of units.
The independent statement review can verify this equality when checking target
meaning; no target binder, universe, hypothesis or conclusion changes.
No forced adaptation is necessary. Current checkout claim holders are listed below.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.SectionDerivedTensorNormalization` | Y7 | Assigned proof completed; equivalent compact unit formulas. |
| `Sheaf.Paper.AlgClTopologyMateHomBijection` | unclaimed | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.BoundedFlatTensorContinuity` | B2 | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.CoefficientProjectionSquare` | N1 | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.CoefficientPushFilteredLegs` | C5 | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.CoefficientScalarTensorRealization` | D7 | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.CondensedOpenExceptionalProjectionFormula` | unclaimed | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.ConstructibleAlgClTopologyComparison` | unclaimed | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.FiniteStageSupportedGeneration` | unclaimed | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.FlatCoefficientSquareNormalization` | R9 | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.IntegralQuotientProjectionComparison` | K9 | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.InternalScalarMateProjection` | J3 | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.InternalScalarMateTransitivity` | J4 | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.InternalScalarProjectionMate` | K1 | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.InternalScalarPullbackNormalization` | K2 | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.KummerStratumScalarMateDetection` | unclaimed | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.ModuleRingedToposDerivedComparison` | unclaimed | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.QuotientPullbackTensorCoherence` | N3 | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.QuotientSectionTensorNormalization` | N4 | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.RestrictedCoefficientMateProjection` | S7 | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.ScalarChangeDirectImageUnit` | unclaimed | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.ScalarGeometricExchangeRectangle` | J6 | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.SupportedCommonFieldScalarData` | unclaimed | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.SupportedCommonFieldScalarModels` | unclaimed | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.Paper.SupportedFiniteStageTopologyDefect` | unclaimed | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.PoincareDuality.OpenModuleKFlatProjectionModel` | unclaimed | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.SixFunctors.FiniteOpenDirectImageCtf` | unclaimed | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits` | unclaimed | No textual use of changed helpers; meanings preserved; no adaptation. |
| `Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage` | unclaimed | No textual use of changed helpers; meanings preserved; no adaptation. |

The final proof also marks `internalDelta`, `internalDerivedPullback` and
`derivedPullback` locally irreducible after their concrete API proofs have been
established. This keeps the generic coherence application from reopening the
large derived functor implementations. These attributes are local to this file.

## Status

landed 20261024T191829-L-509559 2026-10-24 (merge of deliver/Y7/Sheaf.Paper.SectionDerivedTensorNormalization)
