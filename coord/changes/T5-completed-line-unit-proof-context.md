# CompletedLineTensor unit proof context

## Reason

Prove `ordinaryUnit_existsUnique` from the existing universal cochain-derived model
and chain multiplication isomorphism. Private projection lemmas identify the model's
functor, complex and counit with the public wrappers, and a generic localization
argument constructs the normalized unitor. The good-complex localization proves
uniqueness. All five added private helpers are fully proved.

The concrete localization witnesses are large. File-local instance and reducibility
controls prevent repeated expansion and keep compilation within the fixed limit.
All public signatures and public imports remain unchanged. The source library is
unchanged. No target or downstream statement changes meaning, and no new hole is added.

## Old

`ordinaryUnit_existsUnique` had the same signature and proof `by sorry`.
There was no `DerivedUnitProof` section or its five private helpers. The existing
`comparisonComplex` and `scalarAssociatorComplex` bodies were both:

```lean
  NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)
```

The additivity step of `exact` used `rightExactFunctor_le_additiveFunctor`.
The extra local elaboration commands below were absent, or (for the scalar wrappers
and `sheaf`) occurred later in the file.

## New

The two definitionally equal comparison bodies are, respectively:

```lean
  by
    unfold complex completedOrdinaryScalarComplex
    exact NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)
```

```lean
  by
    unfold completedOrdinaryScalarComplex
    exact Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)
```

Mathlib defines `Functor.mapHomologicalComplexCompIso e c` to be precisely
`NatIso.mapHomologicalComplex e c`. Thus neither definition changes its data.
The additivity step uses `Functor.additive_of_preserves_binary_products T`.
The private `rationalTwist_additive` proof explicitly unfolds `rationalTwist` once
before `infer_instance`, avoiding an expensive inferred-type conversion.

The file disables the imported overlapping sheafification instances
`hasSheafify_proEtTopology`, `PrincipalKoszulStrictReplacement.abSheafify`,
`PrincipalKoszulStrictReplacement.abLocallyBijective`,
`PrincipalKoszulStrictReplacement.siteSmall`, `integralOperationsAbSheafify`,
`integralOperationsAbLocallyBijective`, `integralOperationsSiteSmall`, and
`integralOperationsCommHasDerivedCategory`. These commands match the existing
finite-free comparison module's instance selection. It locally marks
`HasDerivedCategory.standard` irreducible and selects
`integralTowerHasDerivedCategory` at priority 5000.

The existing local irreducibility of `completedScalarChangeData`,
`completedOrdinaryScalarComplex`, and `sheaf` is moved earlier. Explicit unfolding in
the two comparison bodies supplies the corresponding elaboration equations.

Inside `DerivedUnitProof`, `integralOperationsGoodComplex` and (after its projection
lemmas) `completedScalarCochainModel` are locally irreducible. The wrappers
`completedDerivedScalarExtension`, `completedOrdinaryScalarComplex` and
`completedOrdinaryScalarExtension` are locally semireducible there. The section ends
immediately after `ordinaryUnit_existsUnique`, restoring these settings.

Inside `Rational`, `sfIntegralConstructible`, `integralCoefficientLinear`,
`integralScalarConstant`, `sfIntegralCoefficientLinear`, and
`sfIntegralConstructibleLinear` are locally irreducible. `integralTwist` is locally
irreducible after its definition and through `rationalTwist_additive`. Its existing
additive and linear instances receive local priority 5000. Afterwards it and
`sfIntegralConstructible` are restored to semireducible. The remaining attributes
end with the section. These controls bound elaboration of existing declarations;
their signatures and mathematical bodies are otherwise unchanged.

Two proof-only `import all` commands access existing proved private declarations in
`IntegralOperationsWellDefined` and `FiniteFreeCompletedScalarComparison`.
No public definition uses the new private helpers.

## Users

`tools/downstream.py Sheaf.Paper.CompletedLineTensorCoherence --uses ordinaryUnit_existsUnique`
reports 2,347 transitive importers and only `Sheaf.Paper.ScalarCompletionAssociator`
(and the item itself) as textual users of this declaration. Its signature and uniqueness
specification are unchanged, so no adaptation is needed. All 16 current direct importers
are listed below. No module held by another group is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | W2 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.CompactSupportNormalizedScalarDescent | D5 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.FdIntegralInverseScalarCocycle | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.IntegralLineTensorCompleteness | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.MixedReductionUnitComposition | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.PerfectDualPairAndTateStability | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.PurShiftedTateUnitScalarCoherence | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ScalarCompletionAssociator | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.ScalarShiftLineTowerTransport | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.SfStrictDirectImageScalarComparison | Y8 | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.TateTwistLocallyFree | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.UnshiftedLineUnitTower | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.Paper.WfTateTwistCompatibility | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.TraceFormula.CounitRealizationSubstitution | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.TraceFormula.ScalarModelAssociativity | unclaimed | Signature and meaning unchanged; no adaptation. |
| Sheaf.TraceFormula.ScalarModelUnit | unclaimed | Signature and meaning unchanged; no adaptation. |

## Status

landed 20261025T181137-L-4080685 2026-10-25 (merge of deliver/T5/Sheaf.Paper.CompletedLineTensorCoherence)
