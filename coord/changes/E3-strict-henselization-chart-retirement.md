# AlgebraicGeometry.Scheme.strictHenselization_chart_maximalIdeal

## Reason

Retirement assignment in coord/retire-items.tsv, authorized by the human hand-off in
coord/changes/retire-sheaf-twins-20261020.md. The small-model copy duplicates the official
chart maximal-ideal theorem. Its three consumers retain their existing statements by
transporting the official theorem through smallStrictHenselizationColimitIso.

Importing the official chart theorem exposes its full-affine structural-map helper.
The old Sheaf structural-map wrapper exports a different theorem with the same full name,
strictHenselizationStructuralMap_eq. The first consumer compile failed at its imports with
"environment already contains 'AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_eq'".
The affected import chains therefore use the original upstream small-model structural-map
module directly. SetsPushforwardStalkStrictHenselization uses the unchanged existence
theorem's choose_spec instead of the wrapper helper. The private ind-etale imports in the
two chart-algebra consumers switch to the official twin and its comparison-isomorphism API.
No held module is edited; all five adapted modules were unclaimed at inspection.

## Old

The withdrawn Sheaf declaration had the following signature:

```lean
theorem strictHenselization_chart_maximalIdeal
{S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (R : CommRingCat.{u}) (i : Spec R ⟶ S) [IsOpenImmersion i]
    (xR : Spec (.of Ω) ⟶ Spec R) :
    ∃ (_ : IsLocalRing (strictHenselizationRing (xR ≫ i)))
      (ρ : R ⟶ strictHenselizationRing (xR ≫ i)),
      Spec.map ρ ≫ i = strictHenselizationStructuralMap (xR ≫ i) ∧
      IsLocalRing.maximalIdeal (strictHenselizationRing (xR ≫ i)) =
        (xR (IsLocalRing.closedPoint Ω)).asIdeal.map ρ.hom
```

Its module publicly imported Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap.

## New

The existing official declaration supplies the same mathematical chart assertion in the
full affine-colimit presentation:

```lean
theorem strictHenselization_chart_maximalIdeal
{S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (R : CommRingCat.{u}) (i : Spec R ⟶ S) [IsOpenImmersion i]
    (xR : Spec (.of Ω) ⟶ Spec R) :
    ∃ (_ : IsLocalRing (strictHenselization (xR ≫ i)))
      (ρ : R ⟶ strictHenselization (xR ≫ i)),
      Spec.map ρ ≫ i = strictLocalizationToBase (xR ≫ i) ∧
      IsLocalRing.maximalIdeal (strictHenselization (xR ≫ i)) =
        (xR (IsLocalRing.closedPoint Ω)).asIdeal.map ρ.hom
```

The Sheaf module is withdrawn, and its node names the official module. At each small-model
consumer, a proved private small_toBase lemma identifies Spec of the inverse comparison
followed by strictLocalizationToBase with strictHenselizationStructuralMap. The inverse
coprojection formula for the final-functor colimit isomorphism proves this equation.
IsLocalRing.map_ringEquiv_maximalIdeal and Ideal.map_map transport the maximal ideal.
The two ind-etale calls supply Spec of the same comparison to the official theorem.

In ConstantStrictFibreStalkComparison, SetsPushforwardStalkStrictHenselization, and
StrictHenselizationClosedFiberForward, the public import of
Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap is replaced by
WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap. Existing declarations
in all five adapted files keep their signatures, visibility, attributes and definitions.
No target statement or source-library file changes. Targets need no statement re-review:
only proof transport and removal of duplicate imports are performed.

## Users

The table covers the modules listed by tools/downstream.py with --uses, the transitive
consumers it lists, and all additional adapted modules.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineStrictLocalRingComparison | unclaimed | Import official chart theorem; transport its conclusion via the existing comparison. Signatures unchanged. |
| Sheaf.AlgebraicGeometry.ConstantStrictFibreStalkComparison | unclaimed | Replace structural-map wrapper import by its original upstream module; signatures unchanged. |
| Sheaf.AlgebraicGeometry.FreeCharacteristicRegularBoundary | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |
| Sheaf.AlgebraicGeometry.IntegralFibreSectionLocalLiftAux | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |
| Sheaf.AlgebraicGeometry.LogBlowupNormalization | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |
| Sheaf.AlgebraicGeometry.LogRegularMonoidalIdealContraction | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |
| Sheaf.AlgebraicGeometry.LogRegularMonomialTensor | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |
| Sheaf.AlgebraicGeometry.LogSmoothInvertibleTorsionLogRegular | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |
| Sheaf.AlgebraicGeometry.LogSmoothLogRegular | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |
| Sheaf.AlgebraicGeometry.NormalConstantGenericUnit | unclaimed | Import official chart theorem; transport its conclusion via the existing comparison. Signatures unchanged. |
| Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |
| Sheaf.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization | unclaimed | Replace structural-map wrapper import by its original upstream module; signatures unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal | E3 | Withdrawn; DAG attachment uses the official twin. |
| Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiber | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |
| Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberForward | unclaimed | Import official chart theorem; transport its conclusion via the existing comparison. Signatures unchanged. |
| Sheaf.AlgebraicGeometry.StrictHenselizationClosedImmersionCartesian | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |
| Sheaf.AlgebraicGeometry.StrictHenselizationModuleFibreFactorization | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |
| Sheaf.TraceFormula.DivisorialLogChart | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |
| Sheaf.TraceFormula.KatoTorIndependenceChart | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |
| Sheaf.TraceFormula.LogRegularDesingularization | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |
| Sheaf.TraceFormula.LogRegularDivisorialStructure | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |
| Sheaf.TraceFormula.LogRegularToricRefinement | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |
| Sheaf.TraceFormula.SmoothGeometricStalkAlgebra | unclaimed | Statements and definitions unchanged; transitive consumer of preserved APIs. |

## Status

landed 20261020T164813-L-3967237 2026-10-20 (merge of deliver/E3/Sheaf.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal)
