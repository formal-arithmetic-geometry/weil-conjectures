# AlgebraicGeometry.Scheme.strictHenselizationPointEvaluation

## Reason

Replace the hollow definition with the specified evaluation ring homomorphism. The compatible cocone is already constructed; its colimit descent, transported by the existing canonical small-colimit comparison, constructs the map without choosing a witness of mere existence. All binders, universes, visibility and result types stay identical. The current compiled strictHenselizationRing is an alias of upstream strictHenselization.

## Old

```lean
noncomputable def strictHenselizationPointEvaluation
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y) : strictHenselizationRing barY →+* Ω := by
  sorry
```

## New

```lean
noncomputable def strictHenselizationPointEvaluation
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y) : strictHenselizationRing barY →+* Ω := by
  exact ((smallStrictHenselizationColimitIso barY).inv ≫
    colimit.desc (smallStrictHenselizationDiagram barY)
      (strictHenselizationPointCocone barY)).hom
```

## Users

The declaration-use inventory was obtained with tools/downstream.py --uses. Every listed user keeps its statement: only the implementation of the previously unspecified canonical map is completed. No consumer adaptation is needed. The target statements stay identical; their semantic review should verify this concrete canonical construction in place of the hollow definition.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.StrictBaseClosedPointLocalizations` | unclaimed | Signature unchanged; canonical evaluation implemented. |
| `Sheaf.AlgebraicGeometry.SpecializationCospecializationArrows` | unclaimed | Signature unchanged; canonical evaluation implemented. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift` | unclaimed | Signature unchanged; canonical evaluation implemented. |
| `Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnit` | unclaimed | Signature unchanged; canonical evaluation implemented. |
| `Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf` | unclaimed | Signature unchanged; canonical evaluation implemented. |
| `Sheaf.AlgebraicGeometry.ExchangeStrictLocalCohomology` | unclaimed | Signature unchanged; canonical evaluation implemented. |
| `Sheaf.AlgebraicGeometry.IndEtaleAffineStrictLocalBaseChange` | unclaimed | Signature unchanged; canonical evaluation implemented. |
| `Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap` | unclaimed | Signature unchanged; canonical evaluation implemented. |
| `Sheaf.Paper.StrictHenselizationPointEvaluationImage` | F1 | Signature unchanged; canonical evaluation implemented. |
| `Sheaf.Paper.StrictHenselizationPointEvaluationComparison` | E3 | Signature unchanged; canonical evaluation implemented. |
| `Sheaf.Paper.StrictHenselizationPointEvaluationProperties` | unclaimed | Signature unchanged; canonical evaluation implemented. |
| `Sheaf.Paper.StrictHenselizationPointEvaluation` | E2 | Signature unchanged; canonical evaluation implemented. |
| `Sheaf.Paper.StrictHenselizationPointedMap` | C3 | Signature unchanged; canonical evaluation implemented. |
| `Sheaf.Paper.StrictHenselizationPointEvaluationPointed` | D4 | Signature unchanged; canonical evaluation implemented. |

## Status

landed 20261016T221606-L-1613499 2026-10-16 (merge of deliver/E2/Sheaf.Paper.StrictHenselizationPointEvaluation)
