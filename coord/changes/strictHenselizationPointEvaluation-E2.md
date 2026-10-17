# strictHenselizationPointEvaluation

## Reason

Repair the returned definition after synchronization to source e47efb5a5. The
previous term used the inverse of `smallStrictHenselizationColimitIso` in the
wrong domain: the declaration's source is the chosen small coordinate-ring
colimit `strictHenselizationRing`, while the upstream evaluation has source the
affine-neighbourhood colimit `strictHenselization`. Construct the map directly
from the specified small diagram and its concrete geometric-point cocone.

The definition's public signature is unchanged. Downstream modules need no
adaptation: their public interfaces and proofs compile unchanged against this
body repair, so they are not part of this delivery.

This replaces unspecified data with the canonical evaluation specified by the
node and Stacks Tag 04HX. No target statement is edited. Any target whose
statement uses this definition must be reviewed against this concrete body
under AGENTS.md §4 and stages/2-statements.md §4; compilation alone does not
establish that semantic check.

## Old

```lean
noncomputable def strictHenselizationPointEvaluation
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y) : strictHenselizationRing barY →+* Ω := by
  sorry
```

The returned, rejected body was:

```lean
  exact ((smallStrictHenselizationColimitIso barY).inv ≫
    colimit.desc (smallStrictHenselizationDiagram barY)
      (strictHenselizationPointCocone barY)).hom
```

## New

```lean
noncomputable def strictHenselizationPointEvaluation
    {Y : Scheme.{v}} {Ω : Type v} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Y) : strictHenselizationRing barY →+* Ω := by
  exact (colimit.desc (smallStrictHenselizationDiagram barY)
    (strictHenselizationPointCocone barY)).hom
```

This uses the universal property of the actual source colimit and chooses no
arbitrary witness.

## Users

The 13 textual consumers listed by `tools/downstream.py --uses` retain their
signatures. Each is checked unchanged against this definition repair in the scratch
consumer set; no consumer is adapted. The 857 transitive downstream modules use the
same public interface. Only a global build checks that entire closure.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.StrictHenselizationPointEvaluationPointed` | D4 | unchanged; original proof compiles |
| `Sheaf.Paper.StrictHenselizationPointEvaluationComparison` | E3 | unchanged; original proof compiles |
| Sheaf.AlgebraicGeometry.ExchangeStrictLocalCohomology | unclaimed | unchanged; textual use only |
| Sheaf.AlgebraicGeometry.IndEtaleAffineStrictLocalBaseChange | unclaimed | unchanged; textual use only |
| Sheaf.AlgebraicGeometry.LocalAcyclicityAbelianSheaf | unclaimed | unchanged; textual use only |
| Sheaf.AlgebraicGeometry.LocalAcyclicityClosedFibreUnit | unclaimed | unchanged; textual use only |
| Sheaf.AlgebraicGeometry.SpecializationCospecializationArrows | unclaimed | unchanged; textual use only |
| Sheaf.AlgebraicGeometry.StrictBaseClosedPointLocalizations | unclaimed | unchanged; textual use only |
| Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap | unclaimed | unchanged; textual use only |
| Sheaf.AlgebraicGeometry.StrictHenselizationClosedLift | unclaimed | unchanged; textual use only |
| Sheaf.Paper.StrictHenselizationPointEvaluationImage | unclaimed | unchanged; textual use only |
| Sheaf.Paper.StrictHenselizationPointEvaluationProperties | unclaimed | unchanged; textual use only |
| Sheaf.Paper.StrictHenselizationPointedMap | unclaimed | unchanged; textual use only |

## Status

landed 20261017T013733-L-113186 2026-10-17 (merge of deliver/E2/Sheaf.Paper.StrictHenselizationPointEvaluation)
