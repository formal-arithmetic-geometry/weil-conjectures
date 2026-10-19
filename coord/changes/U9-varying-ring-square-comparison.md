# AlgebraicGeometry.ProEtale.VaryingRing.moduleSquareG

## Reason

Closing `moduleBetaInvApp_naturality` exposed a kernel conversion timeout while
unfolding the adjoint-compositor square. Both the direct naturality proof and its
abstract categorical specialization reached deterministic kernel timeout (about
58 seconds). Keeping the specified square behind a proved unique-equality
specification makes the same naturality proof compile in 2.8 seconds.

The new `moduleSquareG_existsUnique` is fully proved: its witness is the original
explicit composite, and equality to that composite proves uniqueness. The selected
object is thus completely determined; no arbitrary existence witness or unproved
data is introduced. `moduleSquareG_eq` proves equality to the original construction.

## Old

```lean
noncomputable def moduleSquareG {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    pull R φ i ⋙ pull R φ r ≅ pull R φ p ⋙ pull R φ k :=
  (moduleGComp R φ r i).symm ≪≫ eqToIso (congrArg (pull R φ) h.symm) ≪≫ moduleGComp R φ k p
```

## New

```lean
noncomputable def moduleSquareG {V W S T : Scheme.{u}} (k : V ⟶ W) (r : V ⟶ S)
    (p : W ⟶ T) (i : S ⟶ T) (h : k ≫ p = r ≫ i) :
    pull R φ i ⋙ pull R φ r ≅ pull R φ p ⋙ pull R φ k :=
  (moduleSquareG_existsUnique R φ k r p i h).choose
```

Two fully proved supporting theorems expose the unique specification and its
original equation, with the same scheme maps, rings, and universes. The original
public signatures and visibility are unchanged. No target statement or the meaning
of a definition used by a target changes: the equation is equality of the actual
natural isomorphisms, rather than a weaker comparison.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows --uses
moduleSquareG moduleBetaInvApp` lists the modules below. Only the assigned module
mentions the changed definition. The direct importer is checked unchanged against
the compiled sandbox. All other users are indirect, keep their signatures, and
never unfold or mention this definition. No forced adaptation is included.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting` | K9 | No use of moduleSquareG or moduleBetaInvApp; no adaptation needed. |
| `Sheaf.Paper.CoefficientTowerShriekCalculus` | unclaimed | No use of moduleSquareG or moduleBetaInvApp; no adaptation needed. |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | No use of moduleSquareG or moduleBetaInvApp; no adaptation needed. |
| `Sheaf.Paper.FieldShriekCompositionQcqs` | unclaimed | No use of moduleSquareG or moduleBetaInvApp; no adaptation needed. |
| `Sheaf.Paper.SystemCompactificationProjectionSubstitution` | unclaimed | No use of moduleSquareG or moduleBetaInvApp; no adaptation needed. |
| `Sheaf.Paper.VaryingRingGraphSummand` | unclaimed | No use of moduleSquareG or moduleBetaInvApp; no adaptation needed. |
| `Sheaf.Paper.VerdierExchange` | unclaimed | No use of moduleSquareG or moduleBetaInvApp; no adaptation needed. |
| `Sheaf.Paper.ZlFrobeniusCompactSupportComparison` | unclaimed | No use of moduleSquareG or moduleBetaInvApp; no adaptation needed. |
| `Sheaf.Paper.ZlShriekComposition` | unclaimed | No use of moduleSquareG or moduleBetaInvApp; no adaptation needed. |
| `Sheaf.SixFunctors.IntegralCompactificationSystemRealization` | unclaimed | No use of moduleSquareG or moduleBetaInvApp; no adaptation needed. |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | unclaimed | No use of moduleSquareG or moduleBetaInvApp; no adaptation needed. |
| `Sheaf.SixFunctors.IntegralSystemCanonicalBridge` | unclaimed | No use of moduleSquareG or moduleBetaInvApp; no adaptation needed. |
| `Sheaf.SixFunctors.OpenAdjunctionShift` | unclaimed | No use of moduleSquareG or moduleBetaInvApp; no adaptation needed. |
| `Sheaf.SixFunctors.ProperOpenProjectionMate` | unclaimed | No use of moduleSquareG or moduleBetaInvApp; no adaptation needed. |
| `Sheaf.SixFunctors.SemilinearProperOpenMatePasting` | H1 | No use of moduleSquareG or moduleBetaInvApp; no adaptation needed. |
| `Sheaf.SixFunctors.SynchronizedCanonicalMaps` | unclaimed | No use of moduleSquareG or moduleBetaInvApp; no adaptation needed. |

| `Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows` | U9 | Definition equation API and two proofs; existing signatures unchanged. |

## Status

landed 20261019T034319-L-420255 2026-10-19 (merge of deliver/U9/Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows)
