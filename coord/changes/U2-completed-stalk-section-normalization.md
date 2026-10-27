# WeilConjectures.CompletedStalk.sectionRestriction_existsUnique

## Reason

The existing module and the proof packet exceeded the 60-second compile limit. The section-normalization predicate required expensive conversion between the carrier of final-object sections after scalar restriction and the raw sheaf evaluation carrier. The equivalent predicate using `HEq` on the two identically typed section values compiled as a whole file in 38.9 seconds. This is an elaboration repair, not a proof of the still-open existence theorem.

The input binder remains `(pointIntegralSections l E D.k).obj M`; restriction of scalars keeps its carrier. The output carrier of the inverse-image sections is definitionally the raw section carrier at `(s, Spec alpha)`. On these equal types, `HEq x y` is equivalent to `x = y`. Thus this changes no hypothesis, conclusion, normalization or unique isomorphism mathematically. The theorem remains a named hole with its original source and proof. The `sectionRestriction` definition still chooses the same isomorphism type, and no public definition body changes. The target statements and definitions retain their mathematical meaning; this equivalent local normalization does not weaken them.

## Old

```lean
theorem sectionRestriction_existsUnique (α : D.k ≃+* D.k) :
    ∃! ρ : pointIntegralSections l E D.k ≅
        AlgebraicGeometry.ProEtale.inverseImageIntegralModules l E (sourceIso D α).hom ⋙
          pointIntegralSections l E D.k,
      ∀ (M : integralTowerModules l E (Spec (.of D.k)))
        (a : (pointIntegralSections l E D.k).obj M),
        ρ.hom.app M a = M.val.map (sourceArrow D α).op a := by
  sorry
```

## New

```lean
theorem sectionRestriction_existsUnique (α : D.k ≃+* D.k) :
    ∃! ρ : pointIntegralSections l E D.k ≅
        AlgebraicGeometry.ProEtale.inverseImageIntegralModules l E (sourceIso D α).hom ⋙
          pointIntegralSections l E D.k,
      ∀ (M : integralTowerModules l E (Spec (.of D.k)))
        (a : (pointIntegralSections l E D.k).obj M),
        HEq ((ρ.hom.app M).hom.toFun a)
          ((M.val.map (sourceArrow D α).op).hom.toFun a) := by
  sorry
```

## Users

The direct declaration search found only the local `sectionRestriction` constructor. The following is the complete transitive module closure reported by `tools/downstream.py ... --uses sectionRestriction_existsUnique`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | No direct use of the existence theorem; the chosen isomorphism and all downstream types are unchanged. No adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicRestrictionBridge | unclaimed | No direct use of the existence theorem; the chosen isomorphism and all downstream types are unchanged. No adaptation. |
| Sheaf.Paper.ClassicalFrontierExistence | unclaimed | No direct use of the existence theorem; the chosen isomorphism and all downstream types are unchanged. No adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierData | unclaimed | No direct use of the existence theorem; the chosen isomorphism and all downstream types are unchanged. No adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | No direct use of the existence theorem; the chosen isomorphism and all downstream types are unchanged. No adaptation. |
| Sheaf.Paper.ClassicalSuccessiveRestrictions | unclaimed | No direct use of the existence theorem; the chosen isomorphism and all downstream types are unchanged. No adaptation. |
| Sheaf.Paper.ClassicalWeilRestrictionExistence | unclaimed | No direct use of the existence theorem; the chosen isomorphism and all downstream types are unchanged. No adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | No direct use of the existence theorem; the chosen isomorphism and all downstream types are unchanged. No adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | No direct use of the existence theorem; the chosen isomorphism and all downstream types are unchanged. No adaptation. |
| Sheaf.Paper.PointPullbackConeLocalization | unclaimed | No direct use of the existence theorem; the chosen isomorphism and all downstream types are unchanged. No adaptation. |
| Sheaf.Paper.PointSectionsCompletionCone | unclaimed | No direct use of the existence theorem; the chosen isomorphism and all downstream types are unchanged. No adaptation. |
| Sheaf.Paper.PointTransportConeComparisonDescent | H4 | No direct use of the existence theorem; the chosen isomorphism and all downstream types are unchanged. No adaptation. |
| Sheaf.Paper.PointTransportResolutionCancellation | unclaimed | No direct use of the existence theorem; the chosen isomorphism and all downstream types are unchanged. No adaptation. |
| Sheaf.TraceFormula.PointConeLiftsChainNaturality | unclaimed | No direct use of the existence theorem; the chosen isomorphism and all downstream types are unchanged. No adaptation. |

## Status

landed 20261025T164438-L-1014529 2026-10-25 (merge of deliver/U2/Sheaf.Paper.CompletedStalkReparametrizationCoherence)
