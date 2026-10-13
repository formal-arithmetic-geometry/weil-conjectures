# sectionRingVeroneseFractionCanonicalMap

## Reason

Repair #1428 requires the canonical map to be the explicitly descended map
`[n, ξ] ↦ ξ / s^n`, rather than a map defined as the inverse of an equivalence.
The new definition descends `sectionRingVeroneseFractionMap` through the relation
subgroup using its proved kernel equality.

## Old

```lean
noncomputable def sectionRingVeroneseFractionCanonicalMap
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d) →+
      HomogeneousLocalization.Away (sectionRingGrade L) s.val :=
  (sectionRingVeroneseFractionEquiv X L d s).symm.toAddMonoidHom
```

## New

```lean
noncomputable def sectionRingVeroneseFractionCanonicalMap
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d) →+
      HomogeneousLocalization.Away (sectionRingGrade L) s.val :=
  QuotientAddGroup.lift
    (sectionFractionRelations (L.tensorPow d) (𝟙_ X.Modules) (s.val d)).toAddSubgroup
    (sectionRingVeroneseFractionMap X L d s)
    (sectionRingVeroneseFractionMap_kernel X L d s).le
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore
--uses sectionRingVeroneseFractionCanonicalMap` finds only the defining module
as a textual user. The direct importer `SectionRingVeroneseFractions` already
imports `SectionRingVeroneseFractionsFormula` independently, so removing the core's
formula import does not remove any declaration it needs.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore` | K2 | Definition and proof adapted in this delivery; both signatures unchanged. |

The scratch equality check proves by `rfl` that the old and new maps are equal.
Thus downstream statements retain their meaning. Targets using the changed
definition are reopened for the required definition review; this definitional
equality supplies the meaning-preservation check. No forced adaptations.

## Status

landed 20261013T224511-L-1471557 2026-10-13 (merge of deliver/K2/Sheaf.AlgebraicGeometry.SectionRingVeroneseFractionsCore)
