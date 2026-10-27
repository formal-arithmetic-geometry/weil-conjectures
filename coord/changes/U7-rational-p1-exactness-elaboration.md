# AlgebraicGeometry.ProEtale.RationalP1.unitCounit_exact

## Reason

Restore the quarantined module for the active rework assignment. The recorded global
failure is a deterministic heartbeat timeout while elaborating the first
`Functor.IsTriangulated` assertion in `unitCounit_exact`, at archived line 237.
A diagnostic compile reproduced the failure at the unchanged 200000-heartbeat limit:
44.9 seconds overall, with 21 seconds in the failing typeclass inference.

Memoize the two canonical families of additive shift instances inside the existing
triangulated-subcategory binders. These are constructed by `inferInstance` from the
existing Mathlib full-subcategory shift-additivity instance. They are proof-valued
local lets, not additional hypotheses or mathematical choices. Their use only shares
elaboration work; zeta reduction and proof irrelevance preserve the elaborated
proposition. Remove the two settings disabling respect for transparency. No heartbeat
or file-time limit is increased. All definitions, canonical map data, normalizations,
imports, public declarations and five existing theorem holes are preserved.
The final minimal repair compiles cleanly through `lcompile.py` in 11.7 seconds,
with the repaired exactness declaration still at the default heartbeat limit.

## Old

```lean
theorem unitCounit_exact (family : Family l Y) :
    ∃ (hP : (CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (coefficient l c).X
          (ProjectiveLine Y))).IsTriangulated)
      (hY : (CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (coefficient l c).X Y)).IsTriangulated),
      (fun [triP : (CategoryTheory.localizingClosure
          (constantModelBoundedConstructible (coefficient l c).X
            (ProjectiveLine Y))).IsTriangulated]
          [triY : (CategoryTheory.localizingClosure
          (constantModelBoundedConstructible (coefficient l c).X Y)).IsTriangulated] ↦
        ∃ (sF : (push l c k p hpl Y).CommShift ℤ)
          (sG : (exceptional l c k p hpl Y).CommShift ℤ),
          (fun [commF : (push l c k p hpl Y).CommShift ℤ]
              [commG : (exceptional l c k p hpl Y).CommShift ℤ] ↦
            (push l c k p hpl Y).IsTriangulated ∧
            (exceptional l c k p hpl Y).IsTriangulated ∧
            NatTrans.CommShift (unitCounit l c k p hpl Y family).1 ℤ ∧
            NatTrans.CommShift (unitCounit l c k p hpl Y family).2 ℤ)
            (commF := sF) (commG := sG)) (triP := hP) (triY := hY) := by
  sorry
```

## New

```lean
theorem unitCounit_exact (family : Family l Y) :
    ∃ (hP : (CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (coefficient l c).X
          (ProjectiveLine Y))).IsTriangulated)
      (hY : (CategoryTheory.localizingClosure
        (constantModelBoundedConstructible (coefficient l c).X Y)).IsTriangulated),
      (fun [triP : (CategoryTheory.localizingClosure
          (constantModelBoundedConstructible (coefficient l c).X
            (ProjectiveLine Y))).IsTriangulated]
          [triY : (CategoryTheory.localizingClosure
          (constantModelBoundedConstructible (coefficient l c).X Y)).IsTriangulated] ↦
        -- Share the additive shift families before elaborating exactness.
        let _ : ∀ n : ℤ,
            (shiftFunctor (rationalLocalizingCategory (coefficient l c).X
              (ProjectiveLine Y)) n).Additive := fun n ↦ inferInstance
        let _ : ∀ n : ℤ,
            (shiftFunctor (rationalLocalizingCategory (coefficient l c).X Y) n).Additive :=
          fun n ↦ inferInstance
        ∃ (sF : (push l c k p hpl Y).CommShift ℤ)
          (sG : (exceptional l c k p hpl Y).CommShift ℤ),
          (fun [commF : (push l c k p hpl Y).CommShift ℤ]
              [commG : (exceptional l c k p hpl Y).CommShift ℤ] ↦
            (push l c k p hpl Y).IsTriangulated ∧
            (exceptional l c k p hpl Y).IsTriangulated ∧
            NatTrans.CommShift (unitCounit l c k p hpl Y family).1 ℤ ∧
            NatTrans.CommShift (unitCounit l c k p hpl Y family).2 ℤ)
            (commF := sF) (commG := sG)) (triP := hP) (triY := hY) := by
  sorry
```

The two local instance families cache canonical proof terms. In particular the
structures for the full subcategories and all shift-commutation assertions are the
same as before. No definition used by a target is changed; no target statement
review is reopened on account of a different mathematical definition.

## Users

`tools/downstream.py Sheaf.Paper.RationalP1UnitCounit --allow-missing --uses
AlgebraicGeometry.ProEtale.RationalP1.unitCounit_exact` finds zero live downstream
modules because the root and its two parents are quarantined. Source search of both
`lean/` and `quarantine/` finds the following two direct importers, neither of which
mentions `unitCounit_exact`. They retain their own rework assignments and are not
withdrawn or adapted by this packet. No additional live importer exists.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RationalP1UnitCounit | U7 (this assignment) | Restore all archived declarations and repair exactness elaboration. |
| Sheaf.Paper.RationalP1KernelContractions | quarantined; no local claim recorded | Existing API restored; no use of changed spelling and no adaptation. |
| Sheaf.Paper.RationalP1Triangle | quarantined; no local claim recorded | Existing API restored; no use of changed spelling and no adaptation. |

## Status

landed 20261025T164511-L-1026715 2026-10-25 (merge of deliver/U7/Sheaf.Paper.RationalP1UnitCounit)
