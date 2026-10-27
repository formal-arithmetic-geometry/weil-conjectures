# CategoryTheory.integerActionTopologyCriterion

## Reason

The assigned twisted-site core needs a sheaf criterion for the integer-action
site. The existing proved slice normalization supplies normalization isomorphisms
and sieve calculations in private helpers. Add a proved public criterion beside
those helpers, so the new construction can reuse them. The module was unclaimed
when checked; no other group's work is adapted.

## Old

No declaration `CategoryTheory.integerActionTopologyCriterion` existed.
All pre-existing declarations, signatures, attributes, definitions and imports
are preserved verbatim.

## New

```lean
theorem integerActionTopologyCriterion
    (J : Precoverage C)
    (hcover : ∀ (n : ℤ) (X : C) (R : Presieve X),
      R ∈ J X ↔ R.map (shiftFunctor C n) ∈ J ((shiftFunctor C n).obj X)) :
    (∀ (X : C) (S : Sieve (IntegerActionSite.mk X : IntegerActionSite C)),
      S ∈ integerActionTopology J (IntegerActionSite.mk X) ↔
        S.functorPullback (integerActionInclusion (C := C)) ∈ J.toGrothendieck X) ∧
    (integerActionInclusion (C := C)).IsContinuous J.toGrothendieck
      (integerActionTopology J) ∧
    (∀ P : (IntegerActionSite C)ᵒᵖ ⥤ Type w,
      Presieve.IsSheaf (integerActionTopology J) P ↔
        Presieve.IsSheaf J.toGrothendieck
          ((integerActionInclusion (C := C)).op ⋙ P))
```

Add this public theorem and one proved private compatibility-preservation lemma.
No global instances or simp attributes change. No sorry is added.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.IntegerActionSliceEquivalence | unclaimed | Add proved API; preserve existing declarations. |
| Sheaf.CategoryTheory.TwistedActionCategory | Z6, new | Reuse existing integer-action category. |
| Sheaf.CategoryTheory.TwistedActionTopology | Z6, new | Apply cover and sheaf criterion. |
| Sheaf.CategoryTheory.TwistedActionSiteCore | Z6 | Package constructed site and coefficient sheaf. |

`tools/downstream.py` and a direct-import search found no existing direct importers
of IntegerActionSliceEquivalence. No existing consumer requires adaptation.
No target statement or existing definition used by a target is modified.

## Status

landed 20261027T103529-L-1103929 2026-10-27 (merge of deliver/Z6/Sheaf.CategoryTheory.TwistedActionSiteCore)
