# WeilConjectures.sfFiniteOpenPresentationRestriction

## Reason

The adjacent restriction equality and its eqToIso are needed to state the new
coefficient-generator theorem. Move the two existing declarations to
Sheaf.Paper.SfFiniteOpenCoefficientGenerators, and publicly import that module
from Sheaf.Paper.SfFiniteOpenPresentation. Their names, signatures, visibility,
proof and definition body stay the same. This avoids a cyclic proof import.
The only other public API change is the addition of the new, finer interfaces.

## Old

```lean
theorem sfFiniteOpenPresentation_restriction_eq (T : Scheme.{u}) (n : ℕ) :
    normalizedDVRModuleRes l E T (Nat.le_succ n) =
      sfCompactSupportFiniteRestriction l E T n := by
  unfold normalizedDVRModuleRes normalizedDVRQuotient integralCoefficientSheafSystem
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

/-- Change only the presentation of the same adjacent restriction functor.
Source: Stacks 03DA (blueprint: lem-sf-finite-open-presentation-coefficients). -/
def sfFiniteOpenPresentationRestriction (T : Scheme.{u}) (n : ℕ) :
    normalizedDVRModuleRes l E T (Nat.le_succ n) ≅
      sfCompactSupportFiniteRestriction l E T n :=
  eqToIso (sfFiniteOpenPresentation_restriction_eq l E T n)
```

Both declarations were in Sheaf.Paper.SfFiniteOpenPresentation.

## New

```lean
theorem sfFiniteOpenPresentation_restriction_eq (T : Scheme.{u}) (n : ℕ) :
    normalizedDVRModuleRes l E T (Nat.le_succ n) =
      sfCompactSupportFiniteRestriction l E T n := by
  unfold normalizedDVRModuleRes normalizedDVRQuotient integralCoefficientSheafSystem
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

/-- Change only the presentation of the same adjacent restriction functor.
Source: Stacks 03DA (blueprint: lem-sf-finite-open-presentation-coefficients). -/
def sfFiniteOpenPresentationRestriction (T : Scheme.{u}) (n : ℕ) :
    normalizedDVRModuleRes l E T (Nat.le_succ n) ≅
      sfCompactSupportFiniteRestriction l E T n :=
  eqToIso (sfFiniteOpenPresentation_restriction_eq l E T n)
```

Both declarations are in Sheaf.Paper.SfFiniteOpenCoefficientGenerators and are
publicly re-exported by their former module. All existing public imports remain.
No target statement, existing definition body, binder, instance or attribute changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SfFiniteOpenPresentation | F7 | Same restriction declarations, publicly re-exported; proof assembled from the new smaller obligations. |
| Sheaf.Paper.SfSupportTransitionPresentation | unclaimed in the available claim records | Sole direct importer; same exported constants and statements. Original compiled against the delivery in 44.6 s; the unchanged temporary copy was removed. |

The declaration-use scans list only SfFiniteOpenPresentation as an actual user
of either moved constant. The full import graph has 2167 transitive descendants;
the relocation changes neither constant's type or body, so their meanings and
all downstream theorem statements are preserved. No descendant is adapted.

## Status

landed 20261027T021322-L-2756951 2026-10-27 (merge of deliver/F7/Sheaf.Paper.SfFiniteOpenPresentation)
