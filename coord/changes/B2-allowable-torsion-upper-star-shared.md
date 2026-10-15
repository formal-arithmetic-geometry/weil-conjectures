# AlgebraicGeometry.Etale.allowable_upperStar

## Reason

The landing return rejected a second proof of the existing private `allowable_upperStar`
lemma. The original lemma lives in `BoundedBelowDerivedSmoothBaseChange`, which imports
this item, so importing it here would form a cycle; a private declaration is also
unavailable across modules. Move the existing statement and its proof unchanged into
`Sheaf.AlgebraicGeometry.AllowableTorsionInverseImage` and make it public. Both callers
import this shared module. Remove the duplicate `allowableTorsionSheafProperty_upperStar`
from the item. No definition or target statement changes.

The original bounded-below module is unclaimed (there is no claim for it); it may be
changed freely under the 2026-10-12 forced-adaptations update. This is a requested
merge of a duplicate, not an adaptation of another group's held module. Its only
changes are one proof import and removal of the relocated private lemma. Its existing
call at `allowable_derived_upperStar` is unchanged. All public signatures and existing
visibility remain unchanged there; the relocated private lemma is now a shared public
result. The new shared lemma has node `lem-sbc-allowable-torsion-upper-star`.

`tools/downstream.py Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange
--uses allowable_upperStar` reports no downstream modules and just that original
module as a textual user. Its full file compiles after the relocation.

## Old

In `lean/Sheaf/AlgebraicGeometry/BoundedBelowDerivedSmoothBaseChange.lean`:

```lean
private lemma allowable_upperStar {U V : Scheme.{u}} (f : U ⟶ V) (P : Set ℕ)
    (F : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : allowableTorsionSheafProperty V P F) :
    allowableTorsionSheafProperty U P ((upperStar AddCommGrpCat.{u + 1} f).obj F) := by
  intro Ω _ _ s x
  let j := (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} f s).app F
  obtain ⟨n, hn, hp, hx⟩ := hF Ω (s ≫ f) (j.hom.hom x)
  refine ⟨n, hn, hp, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso j.hom).1
  simpa only [map_nsmul, map_zero] using hx
```

The item contained a second private theorem with exactly this statement under
`allowableTorsionSheafProperty_upperStar`.

## New

In the new shared `lean/Sheaf/AlgebraicGeometry/AllowableTorsionInverseImage.lean`:

```lean
theorem allowable_upperStar {U V : Scheme.{u}} (f : U ⟶ V) (P : Set ℕ)
    (F : Sheaf V.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : allowableTorsionSheafProperty V P F) :
    allowableTorsionSheafProperty U P ((upperStar AddCommGrpCat.{u + 1} f).obj F) := by
  intro Ω _ _ s x
  let j := (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} f s).app F
  obtain ⟨n, hn, hp, hx⟩ := hF Ω (s ≫ f) (j.hom.hom x)
  refine ⟨n, hn, hp, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso j.hom).1
  simpa only [map_nsmul, map_zero] using hx
```

Both callers add `import Sheaf.AlgebraicGeometry.AllowableTorsionInverseImage`.
The old private declaration is removed from the bounded-below caller. The item's
private duplicate is removed and its use becomes `allowable_upperStar f P _ (hpush.1 q)`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange | unclaimed | Removes the private lemma, imports its shared module; sole original use and public signatures unchanged. |
| Sheaf.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange | B2 | Removes the duplicate and imports and uses the shared original theorem. |
| Sheaf.AlgebraicGeometry.AllowableTorsionInverseImage | B2 (new) | Holds the existing theorem and unchanged proof, now public. |

## Status

landed 20261015T174646-L-626596 2026-10-15 (merge of deliver/B2/Sheaf.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange)
