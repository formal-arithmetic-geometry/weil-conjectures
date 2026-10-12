# CategoryTheory.localized_restriction_adjunction

## Reason

The parent K-injectivity proof needs the general-site extension-by-zero adjunction, while the existing narrow theorem requires small-site and precoverage hypotheses.

## Old

No declaration existed.

## New

In `Sheaf.Algebra.Homology.LocalizedRestrictionAdjunction`:

```lean
theorem localized_restriction_adjunction
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{max u v}) (U : C)
    (hzero : (SheafOfModules.overFunctor.{max u v} R U).PreservesZeroMorphisms) :
    ∃ (G : SheafOfModules.{max u v} (R.over U) ⥤ SheafOfModules.{max u v} R),
      PreservesFiniteLimits G ∧ PreservesFiniteColimits G ∧
      (SheafOfModules.overFunctor.{max u v} R U).Additive ∧
      Nonempty (G ⊣ SheafOfModules.overFunctor.{max u v} R U)
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.KInjectiveRestrictLocalized | N3 | uses the new adjunction to prove K-injectivity |

## Status

landed 20261012T150954-L-2231334 2026-10-12 (merge of deliver/N3/Sheaf.Algebra.Homology.KInjectiveRestrictLocalized)
