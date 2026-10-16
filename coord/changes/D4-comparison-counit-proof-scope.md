# AlgebraicGeometry.ProEtale.comparison_counit

## Reason

The static interface checker treats the extra generic section variables, local
instance registrations and elaboration options used by the private proof helpers
as changed commands. This record documents those proof-scope additions. No
existing definition, theorem signature, visibility or public import changes.

The generic section ends before the existing namespace. Its instance registrations
are explicitly local. The private helpers are inaccessible to importers. The new
import is proof-only. Elaboration options affect checking this file, not the
meaning of the theorem or downstream declarations.

## Old

The existing public signature was:

```lean
theorem comparison_counit {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarComparisonIso f Λ).hom.app
        (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).map
        ((rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ)).hom.app K) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app
        ((DerivedCategory.Plus.ι ⋙ D(ν^*(U)[ModuleCat.{u + 1} Λ])).obj K) =
    (DerivedCategory.Plus.ι ⋙ D(ν^*(U)[ModuleCat.{u + 1} Λ])).map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app K)
```

The surrounding commands were `universe u`, `open CategoryTheory Limits`,
`open scoped CategoryTheory.Functor`, the namespace declaration, and the coefficient
variable `(Λ : Type (u + 1)) [CommRing Λ]`.

## New

The existing public signature is verbatim:

```lean
theorem comparison_counit {U V : Scheme.{u}} (f : U ⟶ V)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (leftDerivedUpperStarComparisonIso f Λ).hom.app
        (R+(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj K) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f).map
        ((rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} Λ)).hom.app K) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app
        ((DerivedCategory.Plus.ι ⋙ D(ν^*(U)[ModuleCat.{u + 1} Λ])).obj K) =
    (DerivedCategory.Plus.ι ⋙ D(ν^*(U)[ModuleCat.{u + 1} Λ])).map
      ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app K)
```

Added three local-to-this-file elaboration options, a generic section with the
four abelian categories, exact functors and adjunction hypotheses for two private
proved lemmas, and `attribute [local instance] comp_preservesFiniteLimits
comp_preservesFiniteColimits`. The generic section is closed before the existing
namespace. All further additions are private proved lemmas or the proof of the
existing theorem. The source file in this delivery contains the full commands.

## Users

`tools/downstream.py Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonCounit
--uses comparison_counit` lists the two uses below. Both see the identical public
signature and definitions; no adaptation is required. The other 47 transitive
importers do not mention this declaration and receive no changed public API.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonCounit | D4 | Proof completed; signature identical. |
| WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange | unclaimed | Existing applications remain identical; no edit. |

No target statement or definition used by a target changes. No consumer is
adapted and no target meaning is reopened.

## Status

landed 20261016T145217-L-3935343 2026-10-16 (merge of deliver/D4/Sheaf.SixFunctors.ProEtale.BaseChange.ComparisonCounit)
