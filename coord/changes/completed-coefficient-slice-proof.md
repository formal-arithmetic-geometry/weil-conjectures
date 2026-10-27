# WeilConjectures.completedRingMap_slice

## Reason

Finish the slice-localization proof using the actual pro-etale restriction functors,
with independent scheme and coefficient universes. Private helpers construct the
constant and completion comparisons and the prescribed geometric adjunction mates.
The added private instances provide existing continuity and preservation of
inverse-sequence limits for these proof constructions. They add no assumptions or choices of mathematical data.

The original restriction construction repeatedly unfolds a slice-equivalence composite
while checking the large final statement. Its replacement is direct precomposition
along `Over.map`; `completedRestriction_slice` proves by `rfl` that the old and new
constructions are equal. This changes the representation, not the mathematical
functor or the downstream theorem types.

## Old

The original restriction definition is:

```lean
abbrev completedRingRestriction {W : Scheme.{t}} (U : W.ProEt) :
    Sheaf (ProEt.topology W) CommRingCat.{max u (t + 1)} ⥤
      Sheaf (ProEt.topology U.left) CommRingCat.{max u (t + 1)} :=
  letI : (ProEt.sliceFrom W U).IsDenseSubsite (ProEt.topology U.left)
      ((ProEt.topology W).over U) := ProEt.sliceDense W U
  (ProEt.topology W).overPullback CommRingCat.{max u (t + 1)} U ⋙
    (ProEt.sliceFrom W U).sheafPushforwardContinuous CommRingCat.{max u (t + 1)}
      (ProEt.topology U.left) ((ProEt.topology W).over U)
```

The existing public theorem signature, unchanged by this delivery, is:

```lean
theorem completedRingMap_slice {T W : Scheme.{t}} (g : T ⟶ W) (U : W.ProEt) :
    ∃ (eU : (completedRingRestriction.{t, u} U).obj
          (completedIntegralCommRingSheafUnrestricted l E W) ≅
            completedIntegralCommRingSheafUnrestricted l E U.left)
      (eV : (completedRingRestriction.{t, u} ((proEtaleBaseChange g).obj U)).obj
          (completedIntegralCommRingSheafUnrestricted l E T) ≅
            completedIntegralCommRingSheafUnrestricted l E ((proEtaleBaseChange g).obj U).left)
      (aU : ∀ n : ℕ, (completedRingRestriction.{t, u} U).obj
          (integralCoefficientCommRingSheaf l E W n) ≅
            integralCoefficientCommRingSheaf l E U.left n)
      (aV : ∀ n : ℕ,
        (completedRingRestriction.{t, u} ((proEtaleBaseChange g).obj U)).obj
          (integralCoefficientCommRingSheaf l E T n) ≅
            integralCoefficientCommRingSheaf l E ((proEtaleBaseChange g).obj U).left n)
      (beta : (proEtaleBaseChange g).sheafPushforwardContinuous
          CommRingCat.{max u (t + 1)} (ProEt.topology W) (ProEt.topology T) ⋙
            completedRingRestriction.{t, u} U ≅
        completedRingRestriction.{t, u} ((proEtaleBaseChange g).obj U) ⋙
          (proEtaleBaseChange (completedRingSliceArrow g U)).sheafPushforwardContinuous
            CommRingCat.{max u (t + 1)} (ProEt.topology U.left)
              (ProEt.topology ((proEtaleBaseChange g).obj U).left))
      (lambda : completedRingRestriction.{t, u} U ⋙
          completedRingPull.{t, u} (completedRingSliceArrow g U) ≅
        completedRingPull.{t, u} g ⋙
          completedRingRestriction.{t, u} ((proEtaleBaseChange g).obj U)),
      (∀ (F : Sheaf (ProEt.topology T) CommRingCat.{max u (t + 1)}) (H : U.left.ProEt),
        (beta.hom.app F).hom.app (op H) =
          F.obj.map (completedRingSlicePointIso g U H).hom.op) ∧
      (∀ F : Sheaf (ProEt.topology W) CommRingCat.{max u (t + 1)},
        lambda.hom.app F =
          (completedRingPull.{t, u} (completedRingSliceArrow g U)).map
            ((completedRingRestriction.{t, u} U).map ((completedRingAdj.{t, u} g).unit.app F)) ≫
          (completedRingPull.{t, u} (completedRingSliceArrow g U)).map
            (beta.hom.app ((completedRingPull.{t, u} g).obj F)) ≫
          (completedRingAdj.{t, u} (completedRingSliceArrow g U)).counit.app
            ((completedRingRestriction.{t, u} ((proEtaleBaseChange g).obj U)).obj
              ((completedRingPull.{t, u} g).obj F))) ∧
      (∀ n : ℕ, eU.hom ≫ completedIntegralCommRingProjectionUnrestricted l E U.left n =
        (completedRingRestriction.{t, u} U).map
          (completedIntegralCommRingProjectionUnrestricted l E W n) ≫ (aU n).hom) ∧
      (∀ n : ℕ, eV.hom ≫ completedIntegralCommRingProjectionUnrestricted l E
          ((proEtaleBaseChange g).obj U).left n =
        (completedRingRestriction.{t, u} ((proEtaleBaseChange g).obj U)).map
          (completedIntegralCommRingProjectionUnrestricted l E T n) ≫ (aV n).hom) ∧
      (∀ (n : ℕ) (H : U.left.ProEt),
        (toSheafify (ProEt.topology W) ((Functor.const W.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1}
              (Padic.coefficientExtensionRing l E (n + 1)))))).app
          (op ((MorphismProperty.Over.map ⊤ U.prop).obj H)) ≫
            (aU n).hom.hom.app (op H) =
        (toSheafify (ProEt.topology U.left) ((Functor.const U.left.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))))).app (op H)) ∧
      (∀ (n : ℕ) (H : ((proEtaleBaseChange g).obj U).left.ProEt),
        (toSheafify (ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1}
              (Padic.coefficientExtensionRing l E (n + 1)))))).app
          (op ((MorphismProperty.Over.map ⊤ ((proEtaleBaseChange g).obj U).prop).obj H)) ≫
            (aV n).hom.hom.app (op H) =
        (toSheafify (ProEt.topology ((proEtaleBaseChange g).obj U).left)
          ((Functor.const ((proEtaleBaseChange g).obj U).left.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1}
              (Padic.coefficientExtensionRing l E (n + 1)))))).app (op H)) ∧
      (lambda.hom.app (completedIntegralCommRingSheafUnrestricted l E W) ≫
        (completedRingRestriction.{t, u} ((proEtaleBaseChange g).obj U)).map
          (completedRingMap l E g) ≫ eV.hom =
        (completedRingPull.{t, u} (completedRingSliceArrow g U)).map eU.hom ≫
          completedRingMap l E (completedRingSliceArrow g U)) ∧
      ∀ n : ℕ,
        (lambda.hom.app (completedIntegralCommRingSheafUnrestricted l E W) ≫
          (completedRingRestriction.{t, u} ((proEtaleBaseChange g).obj U)).map
            (completedRingMap l E g) ≫ eV.hom) ≫
              completedIntegralCommRingProjectionUnrestricted l E
                ((proEtaleBaseChange g).obj U).left n =
        (completedRingPull.{t, u} (completedRingSliceArrow g U)).map
          (eU.hom ≫ completedIntegralCommRingProjectionUnrestricted l E U.left n) ≫
            completedRingConstantMap (completedRingSliceArrow g U)
              (CommRingCat.of (ULift.{t + 1}
                (Padic.coefficientExtensionRing l E (n + 1))))
```

Its proof is `by sorry`. There are no private slice-proof constructions between
`completedRingSlicePointIso` and `completedRingMap_slice`.
The private proof import is:

```lean
import Sheaf.Paper.LocalizeRingedSiteMorphismGeneral
```

## New

The new restriction definition is:

```lean
abbrev completedRingRestriction {W : Scheme.{t}} (U : W.ProEt) :
    Sheaf (ProEt.topology W) CommRingCat.{max u (t + 1)} ⥤
      Sheaf (ProEt.topology U.left) CommRingCat.{max u (t + 1)} :=
  letI : (MorphismProperty.Over.map ⊤ U.prop).IsContinuous
      (ProEt.topology U.left) (ProEt.topology W) :=
    ProEt.isContinuous_overMap U.prop
  (MorphismProperty.Over.map ⊤ U.prop).sheafPushforwardContinuous
    CommRingCat.{max u (t + 1)} (ProEt.topology U.left) (ProEt.topology W)
```

The public theorem signature above is retained verbatim; the new proof is in the
attached module. It uses private constructions and quotient-projection calculations.
All other existing definition bodies, declarations and public imports are unchanged.
No new import is needed. The old generic localization import is removed; the
Mathlib mate, sheafification and limit APIs used by the proof are already available
through the preserved public imports.

The new helper names and exact definitions are in the attached module. Every helper
is private; none enters a public signature or a public definition body. Continuity
instances use `ProEt.isContinuous_overMap`, `ProEt.isCocontinuous_overMap` and
`ProEt.isContinuous_overPullback`. Size-shrunk limits and sheafification instances are supplied locally inside proofs.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedCoefficientRingedCoherence | F1 | Completes the slice theorem. |
| Sheaf.Paper.OrdinaryImmersionChartComparison | unclaimed | The same theorem supplies chartRingIso; no adaptation needed. |

`tools/downstream.py --uses completedRingMap_slice` finds the item and the consumer
above. The consumer uses only the unchanged public theorem and definitions.
The final full module compiled cleanly in 25.8 seconds (`full26.log`), including
the `rfl` equality with the original restriction construction. No target statement or definition
used by a target changes meaning. The helper-specific transparency attributes are
scoped before the public theorem. All added definitions and instances are private;
private comparison constructions become irreducible after their proved API lemmas.

## Status

landed 20261024T185119-L-3404873 2026-10-24 (merge of deliver/F1/Sheaf.Paper.CompletedCoefficientRingedCoherence)
