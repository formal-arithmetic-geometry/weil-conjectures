/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.SixFunctors.ProEtale.BaseChange.SmoothBaseChangeComparisons

/-! # Compatibility of canonical derived site comparisons -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The fixed pullback comparisons commute with the fixed square isomorphisms.
Source: blueprint transport proof, step 4; Stacks Project, Tag 0B65.
(blueprint: stage3-proetale-comparison-square)

Proof: the underived comparison is the conjugate of the canonical comparison of
restriction functors. Both restriction composites around the square send a test object
to the same iterated fibre product, and the maps are the canonical projection maps.
Their equality follows by the pullback universal property. Conjugation transports
this equality to pullbacks. Apply the exact functors termwise to complexes; the
composition comparisons for mapDerivedCategory and the canonical identifications
with left derived pullbacks preserve this equality. Restrict the input to D+. -/
theorem comparison_square {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (DerivedCategory.Plus.ι ⋙ D(ν^*(X')[ModuleCat.{u + 1} Λ])).map
        ((Etale.pullbackSquareComparison (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app M) ≫
      (leftDerivedUpperStarComparisonIso g' Λ).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) f).obj M) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g').map
        ((leftDerivedUpperStarComparisonIso f Λ).hom.app M) =
    (leftDerivedUpperStarComparisonIso f' Λ).hom.app
        (D+(Etale.upperStar (ModuleCat.{u + 1} Λ) g).obj M) ≫
      L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) f').map
        ((leftDerivedUpperStarComparisonIso g Λ).hom.app M) ≫
      (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} Λ) sq.toCommSq).hom.app
        ((DerivedCategory.Plus.ι ⋙ D(ν^*(Y)[ModuleCat.{u + 1} Λ])).obj M) := by
  sorry
end AlgebraicGeometry.ProEtale
