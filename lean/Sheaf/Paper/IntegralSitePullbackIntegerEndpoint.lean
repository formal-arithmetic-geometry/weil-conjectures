/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TowerClassReduction
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-! # Integer endpoint in the change-of-site pullback square

Source: Stacks Project, Tag 00WX; the integral class construction in
sec-smooth-purity/sk-prop-sp-tower-geometric, classes proof (2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-- Integer endpoint square for the etale-to-pro-etale pullback.

Source: Stacks Project, Tag 00WX, and the integer endpoint part of the
change-of-site construction in the classes proof.
(blueprint: lem-sp-integral-site-pullback-integer-endpoint).

Proof: transpose through the two inverse-image adjunctions and the
constant-sheaf adjunction. The two resulting maps are the same constant-section
map on every base-changed chart, so adjunction injectivity proves the equality.
This endpoint identity is a strict substatement of the conjunction in
`integral_site_pullback_endpoints`.
-/
theorem integral_site_pullback_integer_endpoint {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let κ := comparisonUpperStarCompUpperStarIso AddCommGrpCat.{u + 1} f
    let z := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm
      (Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
    let zEt := ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom
    ((upperStar AddCommGrpCat.{u + 1} f).map (integerComparison Y).inv ≫
        κ.hom.app ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) =
      z ≫ (integerComparison X).inv ≫
        (comparisonUpperStar AddCommGrpCat.{u + 1} X).map zEt) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
