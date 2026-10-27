/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TowerClassReduction
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.WeilSheaf.FieldCoefficientTateTwist

/-! The mate calculation used by the integer endpoint square. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-- The comparison mate for the integer endpoint maps.

Source: Stacks Project, Tag 00WX; this is the adjunction-mate calculation in the
integer endpoint step of the change-of-site construction.
(blueprint: lem-sp-integral-site-pullback-integer-endpoint-mate).

Proof: apply the hom-set adjunctions for the étale and pro-étale inverse images.
The comparison isomorphism is the conjugate of the direct-image comparison, and
`integerComparison` and `upperStarConstantSheafIso` are defined by uniqueness of
left adjoints.  Their defining unit equations reduce both sides to the same
constant-section map. -/
theorem integral_site_pullback_integer_endpoint_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let A := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    let B := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    let AY := (constantSheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    let BX := (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ))
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv A B)
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom ≫
      (Etale.lowerStar AddCommGrpCat.{u + 1} f).map
        ((comparisonAdjunction AddCommGrpCat.{u + 1} X).homEquiv B BX
          (integerComparison X).hom) ≫
      (lowerStarCompComparisonLowerStarIso f AddCommGrpCat.{u + 1}).symm.hom.app BX =
    (comparisonAdjunction AddCommGrpCat.{u + 1} Y).homEquiv A AY
        (integerComparison Y).hom ≫
      (comparisonLowerStar AddCommGrpCat.{u + 1} Y).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv AY BX
          (proEtaleConstantInverseImageMap f AddCommGrpCat.{u + 1}
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) := by
  sorry

end AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
