/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-! Compatibility of the two presentations of the pro-etale inverse-image map. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-- The inverse-image map defined from the pro-etale adjunction is the adjoint of the
constant direct-image map.

Source: Stacks Project, Tag 00WX; this is the adjunction compatibility used in the
integer endpoint calculation.
(blueprint: lem-sp-integral-site-pullback-integer-endpoint-inverse-image).

Proof: expand `proEtaleConstantInverseImageMap`.  The hom-set equivalence for the
pro-etale inverse-image adjunction sends the counit composite back to its defining
direct-image map by `Adjunction.homEquiv_counit`; the two adjunction presentations
have the same sheaf-pullback construction. -/
theorem integral_site_pullback_integer_endpoint_inverse_image {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm
        (Scheme.proEtaleConstantDirectImageMap f AddCommGrpCat.{u + 1}
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) =
      Scheme.proEtaleConstantInverseImageMap f AddCommGrpCat.{u + 1}
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) := by
  unfold Scheme.proEtaleConstantInverseImageMap
  rw [← Adjunction.homEquiv_counit]
  change _ = ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm _
  rfl

end AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
