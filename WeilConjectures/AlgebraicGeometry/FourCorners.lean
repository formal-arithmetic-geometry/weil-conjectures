/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition

/-!
# The four finite-coefficient corners

Source: blueprint, proper base change, four corners; Stacks Project Tags 07A7 and 099M
(blueprint: def-weil-pbc-four-corners).

## Main definitions

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourCorners`:
  the recorded construction or statement of this node.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme

attribute [instance] proEtaleRingRestrictScalars_preservesFiniteLimits
  proEtaleRingRestrictScalars_preservesFiniteColimits

variable {T : Scheme.{u}} {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S)

/-- Ordinary scalar extension, with objects and maps fixed by the tensor construction.
Source: Stacks Tag 06YY (blueprint: def-weil-pbc-four-corners). -/
noncomputable def proEtaleRingExtension : proEtaleRingModules T R ⥤ proEtaleRingModules T S :=
  reductionChange T a

/-- Reuse the published tensor-unit normalized ordinary scalar adjunction.
Source: Stacks 03D3, 06YY (blueprint: def-weil-pbc-four-corners). -/
noncomputable abbrev proEtaleRingExtensionAdjunction :
    proEtaleRingExtension a ⊣ proEtaleRingRestrictScalars a := pbcScalarAdjunction a

variable {U V : Scheme.{u}} (f : U ⟶ V)
  (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
  (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
  (aV : RV ⟶ SV) (aU : RU ⟶ SU)
  (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
  (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SV ≅ SU)
  (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aV ≫ cS.hom)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

attribute [instance] AdicCoefficientDatum.ringTower_finite

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

end AlgebraicGeometry.Scheme
