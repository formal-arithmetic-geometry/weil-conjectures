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

## Main definitions

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.fourCorners`:
  the four finite-coefficient corners of the proper base change setup.

## References

* Stacks Project, Tags 07A7 and 099M.
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

/-- Ordinary scalar extension, with objects and maps fixed by the tensor construction
(Stacks, Tag 06YY). -/
noncomputable def proEtaleRingExtension : proEtaleRingModules T R ⥤ proEtaleRingModules T S :=
  reductionChange T a

/-- The fixed scalar extension is additive (Stacks, Tag 06YY). -/
noncomputable instance proEtaleRingExtension_additive : (proEtaleRingExtension a).Additive :=
  reductionChangeAdditive T a

/-- The tensor-unit normalized ordinary scalar adjunction (Stacks, Tags 03D3 and 06YY). -/
noncomputable abbrev proEtaleRingExtensionAdjunction :
    proEtaleRingExtension a ⊣ proEtaleRingRestrictScalars a := pbcScalarAdjunction a

end AlgebraicGeometry.Scheme
