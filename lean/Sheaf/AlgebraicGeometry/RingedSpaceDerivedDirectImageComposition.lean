/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage

/-!
# Composition of derived direct images of modules on ringed spaces

Source: Stacks Project, Cohomology, Lemma 20.28.2 (Tag 0D5T)
(blueprint: lem-pc-ringed-spaces-derived-direct-image-composition).
-/

@[expose] public section

universe u wX wY wZ

open CategoryTheory

set_option autoImplicit false

namespace AlgebraicGeometry.RingedSpace

/-- Derived direct images compose canonically. The inverse of the comparison is
characterized by compatibility with the right-derived units: its composite with the
unit for `(g ∘ f)_*` is the composite of the units for `g_*` and `f_*`. The underived
identification `(g ∘ f)_* = g_* ∘ f_*` is the identity on sections of inverse-image opens.
This specifies the canonical comparison rather than an arbitrary natural isomorphism.
Source: Stacks Project, Cohomology, Lemma 20.28.2 (Tag 0D5T)
(blueprint: lem-pc-ringed-spaces-derived-direct-image-composition).

Proof: by lem-pc-ringed-spaces-derived-adjoint-general (Tag 079W), derived pullback
is left adjoint to derived direct image for each of `f`, `g`, and `f ≫ g`.
By lem-pc-ringed-spaces-derived-pullback-composition (Tag 0D5S), the composite
`Lg^* ⋙ Lf^*` identifies canonically with `L(g ∘ f)^*`. Transport the adjunction for
the composite morphism across this identification. Then lem-cat-right-adjoint-composition
identifies its right adjoint with `Rf_* ⋙ Rg_*`; invert that identification to obtain
the displayed orientation. The mate construction is compatible with the underived
composition identification, so its inverse satisfies the displayed unit equation.
The right-derived universal property makes this equation characterize the comparison. -/
theorem exists_derivedModuleDirectImageComposition
    {X Y Z : RingedSpace.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z))]
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∃ e : derivedModuleDirectImage f ⋙ derivedModuleDirectImage g ≅
        derivedModuleDirectImage (f ≫ g),
      ∀ K : HomotopyCategory (SheafOfModules.{u} (moduleRings X)) (ComplexShape.up ℤ),
        (moduleDirectImage (f ≫ g)).rightDerivedFunctorUnit.app K ≫
            e.inv.app (DerivedCategory.Qh.obj K) =
          (moduleDirectImage g).rightDerivedFunctorUnit.app
              (((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
            (derivedModuleDirectImage g).map
              ((moduleDirectImage f).rightDerivedFunctorUnit.app K) := by
  sorry

end AlgebraicGeometry.RingedSpace
