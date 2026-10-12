/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage

/-!
# Acyclicity of a direct image of a K-injective complex

Source: Stacks Project, Cohomology, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-pc-ringed-space-direct-image-kinjective-acyclic).
-/

@[expose] public section

universe u wY wZ

open CategoryTheory

set_option autoImplicit false

namespace AlgebraicGeometry.RingedSpace

/-- Direct image of a K-injective complex is acyclic for a subsequent direct image.
This asserts invertibility only on these particular complexes; it does not assert
that module direct image preserves K-injectivity.
Source: Stacks Project, Cohomology, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-pc-ringed-space-direct-image-kinjective-acyclic).

Proof: derive the tensor pullbacks by K-flat resolutions. Pullback preserves K-flat
complexes, so successive pullbacks of a K-flat resolution compute the derived
pullback of the composite (Tag 0D5S). The underived composition identification and
its adjoint identify the Hom bijections for these two pullbacks. Apply these
bijections to a K-injective complex I on X: maps into I in the derived category are
homotopy classes of chain maps, so the right-derived unit for f and that for the
composite are invertible there. The compatibility of the derived adjunction with
underived adjunction (Tag 079W) identifies the resulting comparison with the
pasted right-derived units. Thus the composite of the unit for g at f-star I with
Rg-star of the unit for f at I is invertible. The latter factor is invertible,
so the former is invertible by cancellation. This argument is confined to
K-injective representatives and does not assume a direct-image composition
isomorphism on the whole derived category. -/
theorem isIso_moduleDirectImage_unit_on_kInjective
    {X Y Z : RingedSpace.{u}}
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]
    [HasDerivedCategory.{wZ} (SheafOfModules.{u} (moduleRings Z))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ) [I.IsKInjective] :
    IsIso ((moduleDirectImage g).rightDerivedFunctorUnit.app
      (((moduleDirectImage f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by sorry

end AlgebraicGeometry.RingedSpace
