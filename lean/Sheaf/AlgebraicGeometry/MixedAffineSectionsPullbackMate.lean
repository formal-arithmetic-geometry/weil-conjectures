/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.GlobalHomPullbackComparison
public import Sheaf.AlgebraicGeometry.MixedGlobalExtension
public import Sheaf.AlgebraicGeometry.MixedGlobalSectionsDirectImageIso
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde

/-! # Affine sections transport the pullback adjunction mate

Source: Stacks Project, Tags 08DW(2), 06Z0, 08HY and 0D5T.
(blueprint: lem-sc-mixed-affine-sections-pullback-mate).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w wA
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Affine scalar extension of sections agrees with sheaf pullback, including mates.
No perfectness, flatness, or invertibility of the input morphism is assumed.
Source: Stacks Project, perfect.tex, Tags 06Z0 and 08DW(2); cohomology.tex,
Tags 08HY and 0D5T; duality.tex, Tag 0AA8, identification of the map beta.
(blueprint: lem-sc-mixed-affine-sections-pullback-mate).

Proof: Identify S and T with spectra of their global rings via isoSpec. The affine
quasi-coherent derived equivalence identifies E with a module complex. Resolve it
by a K-flat complex. Termwise tilde and the derived pullback counit identify its
pullback with derived extension of scalars. Derive the underived sections adjunction
using K-injective resolutions. The same tilde/scalar-extension identification
intertwines the adjunction units: both are induced on K-flat representatives by
x mapping to 1 tensor x. Uniqueness of the left adjoint to derived scalar restriction
therefore gives a unique unit-compatible comparison a for mixedGlobalExtension.
For theta, transpose a.hom followed by RGlobalSections(theta) under the fixed scalar
adjunction. Unit compatibility and naturality identify this transpose with derived
sections of the sheaf pullback adjunct of theta, followed by Leray. The right-derived
unit equation for mixedGlobalSectionsDirectImageIso fixes this last identification.
Injectivity of the scalar adjunction equivalence gives the displayed equation for
all L and theta at once. Work separately in the sheaf and module localizations;
localization uniqueness preserves the equations for independent morphism universes.
On an empty affine scheme or for E=0, these constructions give the unique zero map. -/
theorem exists_mixedAffineSectionsPullbackMate
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (R : Type u) [Ring R], HasDerivedCategory.{wA} (ModuleCat.{u} R)]
    {S T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (g : T ⟶ S) (E : schemeDerivedCategory S)
    (hE : schemeDerivedQCohProperty S E) :
    ∃ a : (mixedGlobalExtension g).obj ((schemeDerivedGlobalSections S).obj E) ≅
        (schemeDerivedGlobalSections T).obj ((derivedPullback g).obj E),
      ∀ (L : schemeDerivedCategory T) (theta : (derivedPullback g).obj E ⟶ L),
        ((mixedGlobalExtensionAdjunction g).homEquiv _ _).symm
            ((schemeDerivedGlobalSections S).map
                ((schemeHomPullbackAdjunction g).homEquiv E L theta) ≫
              (mixedGlobalSectionsDirectImageIso g).hom.app L) =
          a.hom ≫ (schemeDerivedGlobalSections T).map theta := by sorry

end AlgebraicGeometry
