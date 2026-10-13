/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y3
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeOpenChoices

/-! # Naturality of the concrete higher-direct-image resolution section map

Source: Stacks Project, Cohomology, Tags 01E1 and 01E4.
(blueprint: lem-pc-higher-direct-image-resolution-naturality).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The canonical section-class map computed from a specified resolution.
Source: Stacks Project, Cohomology, Lemma 20.7.3, Tag 01E4.
(blueprint: lem-pc-higher-direct-image-resolution-naturality). -/
noncomputable def higherDirectImageResolutionSectionMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) (V : Y.Opens)
    {N : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (I : InjectiveResolution N) :
    ((RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).rightDerived p).obj N ⟶
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p ⋙
        RingedSpace.openModuleSections Y.toRingedSpace V).obj N :=
    let K : CochainComplex Y.Modules ℕ :=
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℕ)).obj I.cocomplex
    let L := ((SheafOfModules.forget Y.ringCatSheaf).mapHomologicalComplex (.up ℕ)).obj K
    let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
      (evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (Opposite.op V)
    (I.isoRightDerivedObj
      (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)) p).hom ≫
      ((L.sc p).mapHomologyIso E).hom ≫
      ((PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map
        (Scheme.Modules.sectionCohomologyTheta K p ≫
          (SheafOfModules.forget Y.ringCatSheaf).map
            (I.isoRightDerivedObj
              (RingedSpace.moduleDirectImage f.toLRSHom.toShHom) p).inv)).app
                (Opposite.op V)

/-- The canonical resolution-section map commutes with coefficient maps.

Source: Stacks Project, Cohomology, Lemma 20.7.3, Tag 01E4.
(blueprint: lem-pc-higher-direct-image-resolution-naturality).

Proof: Lift a to a cochain map g from I to J preserving the augmentations.
The isoRightDerivedObj_hom_naturality formula moves the derived sections map past
the source resolution isomorphism. Exact evaluation preserves homology, and its
mapHomologyIso is natural for g. Theta is adjoint to the homology comparison for
exact sheafification followed by the counit on the complex; naturality of both
mapHomologyIso and the counit, and naturality of the adjunction homEquiv, show that
theta commutes with f_*g. Finally isoRightDerivedObj_inv_naturality moves f_*g past
the inverse target comparison. Compose these three equalities and reassociate to
obtain the displayed square. Different lifts are homotopic and additive functors
preserve homotopies, so all such lifts give the same homology maps. This does not
use the comparison between restriction cohomology and derived open sections, and
requires neither properness nor an affine basis. It applies also for p = 0 and for
an empty inverse-image open. -/
theorem higherDirectImage_resolution_naturality
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) (V : Y.Opens)
    {M N : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (a : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) :
  ((RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).rightDerived p).map a ≫
      higherDirectImageResolutionSectionMap f p V J =
        higherDirectImageResolutionSectionMap f p V I ≫
        ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p ⋙
          RingedSpace.openModuleSections Y.toRingedSpace V).map a := by sorry

end AlgebraicGeometry
