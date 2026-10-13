/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedMayerVietorisCanonicalData

/-! # Counit computation for the canonical open composition comparison

Source: Stacks Project, Cohomology, Tags 08FE, 0D5T and 08BV.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

noncomputable section
namespace AlgebraicGeometry

attribute [local instance 2000] schemeMVModuleAbelian

/-- On a K-injective complex on the inverse-image open, restricting the normalized
composition comparison and then applying the base-open counit agrees with first
using the open-restriction comparison and then pushing forward the source-open counit.
The parameter β is fixed by hβ to the canonical composite. Keeping it as an
explicit parameter avoids unfolding its right-derived choice in each projection.
This concerns an arbitrary complex on the open, not a restriction unit on X.

Source: Stacks Project, Tags 08FE (sectionwise restriction/direct-image identity),
0D5T (composition of derived direct images), and 08BV (open adjunction computation).
Proof: Substitute the defining equality hβ. Let jX and jY be the two open
inclusions and g the restricted morphism.
Open direct image jX_* preserves K-injective complexes, since its left adjoint is
exact restriction. Thus I and jX_*I compute the relevant source derived images.
Use the determining right-derived unit equations of both composition comparisons
and jX followed by h = g followed by jY to identify the restricted composition
comparison with the localization of the sectionwise composition identity. Expand
schemeMVOpenRestrictionComparison using the unit factorization equations of its
exact-functor and composition factors. The required equality now reads, on an open
W of U, that the two counit identifications of sections of I over g inverse image W
are equal. Both are the restriction/direct-image identity of Tag 08FE, with the
open-adjunction counits identifying restriction of open direct image with I.
These equalities commute with differentials, so descend through the homotopy and
derived localizations. The factorization equation for the derived counit
(Adjunction.derivedε_fac_app) identifies the localized counits with the displayed
schemeMVAdjunction counits. Cancel the intervening computation isomorphisms.
For U empty both target objects are zero; for U top this is the normalized
composition identity. Neither a cover nor a unit at an object on X is used.
(blueprint: lem-pc-derived-mayer-vietoris-open-composition-counit). -/
theorem schemeMVOpenComposition_counit_Q
    (X Y : Scheme.{u}) (h : X ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ T : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    [∀ T : Y.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toScheme.toRingedSpace))]
    (U : Y.Opens)
    (β : schemeDerivedDirectImage (h ⁻¹ᵁ U).ι ⋙ schemeDerivedDirectImage h ≅
      schemeDerivedDirectImage (h ∣_ U) ⋙ schemeDerivedDirectImage U.ι)
    (hβ : β = (schemeMVDirectImageComposition (h ⁻¹ᵁ U).ι h).symm ≪≫
      eqToIso (congrArg schemeDerivedDirectImage (morphismRestrict_ι h U).symm) ≪≫
      schemeMVDirectImageComposition (h ∣_ U) U.ι)
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (h ⁻¹ᵁ U).toScheme.toRingedSpace)) ℤ)
    [I.IsKInjective] :
    (schemeMVDerivedRestriction Y U).map
        (β.hom.app (DerivedCategory.Q.obj I)) ≫
        (schemeMVAdjunction Y U).counit.app
          ((schemeDerivedDirectImage (h ∣_ U)).obj (DerivedCategory.Q.obj I)) =
      (schemeMVOpenRestrictionComparison h U).hom.app
          ((schemeDerivedDirectImage (h ⁻¹ᵁ U).ι).obj (DerivedCategory.Q.obj I)) ≫
        (schemeDerivedDirectImage (h ∣_ U)).map
          ((schemeMVAdjunction X (h ⁻¹ᵁ U)).counit.app (DerivedCategory.Q.obj I)) := by
  sorry

end AlgebraicGeometry
