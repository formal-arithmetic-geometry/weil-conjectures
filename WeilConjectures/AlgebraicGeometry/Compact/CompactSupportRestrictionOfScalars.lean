/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedUpperShriek

/-!
# The canonical compact-support restriction comparison

Source: Stacks Tags 0GL5, 0GL6 and 0D6E; blueprint
(blueprint: lem-sf-compact-support-restriction-of-scalars).
All categories are the standard fixed-scalar presentation of modules over the constant ring.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The exact open adjunction, with the published derived pullback as right adjoint.
Source: Stacks Tag 03S2
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def fixedScalarOpenAdjunction (A : Type (u + 1)) [CommRing A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    D((j)_!open[ModuleCat.{u + 1} A]) ⊣ L((j)^*[ModuleCat.{u + 1} A]) :=
  ((openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) j).mapDerivedCategoryAdjunction).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).symm

/-- Open extension and scalar restriction, normalized by the unit of the open adjunction.
It is the inverse mate of the actual restriction/pullback isomorphism.
Source: Stacks Tags 03S2 and 07A6
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def fixedScalarRestrictionOpenMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        D((j)_!open[ModuleCat.{u + 1} A]) ⟶
      D((j)_!open[ModuleCat.{u + 1} B]) ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ :=
  (mateEquiv (fixedScalarOpenAdjunction B j) (fixedScalarOpenAdjunction A j)).symm
    (fixedScalarRestrictionPullback φ j).inv

/-- Restriction commutes with the exact extension by zero.
Source: Stacks Tags 03S2 and 0GL6
(blueprint: lem-sf-compact-support-restriction-of-scalars).
Proof: on sheaves both composites have the same underlying extension-by-zero groups,
restriction maps and scalar actions. The identity on these groups is an isomorphism.
Its transpose is restriction of the unit of the open adjunction, hence it is exactly
the inverse mate displayed above. The equality descends termwise because all open
functors and restriction of scalars are exact. -/
theorem fixedScalarRestrictionOpenMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    IsIso (fixedScalarRestrictionOpenMap φ j) := by
  sorry

/-- The canonical open comparison, with its unit normalization.
Source: Stacks Tag 0GL6 (blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def fixedScalarRestrictionOpen
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  letI := fixedScalarRestrictionOpenMap_isIso φ j
  asIso (fixedScalarRestrictionOpenMap φ j)

/-- The specified proper/open composite, in the forward restriction direction.
Source: Stacks Tags 0GL5 and 0GL6
(blueprint: lem-sf-compact-support-restriction-of-scalars). -/
noncomputable def compactSupportRestrictionIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        Rf_!(c)[ModuleCat.{u + 1} A] ≅
      Rf_!(c)[ModuleCat.{u + 1} B] ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (fixedScalarRestrictionOpen φ c.i) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (fixedScalarRestrictionDirectImage φ c.g) ≪≫
    (Functor.associator _ _ _).symm

end AlgebraicGeometry.ProEtale
