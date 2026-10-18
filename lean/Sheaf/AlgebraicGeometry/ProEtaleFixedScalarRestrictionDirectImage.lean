/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.Paper.WitnessCompatibility
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Direct image and finite coefficient restriction in the fixed scalar presentation

Source: Stacks, Tags 0D6E and 07A6; blueprint
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars).
The comparison is the actual adjunction mate of the canonical inverse-image comparison.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The canonical inverse-image/restriction square, with its published normalization.
Source: Stacks Tag 07A6
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars). -/
noncomputable abbrev fixedScalarRestrictionPullback
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  leftDerivedUpperStarRestrictScalarsIso φ f

/-- The inverse-direction direct-image comparison is the mate of the canonical square.
Source: Stacks Tags 0D6E and 07A6
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars). -/
noncomputable def fixedScalarRestrictionDirectImageMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R((f)_*[ModuleCat.{u + 1} B]) ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ ⟶
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        R((f)_*[ModuleCat.{u + 1} A]) :=
  mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (fixedScalarRestrictionPullback φ f).hom

/-- Restriction of finite coefficients commutes with the unbounded derived direct image.
The map is fixed by its adjunction-mate definition, rather than an arbitrary isomorphism.
Source: Stacks Tags 0D6E and 07A6
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars).
Proof: restriction is exact. The two composites are the direct image of the same
morphism of ringed topoi. Resolve a K-injective B-complex after restriction by a
K-injective A-complex. The right-derived comparison is inverse to the image of this
resolution. The canonical derived adjunction formula identifies that comparison with
the mate above. In particular this argument does not suppose that restriction itself
preserves K-injectives. This gives invertibility for every unbounded object. -/
theorem fixedScalarRestrictionDirectImageMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (fixedScalarRestrictionDirectImageMap φ f) := by
  sorry

/-- The forward-direction canonical comparison, with the K-injective normalization
inherited from the named mate theorem. Source: Stacks Tag 0D6E
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars). -/
noncomputable def fixedScalarRestrictionDirectImage
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙
        R((f)_*[ModuleCat.{u + 1} A]) ≅
      R((f)_*[ModuleCat.{u + 1} B]) ⋙
        Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ :=
  letI := fixedScalarRestrictionDirectImageMap_isIso φ f
  (asIso (fixedScalarRestrictionDirectImageMap φ f)).symm

/-- The canonical comparison is the inverse image of the restricted K-injective
resolution, with all exact-functor quotient identifications written explicitly.
Source: Stacks Tags 0D6E and 0D6J
(blueprint: lem-weil-proetale-direct-image-restriction-of-scalars).
Proof: resolve the scalar restriction of J by I. The composition theorem for the two
factorizations of the same ringed-topos map makes f_*(j) a quasi-isomorphism. Both
underived composites are definitionally restriction of the same module presheaf.
The canonical derived-adjunction fraction formula identifies their comparison with
the mate used above; insert the exact-restriction factorization isomorphisms and the
K-injective computation isomorphisms to obtain the displayed equation. -/
theorem fixedScalarRestrictionDirectImage_kInjective
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)) ℤ)
    [J.IsKInjective]
    (I : CochainComplex (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) ℤ)
    [I.IsKInjective]
    (j : ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapHomologicalComplex
      (.up ℤ)).obj J ⟶ I) [QuasiIso j] :
    QuasiIso (((lowerStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map j) ∧
      (fixedScalarRestrictionDirectImage φ f).hom.app (_root_.DerivedCategory.Q.obj J) ≫
          (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
            ((lowerStar (ModuleCat.{u + 1} B) f).rightDerivedFunctorObjQIso J).hom ≫
          (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ).mapDerivedCategoryFactors.hom.app
            (((lowerStar (ModuleCat.{u + 1} B) f).mapHomologicalComplex (.up ℤ)).obj J) ≫
          _root_.DerivedCategory.Q.map
            (((lowerStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).map j) =
        (R((f)_*[ModuleCat.{u + 1} A])).map
            ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryFactors.hom.app
              J) ≫
          (R((f)_*[ModuleCat.{u + 1} A])).map (_root_.DerivedCategory.Q.map j) ≫
          ((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorObjQIso I).hom := by
  sorry

end AlgebraicGeometry.ProEtale
