/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleDerivedFunctorCompositorShifts
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteCoefficientTriangulated
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement

/-!
# Integer shift witnesses for ordinary condensed pullbacks

Source: latest blueprint, sec-smooth-purity/sk-prop-sf-localization/
prop-sf-open-closed-triangle-all-stages.proof.md, Weil structures paragraph.
(blueprint: new-h2-integral-shift-witness)

The auxiliary definitions construct the bounded-constructible restrictions, their canonical
termwise comparisons, and the inverse square comparison. The theorem records the integer shifts,
exactness, and compatibility for the coefficient cases of the node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures

/-- Restriction of an ordinary condensed-module derived pullback to bounded constructible objects.
Source: `def-sf-setting` and `lem-sfb-dc-upper-star-preserves` (blueprint:
new-h2-integral-shift-witness). -/
noncomputable def restrictedCondensedPullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    BoundedConstructible (condensedRingObj Λ Y) ⥤
      BoundedConstructible (condensedRingObj Λ X) :=
  (boundedConstructible (condensedRingObj Λ X)).lift
    ((boundedConstructible (condensedRingObj Λ Y)).ι ⋙
      moduleObjectDerivedPullback Λ g)
    (fun K ↦ boundedConstructible_leftDerivedUpperStar_obj_of_scheme Λ g K.obj K.property)

/-- Compatibility of the restricted pullback with its ambient left-derived pullback.
Source: `def-sf-setting` and `lem-sfb-dc-upper-star-preserves` (blueprint:
new-h2-integral-shift-witness). -/
noncomputable def restrictedCondensedPullbackCompatibility
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    restrictedCondensedPullback Λ g ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ moduleObjectDerivedPullback Λ g :=
  ObjectProperty.liftCompιIso _ _ _

/-- Comparison of the restricted pullback with termwise exact pullback followed by localization.
Source: `lem-sfb-module-derived-functor-compositor-shifts` (blueprint:
new-h2-integral-shift-witness). -/
noncomputable def restrictedCondensedPullbackTermwiseComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    restrictedCondensedPullback Λ g ⋙ (boundedConstructible _).ι ≅
      (boundedConstructible _).ι ⋙ (upperStar Λ g).mapDerivedCategory :=
  restrictedCondensedPullbackCompatibility Λ g ≪≫
    Functor.isoWhiskerLeft (boundedConstructible _).ι
      (modulePullbackExactComparison Λ g)

/-- The inverse square comparison on bounded constructible restrictions, constructed by fully
faithful preimage of the ambient canonical comparison with its specified inverse orientation.
Source: latest blueprint, sec-smooth-purity/sk-prop-sf-localization/
prop-sf-open-closed-triangle-all-stages.proof.md, Weil structures paragraph, and
`lem-sfb-module-derived-functor-compositor-shifts`.
(blueprint: new-h2-integral-shift-witness) -/
noncomputable def restrictedCondensedPullbackSquareComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}}
    (f : Y ⟶ X) (eX : X ≅ X) (eY : Y ≅ Y)
    (h : eY.hom ≫ f = f ≫ eX.hom) :
    restrictedCondensedPullback Λ f ⋙ restrictedCondensedPullback Λ eY.hom ≅
      restrictedCondensedPullback Λ eX.hom ⋙ restrictedCondensedPullback Λ f := by
  apply ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
  exact
    (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft _ (restrictedCondensedPullbackCompatibility Λ eY.hom) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (restrictedCondensedPullbackCompatibility Λ f) _ ≪≫
      (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft _
        (modulePullbackSquareComparison Λ f eX.hom eY.hom f h.symm).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (restrictedCondensedPullbackCompatibility Λ eX.hom).symm _ ≪≫
      (Functor.associator _ _ _) ≪≫
      Functor.isoWhiskerLeft _ (restrictedCondensedPullbackCompatibility Λ f).symm ≪≫
      (Functor.associator _ _ _).symm

end WeilConjectures
