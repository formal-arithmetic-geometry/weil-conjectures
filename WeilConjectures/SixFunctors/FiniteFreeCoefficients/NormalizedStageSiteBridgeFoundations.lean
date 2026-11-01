/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDualitySiteComparison
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison

/-! # Finite-ring exceptional site bridges

Source: blueprint latest, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp
  AlgebraicGeometry.ProEtale.pbcComparisonReduction
  _root_.DerivedCategory.monoidalClosed
  _root_.DerivedCategory.instMonoidalCategory_weilConjectures
  _root_.DerivedCategory.commShift₂CurriedTensor

private theorem boundedConstructible_iff_source
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) (K : Cat A X) :
    Etale.DerivedCategory.isBoundedConstructible A X K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
  constructor
  · rintro ⟨hc, a, b, hab, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun q ↦ ?_⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 fun q hq ↦ hz q (.inl hq)
    · exact (_root_.DerivedCategory.isLE_iff K b).2 fun q hq ↦ hz q (.inr hq)
    · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc q),
      min a b, b, min_le_right _ _, fun q hq ↦ ?_⟩
    rcases hq with hq | hq
    · exact (_root_.DerivedCategory.isGE_iff K a).1 ha q (hq.trans_le (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff K b).1 hb q hq

private theorem closed_bridge_iso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Cat A X) (hM : Ctf A X M) : IsIso (Sites.closedBridge A i M) := by
  have hunit := ProEtale.isIso_derivedComparisonAdjunction_unit_app (ModuleCat.{u + 1} A) X M
    ((boundedConstructible_iff_source A X M).1 hM.1).1.1
  dsimp only [Sites.closedBridge]
  have hmap := @Functor.map_isIso _ _ _ _ _ _ (closedUpper A i)
    ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app M) hunit
  exact @Functor.map_isIso _ _ _ _ _ _ (Sites.nu A Z) _ hmap

private theorem omega_bridge_iso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X S : Scheme.{u}} {aX : X ⟶ S} (c : Compactification aX) :
    IsIso (Sites.omegaBridge A c) := by
  have hbase := ProEtale.isIso_baseUnit (ModuleCat.{u + 1} A) S
    (ProEtale.comparisonUpperStarUnitIso A S).hom
  dsimp only [Sites.omegaBridge]
  have hmap := @Functor.map_isIso _ _ _ _ _ _ (upper A c)
    (ProEtale.finiteDualityBaseUnit (ModuleCat.{u + 1} A) S
      (ProEtale.comparisonUpperStarUnitIso A S).hom) hbase
  exact @Functor.map_isIso _ _ _ _ _ _ (Sites.nu A X) _ hmap

/-- The closed and dualizing site bridges are isomorphisms for finite coefficients.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--3;
finite duality site comparison, its derived comparison unit and base-unit lemma.
(blueprint: lem-sf-normalized-stage-site-bridge-foundations).

Proof: convert finite-value bounded constructibility to the source t-structure
predicate. The comparison-adjunction unit is invertible at its bounded-below input.
Applying the closed exceptional functor and then the exact site inverse image
preserves this isomorphism; the resulting map is the defined closed bridge.
The published finiteDualityBaseUnit is invertible for the canonical constant-unit
comparison. Apply the compactified upper functor and site inverse image to it.
The resulting map is exactly omegaBridge. Both assertions use the specified arrows,
without replacing them by arbitrary isomorphisms. -/
theorem finite_ring_site_bridge_foundations
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ S} (c : Compactification aX) :
    (∀ M : Cat A X, Ctf A X M → IsIso (Sites.closedBridge A i M)) ∧
      IsIso (Sites.omegaBridge A c) := by
  exact ⟨closed_bridge_iso A i, omega_bridge_iso A c⟩

end WeilConjectures.FiniteFreeCoefficients
