/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A8
-/
module

public import Sheaf.Paper.WitnessCompatibility
public import Sheaf.Paper.AdicCoefficientDatum

/-!
# Canonical unit and reassociation for quotient scalar extensions

Source: Stacks Tags 06YY and 09B1, coefficient refinement of the compatible-origin argument
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons).
The definitions are relocated verbatim from NormalizedEtaleOriginWitnesses.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- Canonical identity restriction on sheaves, given by identity section maps.
Source: Stacks 06YY, unit balancing in the coefficient refinement of Tag 09B1
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons). -/
def normalizedOriginRestrictionUnit
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R : Type (u + 1)} [CommRing R] (φ : R →+* R) (hφ : φ = RingHom.id R) :
    Sheaf.restrictScalars J φ ≅ 𝟭 (Sheaf J (ModuleCat.{u + 1} R)) :=
  NatIso.ofComponents
    (fun F ↦ (fullyFaithfulSheafToPresheaf J _).preimageIso
      (Functor.isoWhiskerLeft F.obj (ModuleCat.restrictScalarsId' φ hφ) ≪≫
        F.obj.rightUnitor))
    (fun {F G} f ↦ by
      apply (fullyFaithfulSheafToPresheaf J _).map_injective
      ext U x
      rfl)

/-- Canonical self-extension unit, the adjunction mate of identity scalar restriction.
It is the derived map x tensor a to ax, not a chosen automorphism.
Source: Stacks 06YY, unit balancing in the coefficient refinement of Tag 09B1
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons). -/
def normalizedOriginScalarUnit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R]
    (φ : R →+* R) (hφ : φ = RingHom.id R) :
    pbcFixedScalarExtension J φ ≅ 𝟭 (DerivedCategory (Sheaf J (ModuleCat.{u + 1} R))) :=
  Adjunction.leftAdjointIdIso (Adjunction.ofIsRightAdjoint _)
    (Functor.mapDerivedCategoryNatIso (normalizedOriginRestrictionUnit J φ hφ) ≪≫
      Functor.mapDerivedCategoryIdIso _)

/-- The canonical scalar unit at a positive quotient, including the first quotient.
Source: Stacks 06YY and 09B1, coefficient refinement
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons). -/
def normalizedOriginQuotientUnit
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (n : ℕ) :
    pbcFixedScalarExtension J (pbcWitnessQuotientMap d n n (le_refl n)) ≅ 𝟭 _ :=
  normalizedOriginScalarUnit J _
    (Scheme.adicQuotientMap_id d.ideal ⟨n + 1, Nat.succ_pos n⟩)

/-- Canonical reassociation for three quotient levels. This is the published
scalar-extension composition comparison, with the actual quotient-factor identity.
Source: Stacks 06YY and 09B1, coefficient refinement
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons). -/
def normalizedOriginQuotientComp
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (k m n : ℕ) (hnm : n ≤ m) (hmk : m ≤ k) :
    pbcFixedScalarExtension J (pbcWitnessQuotientMap d k m hmk) ⋙
        pbcFixedScalarExtension J (pbcWitnessQuotientMap d m n hnm) ≅
      pbcFixedScalarExtension J (pbcWitnessQuotientMap d k n (hnm.trans hmk)) :=
  pbcFixedScalarExtensionComp J _ _ _
    (Scheme.adicQuotientMap_comp d.ideal ⟨k + 1, Nat.succ_pos k⟩
      ⟨m + 1, Nat.succ_pos m⟩ ⟨n + 1, Nat.succ_pos n⟩
      (Nat.add_le_add_right hnm 1) (Nat.add_le_add_right hmk 1)).symm

/-- Direct quotient scalar extension, in the published fixed-ring presentation.
Source: Stacks 06YY and 09B1, coefficient refinement
(blueprint: def-weil-pbc-normalized-origin-scalar-comparisons). -/
abbrev normalizedOriginReduction
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (m n : ℕ) (h : n ≤ m) :=
  pbcFixedScalarExtension J (pbcWitnessQuotientMap d m n h)

end AlgebraicGeometry.ProEtale
