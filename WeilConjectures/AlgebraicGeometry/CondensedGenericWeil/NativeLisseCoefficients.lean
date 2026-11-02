/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedGenericWeil.CondensedGenericWeilData
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels

/-! # Native local freeness and pullback

Source: Bhatt--Scholze, Section 6.8, coefficient trivializing covers.
(blueprint: lem-dl-a1-native-lisse-coefficients).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxSize 4096
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj TensorProduct
namespace AlgebraicGeometry.ProEtale.CondensedGenericWeil

attribute [local irreducible] CondensedRing.upperStar

/-- The two published local-freeness conventions agree for the pulled-back coefficients.
Source: Bhatt--Scholze, Section 6.8, and the normalized coefficient pullback comparison.
(blueprint: lem-dl-a1-native-lisse-coefficients). -/
theorem lisse_coefficient_iff_locallyFree
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} (M : RealCondensedFibre.Modules Λ X) :
    IsLisseCoefficientModule Λ M ↔ CondensedRing.LocallyFree (condensedRingObj Λ X) M := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun s ↦ (CondensedRing.freeAt_iff_standard Λ (C.f s) M).mpr (hC s)⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun s ↦ (CondensedRing.freeAt_iff_standard Λ (C.f s) M).mp (hC s)⟩

/-- Pullback preserves the lisse coefficient predicate used by the Weil category.
Source: base change of a trivializing cover, Bhatt--Scholze, Section 6.8.
(blueprint: lem-dl-a1-native-lisse-coefficients). -/
theorem lisse_coefficient_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (j : Y ⟶ X) (M : RealCondensedFibre.Modules Λ X)
    (hM : IsLisseCoefficientModule Λ M) :
    IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ j).obj M) := by
  exact (lisse_coefficient_iff_locallyFree Λ _).mpr
    (CondensedRing.locallyFree_upperStar Λ j
      ((lisse_coefficient_iff_locallyFree Λ M).mp hM))

/-- The native lisse predicate descends through a pro-etale covering family.
Source: Bhatt--Scholze, Section 6.8, composition of trivializing covers.
(blueprint: lem-dl-a1-native-lisse-coefficients).

Proof: refine each cover member by its supplied finite-free trivialization.
Composition of covers gives a cover of the original scheme; pullback composition
identifies the resulting module with the original module pulled to each member. -/
theorem lisse_coefficient_of_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} (M : RealCondensedFibre.Modules Λ X)
    (C : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (h : ∀ s, IsLisseCoefficientModule Λ ((CondensedRing.upperStar Λ (C.f s)).obj M)) :
    IsLisseCoefficientModule Λ M := by
  exact CondensedRing.locFree_of_cover M C h

/-- Isomorphic native coefficient modules have the same lisse property.
Source: Bhatt--Scholze, Section 6.8, invariance of local finite freeness.
(blueprint: lem-dl-a1-native-lisse-coefficients).

Proof: pull the isomorphism to a trivializing cover and transfer the free module
isomorphisms there. The standard and native coefficient conventions agree. -/
theorem lisse_coefficient_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X : Scheme.{u}} {M N : RealCondensedFibre.Modules Λ X} (e : M ≅ N)
    (hM : IsLisseCoefficientModule Λ M) : IsLisseCoefficientModule Λ N := by
  exact (lisse_coefficient_iff_locallyFree Λ N).mpr
    (CondensedRing.locallyFree_of_iso e ((lisse_coefficient_iff_locallyFree Λ M).mp hM))

end AlgebraicGeometry.ProEtale.CondensedGenericWeil
