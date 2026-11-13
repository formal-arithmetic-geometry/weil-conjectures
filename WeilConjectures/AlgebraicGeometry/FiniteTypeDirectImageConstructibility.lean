/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.DirectImage

/-!
# Bounded constructibility of finite-type direct images

The ordinary derived direct image preserves bounded constructibility, without a
separatedness hypothesis on the morphism.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Direct image for a morphism of finite-type schemes over a field preserves bounded
constructible complexes with finite allowable commutative coefficients. -/
theorem isBoundedConstructible_rightDerivedLowerStar_of_finiteType_over_field
    (k : Type u) [Field k] (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : IsSmoothBaseChangeCoefficients N A (Spec (.of k)))
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX)
    (K : DerivedCategoryModule A X) (hK : DerivedCategory.isBoundedConstructible A X K) :
    DerivedCategory.isBoundedConstructible A Y
      ((rightDerivedLowerStar (ModuleCat.{u + 1} A) f).obj K) := by
  have : HasInvertibleExponent A (Spec (.of k)) :=
    ⟨N, hA.1, hA.2.2.1, hA.2.2.2⟩
  have hK' : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K := by
    obtain ⟨hc, a, b, hab, hvan⟩ := hK
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun q ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc q)⟩
    · exact (_root_.DerivedCategory.isGE_iff K a).2 fun i hi ↦ hvan i (Or.inl hi)
    · exact (_root_.DerivedCategory.isLE_iff K b).2 fun i hi ↦ hvan i (Or.inr hi)
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩ :=
    boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType A f aX aY hf K hK'
  refine ⟨fun q ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2 (hc q),
    min a b, max a b, min_le_max, fun i hi ↦ ?_⟩
  rcases hi with hi | hi
  · exact (_root_.DerivedCategory.isGE_iff _ a).1 ha i (lt_of_lt_of_le hi (min_le_left _ _))
  · exact (_root_.DerivedCategory.isLE_iff _ b).1 hb i (lt_of_le_of_lt (le_max_right _ _) hi)

end AlgebraicGeometry.Etale
