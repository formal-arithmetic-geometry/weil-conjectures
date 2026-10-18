/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.ProperOpenComparison
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange

/-! # Coherence of the normalized proper/open comparison -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, More on Étale Cohomology, Tag 0F7B, refinement specialization.

Proof: Let V = T₁ ×[T₂] X, and let s : X → V be the section defined by (j₁,id).
The section is open and closed, since its composite with the open first projection is
j₁ and it is a section of the proper second projection. Restrict the comparison to j₂.
The unit identity for rightDerivedFunctorPlusBaseChange computes it on an injective
representative by δ followed by the target derived unit. The assumed normalization
of δ identifies the underlying sheaf map with extension by zero from the s-component:
it is the identity on that component and zero on its complement. Under the canonical
base-change, extension-by-zero base-change and clopen-component restriction maps,
this is exactly the inverse of properOpenIdentification. The descended adjunction
j₂! ⊣ j₂* identifies a map out of j₂!K with its restriction followed by the unit.
Thus the map is j₂! of that inverse followed by the counit, which is the definition
of properOpenComparison. The lowerStar identity isomorphism removes R(id)_* with
its canonical unit normalization. No Cartesian hypothesis on the original square is used.
(blueprint: lem-cbc-proper-open-interchange-refinement-normalization). -/
theorem properOpenInterchange_refinement_normalization
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (δ : ∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D) [IsOpenImmersion
        k] [IsOpenImmersion i] [IsProper r] [IsProper p] (_h : k ≫ p = r ≫ i), (lowerStar
        (ModuleCat.{u + 1} Λ) r) ⋙ (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) i) ≅
        (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k) ⋙ (lowerStar (ModuleCat.{u + 1} Λ) p))
    (hδ : (∀ {A B C D : Scheme.{u}} (k : A ⟶ B) (i : C ⟶ D) (r : A ⟶ C) (p : B ⟶ D)
      [IsOpenImmersion k]
        [IsOpenImmersion i] [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i), ∀ (F : (Sheaf
        A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (δ k i r p h).hom.app F ≫ (lowerStar (ModuleCat.{u + 1} Λ) p).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) k).app F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) k p).hom.app F =
      (openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} Λ) i).app ((lowerStar (ModuleCat.{u +
        1} Λ) r).obj F) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) r i (k ≫ p) h).hom.app F)) :
    (∀ {T₁ T₂ X : Scheme.{u}} (p : T₁ ⟶ T₂) [IsProper p]
      (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) [IsOpenImmersion j₁] [IsOpenImmersion j₂]
      (h : j₁ ≫ p = j₂) (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1}
        Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategoryPlus.map
        ((lowerStarIdDerivedPlus (ModuleCat.{u + 1} Λ) X).inv.app K) ≫
        (Functor.rightDerivedFunctorPlusBaseChange (δ j₁ j₂ (𝟙 X) p (h.trans (Category.id_comp
          j₂).symm)).hom).app K =
      properOpenComparison Λ p j₁ j₂ h K) := by
  sorry

end AlgebraicGeometry.Etale
