/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F4
-/
module

public import Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
public import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
public import WeilConjectures.SixFunctors.BaseChange.DerivedPasting.Vertical
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Coherence of the normalized proper/open comparison -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, More on Étale Cohomology, Tags 0F7C and 0F7D.

Proof: First compose each proposed ordinary pasting equation with the inclusion
into the direct image along the outer composite. This is monic, since extension
by zero includes into direct image and direct image preserves monomorphisms.
Naturality, the normalization of δ and associativity of lowerStarComp give the
same composite, proving both ordinary pasting equations. The extension-by-zero
compositor is the adjunction compositor, so its inclusion is the composite of the
two inclusions; the identity compositor has the corresponding unit property.
To derive the vertical law, form the two natural transformations from the
composite right derived direct image followed by the exact bottom extension.
Precompose with its defining unit. Use the factorization equations for
rightDerivedFunctorPlusBaseChange and rightDerivedFunctorPlusCompIso' to replace
the derived maps by their termwise comparisons. Naturality of the target derived
unit moves the ordinary compositor through the unit. The ordinary vertical
pasting equation then identifies the two composites. Direct image preserves
injectives, so its canonical composite is a right derived functor; the source
rightDerived_ext theorem gives equality before precomposition.
For horizontal pasting use the absolute right derived functor Rr* followed by
the two exact extensions. Apply the same argument using the factorization
of mapDerivedCategoryPlusCompIso and mapDerivedCategoryPlusNatIso. The ordinary
horizontal equation identifies the termwise composites, and rightDerived_ext
again gives equality. The exact derived compositor here is precisely
extensionZeroCompDerivedPlusIso. For horizontal identity squares, use the
ordinary identity equation, the factorization of the exact leftAdjointIdIso,
and the same uniqueness argument. No resolution is chosen, and no claim that
extension by zero preserves injectives is needed.
(blueprint: lem-cbc-proper-open-interchange-composition). -/
theorem properOpenInterchange_composition
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
    (∀ {A B C D E F : Scheme.{u}}
      (k : A ⟶ B) (i : C ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j)
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusCompIso' (lowerStar (ModuleCat.{u + 1} Λ) r₁) (lowerStar
        (ModuleCat.{u + 1} Λ) r₂) (lowerStarComp (ModuleCat.{u + 1} Λ) r₁ r₂)).hom.app K) ≫
        (Functor.rightDerivedFunctorPlusBaseChange (δ k j (r₁ ≫ r₂) (p₁ ≫ p₂) h).hom).app K ≫
        (Functor.rightDerivedFunctorPlusCompIso' (lowerStar (ModuleCat.{u + 1} Λ) p₁) (lowerStar
        (ModuleCat.{u + 1} Λ) p₂) (lowerStarComp (ModuleCat.{u + 1} Λ) p₁ p₂)).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) k).mapDerivedCategoryPlus.obj K) =
      (Functor.rightDerivedFunctorPlusBaseChange (δ i j r₂ p₂ h₂).hom).app
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r₁).obj K) ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) p₂).map
          ((Functor.rightDerivedFunctorPlusBaseChange (δ k i r₁ p₁ h₁).hom).app K)) ∧
    (∀ {A B C D E F : Scheme.{u}}
      (k : A ⟶ B) (l : B ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C) (p : B ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j))
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (extensionZeroCompDerivedPlusIso Λ i j).hom.app ((rightDerivedLowerStarPlus (ModuleCat.{u + 1}
        Λ) r).obj K) ≫
        (Functor.rightDerivedFunctorPlusBaseChange (δ (k ≫ l) (i ≫ j) r q h).hom).app K ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) q).map ((extensionZeroCompDerivedPlusIso Λ
        k l).inv.app K) =
      (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.map
        ((Functor.rightDerivedFunctorPlusBaseChange (δ k i r p
        h₁).hom).app K) ≫
        (Functor.rightDerivedFunctorPlusBaseChange (δ l j p q h₂).hom).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
        k).mapDerivedCategoryPlus.obj K)) ∧
    (∀ {A C : Scheme.{u}} (r : A ⟶ C) [IsProper r]
      (K : DerivedCategory.Plus (Sheaf A.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
      (Functor.rightDerivedFunctorPlusBaseChange (δ (𝟙 A) (𝟙 C) r r ((Category.id_comp r).trans
        (Category.comp_id r).symm)).hom).app K ≫
        (rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).map
        ((Functor.mapDerivedCategoryPlusNatIso (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 A)) (upperStarId
        (ModuleCat.{u + 1} Λ) A)) ≪≫ Functor.mapDerivedCategoryPlusIdIso _).hom.app K) =
      (Functor.mapDerivedCategoryPlusNatIso (Adjunction.leftAdjointIdIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 C)) (upperStarId
        (ModuleCat.{u + 1} Λ) C)) ≪≫ Functor.mapDerivedCategoryPlusIdIso _).hom.app
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) r).obj K)) := by
  sorry

end AlgebraicGeometry.Etale
