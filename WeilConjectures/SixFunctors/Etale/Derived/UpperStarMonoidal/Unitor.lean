/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.CompUnit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure

/-!
# The unit of the oplax monoidal derived pullback

The canonical isomorphism `Lg^* Λ_Y ≅ Λ_Z` is the counit `η` of the oplax monoidal derived
pullback (`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso_hom_eq_η`), and the left unitor of
the derived tensor product is compatible with the derived pullback
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_derivedTensorLeftUnitor_hom`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

section Unitor

open Functor.OplaxMonoidal

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The left unitality of the oplax monoidal derived pullback
(`AlgebraicGeometry.Etale.leftDerivedUpperStarOplaxMonoidal`), stated with the left unitor of the
derived tensor product. -/
lemma leftDerivedUpperStar_map_derivedTensorLeftUnitor_hom {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    [(g)^*[A].PreservesFlat] (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarOplaxMonoidal A g
    (L((g)^*[A])).map (derivedTensorLeftUnitor A Y K).hom =
      (leftDerivedUpperStarTensorIso A g _ K).hom ≫
        ((derivedTensor A Z).map (η L((g)^*[A]))).app _ ≫
          (derivedTensorLeftUnitor A Z _).hom := by
  let := leftDerivedUpperStarOplaxMonoidal A g
  exact (left_unitality_hom L((g)^*[A]) K).symm

end Unitor

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The canonical isomorphism `Lg^* Λ_Y ≅ Λ_Z` is the counit `η` of the oplax monoidal derived
pullback. -/
lemma leftDerivedUpperStarUnitIso_hom_eq_η {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) g
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) g).hom =
      Functor.OplaxMonoidal.η (L((g)^*[ModuleCat.{u + 1} Λ])) := by
  have h := leftDerivedUpperStarUnitIso_hom_comp_ε (ModuleCat.{u + 1} Λ) g
  rw [leftDerivedUpperStar_η_eq]
  simp only [← Category.assoc]
  rw [IsIso.eq_comp_inv, h]
  simp only [Category.assoc]
  rfl

end AlgebraicGeometry.Etale
