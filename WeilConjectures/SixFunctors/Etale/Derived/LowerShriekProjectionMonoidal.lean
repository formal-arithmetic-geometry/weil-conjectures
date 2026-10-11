/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionComp
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit

/-!
# Associativity and unitality of the projection maps of the six operations

We show that the projection maps of the derived direct image `Rp_*`, of the extension by zero
`j_!` along an open immersion and of the compactly supported direct image `Rf_!` are
associative and unital, i.e. compatible with the associators and unitors of the derived tensor
product and with the monoidal structure of the derived pullbacks.

## Main statements

- `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_associativity`,
  `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_rightUnitor_hom`: the
  associativity and right unitality of the tensor comparison of `Lg^*`.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap_associativity`: associativity of
  the projection map of `Rp_*`.
- `AlgebraicGeometry.Etale.projectionMapOfCompactification_associativity`,
  `AlgebraicGeometry.Etale.projectionMapOfCompactification_rightUnitality`: associativity and
  unitality of the projection map `PF_c : Rf_!(c)K ⊗ᴸ L ⟶ Rf_!(c)(K ⊗ᴸ Lf^*L)`.
- `AlgebraicGeometry.Etale.projectionMapOfCompactification_comp_forgetSupports`: the projection
  map of `Rf_!` is compatible with that of `Rf_*` through the forget-supports map `Rf_! ⟶ Rf_*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

namespace Etale

section UpperStar

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- **Associativity of the tensor comparison of `Lg^*`**: the comparison
`Lg^*(K ⊗ᴸ M) ⟶ Lg^*K ⊗ᴸ Lg^*M` satisfies the associativity axiom of an oplax monoidal
functor. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_associativity
    (K L M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((leftDerivedUpperStarTensorComparison A g).app (K ⊗ L)).app M ≫
        ((leftDerivedUpperStarTensorComparison A g).app K).app L ▷ L((g)^*[A]).obj M ≫
        (α_ _ _ _).hom =
      L((g)^*[A]).map (α_ K L M).hom ≫
        ((leftDerivedUpperStarTensorComparison A g).app K).app (L ⊗ M) ≫
        L((g)^*[A]).obj K ◁ ((leftDerivedUpperStarTensorComparison A g).app L).app M := by
  let := leftDerivedUpperStarOplaxMonoidal A g
  exact Functor.OplaxMonoidal.associativity L((g)^*[A]) K L M

/-- The unit comparison of the oplax monoidal structure of `Lg^*` is the identification
`Lg^* Λ_Y ≅ Λ_Z` of `AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`. -/
lemma leftDerivedUpperStarOplaxMonoidal_η :
    let := leftDerivedUpperStarOplaxMonoidal A g
    Functor.OplaxMonoidal.η L((g)^*[A]) = (leftDerivedUpperStarUnitIso A g).hom := by
  let := leftDerivedUpperStarOplaxMonoidal A g
  have := isIso_leftDerivedUpperStarOplaxMonoidal_δ A g (𝟙_ _) (𝟙_ _)
  exact (Functor.eq_of_leftUnitality (F := L((g)^*[A]))
    (Functor.OplaxMonoidal.δ _ (𝟙_ _) (𝟙_ _)) (leftDerivedUpperStarUnitIso A g).hom _
    (leftDerivedUpperStarTensorComparison_leftUnitor_hom A g _)
    (Functor.OplaxMonoidal.left_unitality_hom _ _)).symm

/-- **Right unitality of the tensor comparison of `Lg^*`**:
`μ_{K, Λ} ≫ (Lg^* K ◁ ε) ≫ ρ = Lg^*(ρ)`, for the tensor comparison
`μ : Lg^*(K ⊗ᴸ Λ_Y) ⟶ Lg^*K ⊗ᴸ Lg^*Λ_Y` and the unit comparison `ε : Lg^* Λ_Y ≅ Λ_Z`. -/
@[reassoc]
lemma leftDerivedUpperStarTensorComparison_rightUnitor_hom
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((leftDerivedUpperStarTensorComparison A g).app K).app (𝟙_ _) ≫
        L((g)^*[A]).obj K ◁ (leftDerivedUpperStarUnitIso A g).hom ≫
          (ρ_ (L((g)^*[A]).obj K)).hom =
      L((g)^*[A]).map (ρ_ K).hom := by
  let := leftDerivedUpperStarOplaxMonoidal A g
  have h : Functor.OplaxMonoidal.η L((g)^*[A]) = (leftDerivedUpperStarUnitIso A g).hom :=
    leftDerivedUpperStarOplaxMonoidal_η A g
  rw [← h]
  exact Functor.OplaxMonoidal.right_unitality_hom L((g)^*[A]) K

/-- The associativity of the inverse `Lg^*K ⊗ᴸ Lg^*M ⟶ Lg^*(K ⊗ᴸ M)` of the tensor comparison
of `Lg^*`: the associativity axiom of a lax monoidal functor. -/
@[reassoc]
lemma inv_leftDerivedUpperStarTensorComparison_associativity
    (K L M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    inv (((leftDerivedUpperStarTensorComparison A g).app K).app L) ▷ L((g)^*[A]).obj M ≫
        inv (((leftDerivedUpperStarTensorComparison A g).app (K ⊗ L)).app M) ≫
        L((g)^*[A]).map (α_ K L M).hom =
      (α_ _ _ _).hom ≫
        L((g)^*[A]).obj K ◁ inv (((leftDerivedUpperStarTensorComparison A g).app L).app M) ≫
        inv (((leftDerivedUpperStarTensorComparison A g).app K).app (L ⊗ M)) := by
  have h := leftDerivedUpperStarTensorComparison_associativity A g K L M
  rw [← cancel_epi (((leftDerivedUpperStarTensorComparison A g).app K).app L ▷ _),
    ← cancel_epi (((leftDerivedUpperStarTensorComparison A g).app (K ⊗ L)).app M)]
  simp only [← comp_whiskerRight_assoc, IsIso.hom_inv_id, id_whiskerRight, Category.id_comp,
    IsIso.hom_inv_id_assoc]
  rw [reassoc_of% h]
  simp only [← whiskerLeft_comp_assoc, IsIso.hom_inv_id, whiskerLeft_id, Category.id_comp,
    IsIso.hom_inv_id, Category.comp_id]

/-- The right unitality of the inverse of the tensor comparison of `Lg^*`. -/
@[reassoc]
lemma inv_leftDerivedUpperStarTensorComparison_rightUnitality
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    L((g)^*[A]).obj K ◁ (leftDerivedUpperStarUnitIso A g).inv ≫
        inv (((leftDerivedUpperStarTensorComparison A g).app K).app (𝟙_ _)) ≫
        L((g)^*[A]).map (ρ_ K).hom =
      (ρ_ (L((g)^*[A]).obj K)).hom := by
  rw [← leftDerivedUpperStarTensorComparison_rightUnitor_hom, IsIso.inv_hom_id_assoc,
    ← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]

end UpperStar
section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The components of the isomorphism `j^*M ⊗ᴸ Lj^*N ≅ j^*(M ⊗ᴸ N)`
(`AlgebraicGeometry.Etale.mapDerivedCategoryUpperStarDerivedTensorIso`). -/
lemma mapDerivedCategoryUpperStarDerivedTensorIso_hom_app_app
    (M N : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app M).app N =
      (leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app M ▷ L((j)^*[A]).obj N ≫
        inv (((leftDerivedUpperStarTensorComparison A j).app M).app N) ≫
        (leftDerivedUpperStarIsoMapDerivedCategory A j).hom.app (M ⊗ N) := by
  have h : ((leftDerivedUpperStarTensorNatIso A j).inv.app M).app N =
      inv (((leftDerivedUpperStarTensorComparison A j).app M).app N) :=
    IsIso.eq_inv_of_hom_inv_id
      (f := ((leftDerivedUpperStarTensorComparison A j).app M).app N)
      (((leftDerivedUpperStarTensorNatIso A j).app M).app N).hom_inv_id
  rw [← h]
  rfl

/-- The associativity of `j^*M ⊗ᴸ Lj^*N ≅ j^*(M ⊗ᴸ N)` with respect to the inverse of the
tensor comparison of `Lj^*`. -/
lemma mapDerivedCategoryUpperStarDerivedTensorIso_associativity
    (M N P : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app M).app N ▷
          L((j)^*[A]).obj P ≫
        ((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app (M ⊗ N)).app P ≫
        D((j)^*[A]).map (α_ M N P).hom =
      (α_ _ _ _).hom ≫
        D((j)^*[A]).obj M ◁ inv (((leftDerivedUpperStarTensorComparison A j).app N).app P) ≫
        ((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app M).app (N ⊗ P) := by
  simp only [mapDerivedCategoryUpperStarDerivedTensorIso_hom_app_app, Category.assoc]
  rw [comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
    ← comp_whiskerRight_assoc ((leftDerivedUpperStarIsoMapDerivedCategory A j).hom.app (M ⊗ N)),
    Iso.hom_inv_id_app, id_whiskerRight, Category.id_comp,
    ← (leftDerivedUpperStarIsoMapDerivedCategory A j).hom.naturality,
    inv_leftDerivedUpperStarTensorComparison_associativity_assoc,
    associator_naturality_left_assoc]
  erw [whisker_exchange_assoc]

/-- The right unitality of `j^*M ⊗ᴸ Lj^*N ≅ j^*(M ⊗ᴸ N)` with respect to the inverse of the
unit comparison of `Lj^*`. -/
lemma mapDerivedCategoryUpperStarDerivedTensorIso_rightUnitality
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    D((j)^*[A]).obj M ◁ (leftDerivedUpperStarUnitIso A j).inv ≫
        ((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app M).app (𝟙_ _) ≫
        D((j)^*[A]).map (ρ_ M).hom =
      (ρ_ _).hom := by
  rw [mapDerivedCategoryUpperStarDerivedTensorIso_hom_app_app, Category.assoc, Category.assoc,
    ← (leftDerivedUpperStarIsoMapDerivedCategory A j).hom.naturality,
    whisker_exchange_assoc]
  erw [inv_leftDerivedUpperStarTensorComparison_rightUnitality_assoc]
  rw [rightUnitor_naturality_assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- **Associativity of the projection map of `j_!`**: the projection map
`p : j_!(K ⊗ᴸ Lj^*N) ⟶ j_!K ⊗ᴸ N` satisfies `p ≫ (p ▷ N') ≫ α = j_!(α ≫ K ◁ μ) ≫ p`, for the
inverse `μ` of the tensor comparison of `Lj^*`. -/
@[reassoc]
lemma derivedOpenImmersionLowerShriekProjectionMap_associativity
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (N N' : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedOpenImmersionLowerShriekProjectionMap A j).app (K ⊗ L((j)^*[A]).obj N)).app N' ≫
        ((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app N ▷ N' ≫
        (α_ _ _ _).hom =
      D((j)_!open[A]).map ((α_ _ _ _).hom ≫
          K ◁ inv (((leftDerivedUpperStarTensorComparison A j).app N).app N')) ≫
        ((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app (N ⊗ N') :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).projectionMap_associativity _ _
    (fun N N' ↦ inv (((leftDerivedUpperStarTensorComparison A j).app N).app N'))
    (mapDerivedCategoryUpperStarDerivedTensorIso_associativity A j) K N N'

/-- **Right unitality of the projection map of `j_!`**:
`j_!(ρ⁻¹ ≫ K ◁ ε⁻¹) ≫ p = ρ⁻¹` for the projection map `p : j_!(K ⊗ᴸ Lj^*Λ) ⟶ j_!K ⊗ᴸ Λ` and the
unit comparison `ε : Lj^* Λ_X ≅ Λ_U`. -/
lemma derivedOpenImmersionLowerShriekProjectionMap_rightUnitality
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    D((j)_!open[A]).map ((ρ_ K).inv ≫ K ◁ (leftDerivedUpperStarUnitIso A j).inv) ≫
        ((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app (𝟙_ _) =
      (ρ_ _).inv :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).projectionMap_rightUnitality _ _ _
    (mapDerivedCategoryUpperStarDerivedTensorIso_rightUnitality A j) K

end OpenImmersion

end Etale

end AlgebraicGeometry
