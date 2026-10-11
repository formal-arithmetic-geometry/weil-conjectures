/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapAssoc
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection

/-!
# Associativity of the projection formula

## Main results

- `AlgebraicGeometry.Etale.mapDerivedCategoryUpperStarDerivedTensorIso_assoc`: the comparison
  `j^*X ⊗ᴸ Lj^*M ≅ j^*(X ⊗ᴸ M)` for an open immersion `j` is compatible with the monoidal
  structure of `Lj^*`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable [Etale.UpperStarPreservesFlat A] {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The comparison `j^*X ⊗ᴸ Lj^*M ≅ j^*(X ⊗ᴸ M)` is compatible with the monoidal structure of
`Lj^*`. -/
lemma mapDerivedCategoryUpperStarDerivedTensorIso_assoc
    (K M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarMonoidal A j
    (α_ (D((j)^*[A]).obj K) (L((j)^*[A]).obj M) (L((j)^*[A]).obj M')).hom ≫
        D((j)^*[A]).obj K ◁ μ L((j)^*[A]) M M' ≫
          ((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app K).app (M ⊗ M') ≫
            D((j)^*[A]).map (α_ K M M').inv =
      ((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app K).app M ▷
          L((j)^*[A]).obj M' ≫
        ((mapDerivedCategoryUpperStarDerivedTensorIso A j).hom.app (K ⊗ M)).app M' := by
  let := leftDerivedUpperStarMonoidal A j
  have hμ (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
      ((leftDerivedUpperStarTensorNatIso A j).inv.app K).app M = μ L((j)^*[A]) K M := by
    rw [← cancel_mono (Functor.OplaxMonoidal.δ L((j)^*[A]) K M), Functor.Monoidal.μ_δ]
    exact congr_app (congr_app (leftDerivedUpperStarTensorNatIso A j).inv_hom_id K) M
  have h₁ (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
      (((((Functor.whiskeringLeft₂ _).mapIso
        (leftDerivedUpperStarIsoMapDerivedCategory A j).symm).hom.app
        L((j)^*[A])).app (-⊗ᴸ-(U)[A])).app K).app M =
        (leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app K ▷ L((j)^*[A]).obj M := rfl
  have h₂ (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
      (((Functor.postcompose₂.mapIso (leftDerivedUpperStarIsoMapDerivedCategory A j)).hom.app
        (-⊗ᴸ-(X)[A])).app K).app M =
        (leftDerivedUpperStarIsoMapDerivedCategory A j).hom.app (K ⊗ M) := rfl
  simp only [mapDerivedCategoryUpperStarDerivedTensorIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.app_hom, Iso.symm_hom, hμ, h₁, h₂, Category.assoc, comp_whiskerRight]
  rw [← (leftDerivedUpperStarIsoMapDerivedCategory A j).hom.naturality,
    ← comp_whiskerRight_assoc ((leftDerivedUpperStarIsoMapDerivedCategory A j).hom.app _),
    Iso.hom_inv_id_app, id_whiskerRight, Category.id_comp, whisker_exchange_assoc,
    ← associator_naturality_left_assoc, Functor.LaxMonoidal.associativity_inv_assoc,
    Iso.hom_inv_id_assoc]

/-- The projection map `Rp_* M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^* L)` is compatible with the associators. -/
lemma rightDerivedLowerStarProjectionMap_assoc {Y Z : Scheme.{u}}
    (p : Z ⟶ Y) (M : DerivedCategory (Sheaf Z.smallEtaleTopology A))
    (L L' : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarOplaxMonoidal A p
    ((rightDerivedLowerStarProjectionMap A p).app M).app (L ⊗ L') ≫
        R((p)_*[A]).map (M ◁ Functor.OplaxMonoidal.δ L((p)^*[A]) L L') ≫
          R((p)_*[A]).map (α_ M (L((p)^*[A]).obj L) (L((p)^*[A]).obj L')).inv =
      (α_ (R((p)_*[A]).obj M) L L').inv ≫
        (((rightDerivedLowerStarProjectionMap A p).app M).app L ▷ L') ≫
          ((rightDerivedLowerStarProjectionMap A p).app (M ⊗ L((p)^*[A]).obj L)).app L' :=
  letI := leftDerivedUpperStarOplaxMonoidal A p
  (derivedUpperStarLowerStarAdjunction A p).rightAdjointProjectionMap_assoc M L L'

/-- The projection map `j_!(K ⊗ᴸ Lj^*M) ⟶ j_!K ⊗ᴸ M` of an open immersion is compatible with the
associators. -/
lemma derivedOpenImmersionLowerShriekProjectionMap_assoc
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (M M' : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarMonoidal A j
    D((j)_!open[A]).map (α_ K (L((j)^*[A]).obj M) (L((j)^*[A]).obj M')).hom ≫
        D((j)_!open[A]).map (K ◁ μ L((j)^*[A]) M M') ≫
          ((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app (M ⊗ M') ≫
            (α_ (D((j)_!open[A]).obj K) M M').inv =
      ((derivedOpenImmersionLowerShriekProjectionMap A j).app (K ⊗ L((j)^*[A]).obj M)).app M' ≫
        ((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app M ▷ M' :=
  letI := leftDerivedUpperStarMonoidal A j
  (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).projectionMap_assoc L((j)^*[A])
    (mapDerivedCategoryUpperStarDerivedTensorIso A j).hom
    (mapDerivedCategoryUpperStarDerivedTensorIso_assoc A j) K M M'

section Compactification

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

/-- The projection map `Rf_!(c) M ⊗ᴸ L ⟶ Rf_!(c)(M ⊗ᴸ Lf^* L)` is compatible with the
associators. -/
theorem projectionMapOfCompactification_assoc (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L L' : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarOplaxMonoidal A f
    ((projectionMapOfCompactification A c).app M).app (L ⊗ L') ≫
        (Rf_!(c)[A]).map (M ◁ Functor.OplaxMonoidal.δ L((f)^*[A]) L L') ≫
          (Rf_!(c)[A]).map (α_ M (L((f)^*[A]).obj L) (L((f)^*[A]).obj L')).inv =
      (α_ ((Rf_!(c)[A]).obj M) L L').inv ≫
        (((projectionMapOfCompactification A c).app M).app L ▷ L') ≫
          ((projectionMapOfCompactification A c).app (M ⊗ L((f)^*[A]).obj L)).app L' := by
  letI := leftDerivedUpperStarOplaxMonoidal A f
  simp only [projectionMapOfCompactification_app_app]
  trace_state
  sorry

end Compactification

end Etale

end AlgebraicGeometry
