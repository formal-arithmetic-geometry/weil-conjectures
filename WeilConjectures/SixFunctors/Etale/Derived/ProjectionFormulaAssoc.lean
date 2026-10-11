/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapAssoc
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection

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

end Etale

end AlgebraicGeometry
