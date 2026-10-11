/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionComp
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Unit

/-!
# Monoidal coherence of the ingredients of the projection map of `Rf_!`

The projection map `PF_c : Rf_!(c)K ⊗ᴸ L ⟶ Rf_!(c)(K ⊗ᴸ Lf^*L)` of a compactification
`c = (X ⟶[i] Z ⟶[g] Y)` (`AlgebraicGeometry.Etale.projectionMapOfCompactification`) is assembled
from the tensor comparisons of the derived pullbacks, the projection map of `Rg_*` and the
projection formula for the extension by zero `i_!`. We prove that these ingredients are
associative and unital, and compatible with each other; the coherence of `PF_c` and of the
mixed-support cup product is deduced from these facts in
`WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence`.

## Main statements

- `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_associativity`,
  `AlgebraicGeometry.Etale.leftDerivedUpperStarTensorComparison_rightUnitor_hom`: the
  associativity and right unitality of the tensor comparison of `Lg^*`.
- `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap_associativity`,
  `AlgebraicGeometry.Etale.rightDerivedLowerStarProjectionMap_rightUnitality`: associativity and
  unitality of the projection map of `Rp_*`.
- `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso_inv_associativity`,
  `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso_inv_rightUnitality`:
  associativity and unitality of the projection formula `j_!K ⊗ᴸ M ≅ j_!(K ⊗ᴸ Lj^*M)`.
- `AlgebraicGeometry.Etale.derivedOpenImmersionLowerShriekProjectionIso_inv_comp_toLowerStar`:
  the projection formula for `j_!` and the projection map of `Rj_*` agree through `j_! ⟶ Rj_*`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarCompactificationIso_hom_app_tensor`,
  `AlgebraicGeometry.Etale.leftDerivedUpperStarCompactificationIso_hom_app_unit`: the isomorphism
  `Lg^* ⋙ Li^* ≅ Lf^*` of a compactification is monoidal.
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
section LowerStar

variable {X Y : Scheme.{u}} (p : X ⟶ Y)

/-- **Associativity of the projection map of `Rp_*`**: the projection map
`π : Rp_*M ⊗ᴸ L ⟶ Rp_*(M ⊗ᴸ Lp^*L)` satisfies `(π ▷ L') ≫ π ≫ Rp_*(α) = α ≫ π ≫ Rp_*(M ◁ μ)`,
for the tensor comparison `μ` of `Lp^*`. -/
@[reassoc]
lemma rightDerivedLowerStarProjectionMap_associativity
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (L L' : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    ((rightDerivedLowerStarProjectionMap A p).app M).app L ▷ L' ≫
        ((rightDerivedLowerStarProjectionMap A p).app (M ⊗ L((p)^*[A]).obj L)).app L' ≫
        R((p)_*[A]).map (α_ _ _ _).hom =
      (α_ _ _ _).hom ≫ ((rightDerivedLowerStarProjectionMap A p).app M).app (L ⊗ L') ≫
        R((p)_*[A]).map (M ◁ ((leftDerivedUpperStarTensorComparison A p).app L).app L') :=
  (derivedUpperStarLowerStarAdjunction A p).rightAdjointProjectionMap_associativity _
    (leftDerivedUpperStarTensorComparison_associativity A p) M L L'

/-- **Right unitality of the projection map of `Rp_*`**:
`π ≫ Rp_*(M ◁ ε) ≫ Rp_*(ρ) = ρ` for the projection map `π : Rp_*M ⊗ᴸ Λ ⟶ Rp_*(M ⊗ᴸ Lp^*Λ)` and
the unit comparison `ε : Lp^* Λ_Y ≅ Λ_X`. -/
lemma rightDerivedLowerStarProjectionMap_rightUnitality
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((rightDerivedLowerStarProjectionMap A p).app M).app (𝟙_ _) ≫
        R((p)_*[A]).map (M ◁ (leftDerivedUpperStarUnitIso A p).hom) ≫
        R((p)_*[A]).map (ρ_ M).hom =
      (ρ_ _).hom :=
  (derivedUpperStarLowerStarAdjunction A p).rightAdjointProjectionMap_rightUnitality _ _
    (leftDerivedUpperStarTensorComparison_rightUnitor_hom A p) M

end LowerStar

section Compactification

variable {X Y Z : Scheme.{u}}

omit [Etale.UpperStarPreservesFlat A] in
lemma leftDerivedUpperStarComp_symm_trans_eqToIso (g₁ : X ⟶ Z) (g₂ : Z ⟶ Y) (f : X ⟶ Y)
    (h : f = g₁ ≫ g₂) :
    (leftDerivedUpperStarComp A g₁ g₂).symm ≪≫
        eqToIso (congrArg (fun h ↦ L((h)^*[A])) h.symm) =
      (leftDerivedUpperStarComp A g₁ g₂ f h).symm := by
  subst h
  ext
  simp

variable {f : X ⟶ Y} (c : Compactification f)

omit [Etale.UpperStarPreservesFlat A] in
/-- The isomorphism `Lg^* ⋙ Li^* ≅ Lf^*` of a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f` is
the inverse of the composition isomorphism `Lf^* ≅ Lg^* ⋙ Li^*` along `f = i ≫ g`. -/
lemma leftDerivedUpperStarCompactificationIso_eq :
    leftDerivedUpperStarCompactificationIso A c =
      (leftDerivedUpperStarComp A c.i c.g f c.comm).symm :=
  leftDerivedUpperStarComp_symm_trans_eqToIso A c.i c.g f c.comm

/-- The isomorphism `Lg^* ⋙ Li^* ≅ Lf^*` of a compactification is monoidal: it commutes with the
tensor comparisons. -/
@[reassoc]
lemma leftDerivedUpperStarCompactificationIso_hom_app_tensor
    (L L' : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (leftDerivedUpperStarCompactificationIso A c).hom.app (L ⊗ L') ≫
        ((leftDerivedUpperStarTensorComparison A f).app L).app L' =
      L((c.i)^*[A]).map (((leftDerivedUpperStarTensorComparison A c.g).app L).app L') ≫
        ((leftDerivedUpperStarTensorComparison A c.i).app _).app _ ≫
        ((leftDerivedUpperStarCompactificationIso A c).hom.app L ⊗ₘ
          (leftDerivedUpperStarCompactificationIso A c).hom.app L') := by
  rw [leftDerivedUpperStarCompactificationIso_eq, Iso.symm_hom,
    ← cancel_mono ((leftDerivedUpperStarComp A c.i c.g f c.comm).hom.app L ⊗ₘ
      (leftDerivedUpperStarComp A c.i c.g f c.comm).hom.app L'),
    Category.assoc, leftDerivedUpperStarTensorComparison_comp, Iso.inv_hom_id_app_assoc,
    Category.assoc, Category.assoc, tensorHom_comp_tensorHom, Iso.inv_hom_id_app,
    Iso.inv_hom_id_app]
  erw [id_tensorHom_id, Category.comp_id]

/-- The isomorphism `Lg^* ⋙ Li^* ≅ Lf^*` of a compactification commutes with the unit
comparisons. -/
@[reassoc]
lemma leftDerivedUpperStarCompactificationIso_hom_app_unit :
    (leftDerivedUpperStarCompactificationIso A c).hom.app (𝟙_ _) ≫
        (leftDerivedUpperStarUnitIso A f).hom =
      L((c.i)^*[A]).map (leftDerivedUpperStarUnitIso A c.g).hom ≫
        (leftDerivedUpperStarUnitIso A c.i).hom := by
  suffices key : (leftDerivedUpperStarUnitIso A f).hom =
      (leftDerivedUpperStarCompactificationIso A c).inv.app (𝟙_ _) ≫
        L((c.i)^*[A]).map (leftDerivedUpperStarUnitIso A c.g).hom ≫
        (leftDerivedUpperStarUnitIso A c.i).hom by
    rw [key, Iso.hom_inv_id_app_assoc]
  refine Functor.eq_of_leftUnitality (F := L((f)^*[A]))
    (((leftDerivedUpperStarTensorComparison A f).app (𝟙_ _)).app (𝟙_ _)) _ _
    (leftDerivedUpperStarTensorComparison_leftUnitor_hom A f _) ?_
  have h₁ : ((leftDerivedUpperStarTensorComparison A f).app (𝟙_ _)).app (𝟙_ _) =
      (leftDerivedUpperStarCompactificationIso A c).inv.app (𝟙_ _ ⊗ 𝟙_ _) ≫ L((c.i)^*[A]).map
        (((leftDerivedUpperStarTensorComparison A c.g).app (𝟙_ _)).app (𝟙_ _)) ≫
        ((leftDerivedUpperStarTensorComparison A c.i).app _).app _ ≫
        ((leftDerivedUpperStarCompactificationIso A c).hom.app (𝟙_ _) ⊗ₘ
          (leftDerivedUpperStarCompactificationIso A c).hom.app (𝟙_ _)) :=
    (Iso.eq_inv_comp ((leftDerivedUpperStarCompactificationIso A c).app (𝟙_ _ ⊗ 𝟙_ _))).2
      (leftDerivedUpperStarCompactificationIso_hom_app_tensor A c _ _)
  have h₂ := NatTrans.congr_app ((leftDerivedUpperStarTensorComparison A c.i).naturality
    (leftDerivedUpperStarUnitIso A c.g).hom) (L((c.g)^*[A]).obj (𝟙_ _))
  dsimp at h₂
  have h₃ := leftDerivedUpperStarTensorComparison_leftUnitor_hom A c.i
    (L((c.g)^*[A]).obj (𝟙_ _))
  have h₄ := leftDerivedUpperStarTensorComparison_leftUnitor_hom A c.g (𝟙_ _)
  have h₅ := (leftDerivedUpperStarCompactificationIso A c).hom.naturality (λ_ (𝟙_ _)).hom
  dsimp at h₅
  rw [h₁, Category.assoc, Category.assoc, Category.assoc, tensorHom_def_assoc]
  erw [whisker_exchange_assoc]
  rw [← comp_whiskerRight_assoc, Iso.hom_inv_id_app_assoc, leftUnitor_naturality,
    comp_whiskerRight_assoc]
  erw [← reassoc_of% h₂]
  rw [← Functor.map_comp_assoc]
  erw [reassoc_of% h₃]
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc]
  erw [h₄, h₅, Iso.inv_hom_id_app_assoc]

end Compactification
section OpenImmersionInverse
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [X.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]

@[reassoc]
lemma derivedOpenImmersionLowerShriekProjectionIso_inv_naturality_left
    {K K' : DerivedCategory (Sheaf U.smallEtaleTopology A)} (x : K ⟶ K')
    (N : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    D((j)_!open[A]).map x ▷ N ≫
        ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K').app N =
      ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app N ≫
        D((j)_!open[A]).map (x ▷ L((j)^*[A]).obj N) :=
  NatTrans.congr_app ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.naturality x) N

@[reassoc]
lemma derivedOpenImmersionLowerShriekProjectionIso_inv_naturality_right
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A))
    {N N' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (y : N ⟶ N') :
    D((j)_!open[A]).obj K ◁ y ≫
        ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app N' =
      ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app N ≫
        D((j)_!open[A]).map (K ◁ L((j)^*[A]).map y) :=
  ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).naturality y

@[reassoc]
lemma derivedOpenImmersionLowerShriekProjectionIso_inv_associativity
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (N N' : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app N ▷ N' ≫
        ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app
          (K ⊗ L((j)^*[A]).obj N)).app N' =
      (α_ _ _ _).hom ≫ ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app
          (N ⊗ N') ≫
        D((j)_!open[A]).map (K ◁ ((leftDerivedUpperStarTensorComparison A j).app N).app N' ≫
          (α_ _ _ _).inv) := by
  have h := derivedOpenImmersionLowerShriekProjectionMap_associativity A j K N N'
  rw [← derivedOpenImmersionLowerShriekProjectionIso_hom] at h
  rw [← cancel_mono (((derivedOpenImmersionLowerShriekProjectionIso A j).hom.app
      (K ⊗ L((j)^*[A]).obj N)).app N' ≫
      ((derivedOpenImmersionLowerShriekProjectionIso A j).hom.app K).app N ▷ N' ≫
      (α_ _ _ _).hom)]
  simp only [Category.assoc]
  conv_rhs => rw [h]
  simp only [Iso.inv_hom_id_app_app_assoc, ← comp_whiskerRight_assoc,
    Iso.inv_hom_id_app_app, id_whiskerRight, Category.id_comp, ← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← whiskerLeft_comp, IsIso.hom_inv_id,
    whiskerLeft_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app_app, Category.comp_id]

lemma derivedOpenImmersionLowerShriekProjectionIso_inv_rightUnitality
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app (𝟙_ _) ≫
        D((j)_!open[A]).map (K ◁ (leftDerivedUpperStarUnitIso A j).hom ≫ (ρ_ K).hom) =
      (ρ_ _).hom := by
  have h := derivedOpenImmersionLowerShriekProjectionMap_rightUnitality A j K
  rw [← derivedOpenImmersionLowerShriekProjectionIso_hom] at h
  rw [← cancel_epi (ρ_ (D((j)_!open[A]).obj K)).inv, Iso.inv_hom_id, ← h]
  simp only [Category.assoc, Iso.hom_inv_id_app_app_assoc, ← CategoryTheory.Functor.map_comp,
    ← whiskerLeft_comp_assoc, Iso.inv_hom_id, whiskerLeft_id, Category.id_comp,
    Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id]

omit [Etale.UpperStarPreservesFlat A] in
/-- The transpose along `Lj^* ⊣ Rj_*` of the comparison `j_!K ⟶ Rj_*K`. -/
lemma derivedUpperStarLowerStarAdjunction_homEquiv_symm_lowerShriekToLowerStar
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    ((derivedUpperStarLowerStarAdjunction A j).homEquiv _ _).symm
        ((derivedOpenImmersionLowerShriekToLowerStar A j).app K) =
      (leftDerivedUpperStarIsoMapDerivedCategory A j).hom.app _ ≫
        inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app K) := by
  rw [Equiv.symm_apply_eq, Adjunction.homEquiv_unit]
  simp only [derivedOpenImmersionLowerShriekToLowerStar, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    NatIso.isIso_inv_app, Category.id_comp, mapDerivedUpperStarLowerStarAdjunction_eq]
  dsimp [Adjunction.ofNatIsoLeft]
  simp only [Category.assoc, CategoryTheory.Functor.map_comp]

/-- The projection map of `j_!` and that of `Rj_*` agree through the comparison
`j_! ⟶ Rj_*`. -/
@[reassoc]
lemma derivedOpenImmersionLowerShriekProjectionIso_inv_comp_toLowerStar
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A))
    (N : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedOpenImmersionLowerShriekProjectionIso A j).inv.app K).app N ≫
        (derivedOpenImmersionLowerShriekToLowerStar A j).app (K ⊗ L((j)^*[A]).obj N) =
      (derivedOpenImmersionLowerShriekToLowerStar A j).app K ▷ N ≫
        ((rightDerivedLowerStarProjectionMap A j).app K).app N := by
  have key :
      L((j)^*[A]).map (((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app N) ≫
        ((leftDerivedUpperStarTensorComparison A j).app _).app N ≫
        ((leftDerivedUpperStarIsoMapDerivedCategory A j).hom.app _ ≫
          inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app K)) ▷
            L((j)^*[A]).obj N =
      (leftDerivedUpperStarIsoMapDerivedCategory A j).hom.app _ ≫
        inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app
          (K ⊗ L((j)^*[A]).obj N)) := by
    rw [← cancel_epi ((leftDerivedUpperStarIsoMapDerivedCategory A j).inv.app
      (D((j)_!open[A]).obj (K ⊗ L((j)^*[A]).obj N))), Iso.inv_hom_id_app_assoc]
    erw [← (leftDerivedUpperStarIsoMapDerivedCategory A j).inv.naturality_assoc]
    rw [← cancel_epi ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app _),
      IsIso.hom_inv_id]
    erw [Adjunction.unit_app_comp_map_projectionMap_assoc]
    rw [mapDerivedCategoryUpperStarDerivedTensorIso_hom_app_app]
    simp only [Category.assoc]
    erw [Iso.hom_inv_id_app_assoc]
    rw [IsIso.inv_hom_id_assoc]
    simp only [← comp_whiskerRight]
    rw [Iso.inv_hom_id_app_assoc, IsIso.hom_inv_id, id_whiskerRight]
    rfl
  apply ((derivedUpperStarLowerStarAdjunction A j).homEquiv _ _).symm.injective
  erw [Adjunction.homEquiv_naturality_left_symm,
    derivedUpperStarLowerStarAdjunction_homEquiv_symm_lowerShriekToLowerStar,
    Adjunction.homEquiv_naturality_left_symm, homEquiv_symm_rightDerivedLowerStarProjectionMap,
    ← cancel_epi (L((j)^*[A]).map
      (((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app N)),
    ← CategoryTheory.Functor.map_comp_assoc]
  rw [← derivedOpenImmersionLowerShriekProjectionIso_hom, Iso.hom_inv_id_app_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← key]
  have hs : L((j)^*[A]).map ((derivedOpenImmersionLowerShriekToLowerStar A j).app K) ≫
      (derivedUpperStarLowerStarAdjunction A j).counit.app K =
        (leftDerivedUpperStarIsoMapDerivedCategory A j).hom.app _ ≫
          inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app K) := by
    rw [← derivedUpperStarLowerStarAdjunction_homEquiv_symm_lowerShriekToLowerStar,
      Adjunction.homEquiv_counit]
  have hn := NatTrans.congr_app ((leftDerivedUpperStarTensorComparison A j).naturality
    ((derivedOpenImmersionLowerShriekToLowerStar A j).app K)) N
  dsimp at hn
  congr 1
  erw [reassoc_of% hn]
  rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp]
  erw [hs]
  rfl

end OpenImmersionInverse

end Etale

end AlgebraicGeometry
