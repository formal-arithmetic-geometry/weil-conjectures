/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateTransport
public import WeilConjectures.CategoryTheory.Monoidal.ProjectionMateDualizable
public import WeilConjectures.SixFunctors.Etale.Derived.CupProductCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction

/-!
# Tensoring with a dualizable object and the right adjoint of `Rf_!`

Let `f : X ⟶ Y` be a morphism with a compactification `c = (X ⟶[i] Z ⟶[g] Y)`, let `N_Y` be a
dualizable object of `D(Y_ét)` and `a : Lf^* N_Y ≅ N_X`. The comparison
`q : Rf_! K ⊗ᴸ N_Y ⟶ Rf_!(K ⊗ᴸ N_X)` (the projection map followed by `a`,
`AlgebraicGeometry.Etale.rightDerivedLowerShriekDerivedTensorRightMap`) is an isomorphism, and for
any right adjoint `G` of `Rf_!` the mate `G M ⊗ᴸ N_X ⟶ G (M ⊗ᴸ N_Y)` of `q⁻¹` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_mateEquiv_app_inv_rightDerivedLowerShriekDerivedTensorRightMap`):
the projection map of `Rf_!` is a module structure over `Lf^*`.

We also describe `q` through the two pieces of the compactification: the comparison of `Rg_*` with
`- ⊗ᴸ N` is the mate of the comparison of `Lg^*` with `- ⊗ᴸ N`
(`AlgebraicGeometry.Etale.mateEquiv_leftDerivedUpperStarDerivedTensorRightIso_hom`), the
projection map of the extension by zero `D(j_!)` is the left adjoint mate of the comparison of
`Lj^*` with `- ⊗ᴸ N`
(`AlgebraicGeometry.Etale.mateEquiv_symm_leftDerivedUpperStarDerivedTensorRightIso_inv_app`), and
`q` is assembled from them
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekDerivedTensorRightMap_app_comp_map`).

## Main results

- `AlgebraicGeometry.Etale.mateEquiv_leftDerivedUpperStarDerivedTensorRightIso_hom`
- `AlgebraicGeometry.Etale.mateEquiv_symm_leftDerivedUpperStarDerivedTensorRightIso_inv_app`
- `AlgebraicGeometry.Etale.rightDerivedLowerShriekDerivedTensorRightMap_app_comp_map`
- `AlgebraicGeometry.Etale.isIso_mateEquiv_app_inv_rightDerivedLowerShriekDerivedTensorRightMap`
-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]

section Basic

variable {X : Scheme.{u}}

omit [Etale.UpperStarPreservesFlat A] in
/-- Tensoring on the right with `N` acts on morphisms by whiskering. -/
lemma derivedTensorRight_map (N : DerivedCategory (Sheaf X.smallEtaleTopology A))
    {K K' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (φ : K ⟶ K') :
    (derivedTensorRight A X N).map φ = φ ▷ N :=
  rfl

variable {Y : Scheme.{u}}

/-- The inverse of the comparison `Lf^*(L ⊗ᴸ N_Y) ≅ Lf^* L ⊗ᴸ N_X` of
`AlgebraicGeometry.Etale.leftDerivedUpperStarDerivedTensorRightIso`. -/
lemma leftDerivedUpperStarDerivedTensorRightIso_inv_app (f : X ⟶ Y)
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ≅ NX)
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (leftDerivedUpperStarDerivedTensorRightIso A f a).inv.app L =
      L((f)^*[A]).obj L ◁ a.inv ≫ ((leftDerivedUpperStarTensorNatIso A f).inv.app L).app NY :=
  rfl

end Basic

section LowerStar

variable {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- The comparison `Rg_* M ⊗ᴸ N_Y ⟶ Rg_*(M ⊗ᴸ N_Z)` of
`AlgebraicGeometry.Etale.rightDerivedLowerStarDerivedTensorRightMap` is the mate along
`Lg^* ⊣ Rg_*` of the comparison `Lg^*(K ⊗ᴸ N_Y) ≅ Lg^* K ⊗ᴸ N_Z`. -/
lemma mateEquiv_leftDerivedUpperStarDerivedTensorRightIso_hom
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NZ : DerivedCategory (Sheaf Z.smallEtaleTopology A)} (a : L((g)^*[A]).obj NY ≅ NZ) :
    mateEquiv (derivedUpperStarLowerStarAdjunction A g) (derivedUpperStarLowerStarAdjunction A g)
        (leftDerivedUpperStarDerivedTensorRightIso A g a).hom =
      rightDerivedLowerStarDerivedTensorRightMap A g a.hom := by
  ext M
  have h := Adjunction.mateEquiv_app_comp_map_eq_rightAdjointProjectionMap
    (derivedUpperStarLowerStarAdjunction A g) (leftDerivedUpperStarTensorComparison A g) a.hom
    (Iso.refl (derivedTensorRight A Y NY)) (Iso.refl (derivedTensorRight A Z NZ))
    (leftDerivedUpperStarDerivedTensorRightIso A g a).hom (fun X ↦ by
      rw [leftDerivedUpperStarDerivedTensorRightIso_hom_app]
      simp [derivedTensor_obj_map]) M
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

end LowerStar

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- For an open immersion `j`, the extension by zero `D(j_!)` is left adjoint to the derived
pullback `Lj^*`: the adjunction `D(j_!) ⊣ D(j^*)` transported along `Lj^* ≅ D(j^*)`. -/
noncomputable def openImmersionLowerShriekLeftDerivedUpperStarAdjunction :
    D((j)_!open[A]) ⊣ L((j)^*[A]) :=
  (derivedOpenImmersionLowerShriekUpperStarAdjunction A j).ofNatIsoRight
    (leftDerivedUpperStarIsoMapDerivedCategory A j).symm

/-- The projection map `j_!(K ⊗ᴸ Lj^* N_X) ⟶ j_!K ⊗ᴸ N_X` of the extension by zero, preceded by
`a⁻¹ : N_U ≅ Lj^* N_X`, is the left adjoint mate along `D(j_!) ⊣ Lj^*` of the inverse of the
comparison `Lj^*(M ⊗ᴸ N_X) ≅ Lj^* M ⊗ᴸ N_U`. -/
lemma mateEquiv_symm_leftDerivedUpperStarDerivedTensorRightIso_inv_app
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {NU : DerivedCategory (Sheaf U.smallEtaleTopology A)} (a : L((j)^*[A]).obj NX ≅ NU)
    (K : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    ((mateEquiv (openImmersionLowerShriekLeftDerivedUpperStarAdjunction A j)
        (openImmersionLowerShriekLeftDerivedUpperStarAdjunction A j)).symm
        (leftDerivedUpperStarDerivedTensorRightIso A j a).inv).app K =
      D((j)_!open[A]).map (K ◁ a.inv) ≫
        ((derivedOpenImmersionLowerShriekProjectionMap A j).app K).app NX := by
  apply ((openImmersionLowerShriekLeftDerivedUpperStarAdjunction A j).homEquiv _ _).injective
  have h₁ := unit_mateEquiv_symm (openImmersionLowerShriekLeftDerivedUpperStarAdjunction A j)
    (openImmersionLowerShriekLeftDerivedUpperStarAdjunction A j)
    (leftDerivedUpperStarDerivedTensorRightIso A j a).inv K
  dsimp only [Functor.id_obj] at h₁
  rw [Adjunction.homEquiv_unit, ← h₁]
  simp only [Adjunction.homEquiv_naturality_left,
    openImmersionLowerShriekLeftDerivedUpperStarAdjunction, Adjunction.homEquiv_ofNatIsoRight_apply,
    derivedOpenImmersionLowerShriekProjectionMap, Adjunction.projectionMap_app_app]
  erw [Equiv.apply_symm_apply]
  simp only [Functor.comp_obj, Adjunction.ofNatIsoRight_unit, Iso.symm_hom, NatTrans.comp_app,
    Functor.id_obj, Functor.whiskerLeft_app, derivedTensorRight_map, comp_whiskerRight,
    leftDerivedUpperStarDerivedTensorRightIso_inv_app, Functor.postcompose₂_obj_obj_obj_obj, assoc,
    Adjunction.projectionMapTranspose, mapDerivedCategoryUpperStarDerivedTensorIso,
    Functor.mapIso_symm, Iso.trans_hom, Iso.app_hom, Functor.mapIso_inv, Functor.mapIso_hom,
    Functor.map_comp, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.whiskeringLeft₂_map_app_app_app_app, derivedTensor_map_app,
    Functor.whiskeringLeft₂_obj_obj_map_app_app, Functor.postcompose₂_map_app_app_app]
  erw [Iso.hom_inv_id_app]
  rw [Category.comp_id, whisker_exchange_assoc, whisker_exchange_assoc]

end OpenImmersion

section Compactification

variable {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/-- For a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f` and isomorphisms
`a_g : Lg^* N_Y ≅ N_Z` and `a_i : Li^* N_Z ≅ N_X`, the induced isomorphism `Lf^* N_Y ≅ N_X`. -/
noncomputable def compactificationUpperStarIso
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NZ : DerivedCategory (Sheaf c.Z.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (ag : L((c.g)^*[A]).obj NY ≅ NZ) (ai : L((c.i)^*[A]).obj NZ ≅ NX) :
    L((f)^*[A]).obj NY ≅ NX :=
  ((leftDerivedUpperStarCompactificationIso A c).app NY).symm ≪≫ L((c.i)^*[A]).mapIso ag ≪≫ ai

/-- **The comparison of `Rf_!` with `- ⊗ᴸ N` through the compactification.** The comparison
`Rf_! K ⊗ᴸ N_Y ⟶ Rf_!(K ⊗ᴸ N_X)` followed by `Rg_*` of the left adjoint mate
`i_!(K ⊗ᴸ N_X) ⟶ i_! K ⊗ᴸ N_Z` of the comparison of `Li^*` with `- ⊗ᴸ N` is the comparison
`Rg_*(i_! K) ⊗ᴸ N_Y ⟶ Rg_*(i_! K ⊗ᴸ N_Z)` of `Rg_*` with `- ⊗ᴸ N`. -/
theorem rightDerivedLowerShriekDerivedTensorRightMap_app_comp_map
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NZ : DerivedCategory (Sheaf c.Z.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (ag : L((c.g)^*[A]).obj NY ≅ NZ) (ai : L((c.i)^*[A]).obj NZ ≅ NX)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (rightDerivedLowerShriekDerivedTensorRightMap A c
        (compactificationUpperStarIso A c ag ai).hom).app K ≫
      R((c.g)_*[A]).map
        (((mateEquiv (openImmersionLowerShriekLeftDerivedUpperStarAdjunction A c.i)
          (openImmersionLowerShriekLeftDerivedUpperStarAdjunction A c.i)).symm
          (leftDerivedUpperStarDerivedTensorRightIso A c.i ai).inv).app K) =
      (rightDerivedLowerStarDerivedTensorRightMap A c.g ag.hom).app
        (D((c.i)_!open[A]).obj K) := by
  rw [rightDerivedLowerShriekDerivedTensorRightMap_app, projectionMapOfCompactification_app_app,
    mateEquiv_symm_leftDerivedUpperStarDerivedTensorRightIso_inv_app,
    ← derivedOpenImmersionLowerShriekProjectionIso_hom]
  dsimp only [rightDerivedLowerStarDerivedTensorRightMap, compactificationUpperStarIso]
  simp only [Category.assoc, Functor.comp_map, ← Functor.map_comp]
  congr 2
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, derivedTensor_obj_map,
    MonoidalCategory.whiskerLeft_comp, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
    Iso.hom_inv_id_app_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← reassoc_of% (derivedOpenImmersionLowerShriekProjectionIso_inv_naturality_right A c.i K
    ag.hom), Iso.inv_hom_id_app_app]
  exact Category.comp_id _


end Compactification

section Monoidal

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The unit of the monoidal structure of `Lf^*` is the inverse of the identification
`Lf^* Λ_Y ≅ Λ_X`. -/
lemma leftDerivedUpperStarMonoidal_ε :
    letI := leftDerivedUpperStarMonoidal A f
    Functor.LaxMonoidal.ε L((f)^*[A]) = (leftDerivedUpperStarUnitIso A f).inv := by
  let := leftDerivedUpperStarMonoidal A f
  have hη : Functor.OplaxMonoidal.η L((f)^*[A]) = (leftDerivedUpperStarUnitIso A f).hom :=
    leftDerivedUpperStarOplaxMonoidal_η A f
  rw [← cancel_mono (leftDerivedUpperStarUnitIso A f).hom, Iso.inv_hom_id, ← hη,
    Functor.Monoidal.ε_η]

/-- The tensor structure of the monoidal structure of `Lf^*` is the inverse of the tensor
comparison `Lf^*(B ⊗ᴸ C) ⟶ Lf^* B ⊗ᴸ Lf^* C`. -/
lemma leftDerivedUpperStarMonoidal_μ (B C : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarMonoidal A f
    Functor.LaxMonoidal.μ L((f)^*[A]) B C =
      inv (((leftDerivedUpperStarTensorComparison A f).app B).app C) := by
  let := leftDerivedUpperStarMonoidal A f
  have hδ : Functor.OplaxMonoidal.δ L((f)^*[A]) B C =
      ((leftDerivedUpperStarTensorComparison A f).app B).app C := rfl
  rw [← cancel_mono (((leftDerivedUpperStarTensorComparison A f).app B).app C),
    IsIso.inv_hom_id, ← hδ, Functor.Monoidal.μ_δ]

variable {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {f} (c : Compactification f)

/-- **Unitality of the projection map of `Rf_!`**, in terms of the monoidal structure of
`Lf^*`: `PF_{K, Λ} = Rf_! K ⊗ᴸ Λ ≅ Rf_! K ≅ Rf_!(K ⊗ᴸ Λ) ⟶ Rf_!(K ⊗ᴸ Lf^* Λ)`. -/
lemma projectionMapOfCompactification_app_app_tensorUnit
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarMonoidal A f
    ((projectionMapOfCompactification A c).app K).app (𝟙_ _) =
      (ρ_ ((Rf_!(c)[A]).obj K)).hom ≫
        (Rf_!(c)[A]).map ((ρ_ K).inv ≫ K ◁ Functor.LaxMonoidal.ε L((f)^*[A])) := by
  let := leftDerivedUpperStarMonoidal A f
  have h := compactificationProjectionMap_rightUnitality A c K
  rw [← projectionMapOfCompactification_app_app_eq_compProjectionMap] at h
  rw [leftDerivedUpperStarMonoidal_ε]
  sorry
  rw [    ← cancel_mono ((Rf_!(c)[A]).map (K ◁ (leftDerivedUpperStarUnitIso A f).hom ≫ (ρ_ K).hom)),
    h]
  trace_state
  sorry

/-- **Associativity of the projection map of `Rf_!`**, in terms of the monoidal structure of
`Lf^*`. -/
lemma projectionMapOfCompactification_app_app_tensor
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (B C : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    letI := leftDerivedUpperStarMonoidal A f
    ((projectionMapOfCompactification A c).app K).app (B ⊗ C) =
      (α_ _ _ _).inv ≫ ((projectionMapOfCompactification A c).app K).app B ▷ C ≫
        ((projectionMapOfCompactification A c).app (K ⊗ L((f)^*[A]).obj B)).app C ≫
        (Rf_!(c)[A]).map ((α_ _ _ _).hom ≫ K ◁ Functor.LaxMonoidal.μ L((f)^*[A]) B C) := by
  let := leftDerivedUpperStarMonoidal A f
  have e := projectionMapOfCompactification_assoc A c K B C
  rw [leftDerivedUpperStarMonoidal_μ, Functor.map_comp]
  erw [reassoc_of% e]
  simp [← Functor.map_comp]

end Monoidal

end AlgebraicGeometry.Etale
