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
public import WeilConjectures.SixFunctors.Etale.Derived.TensorSheafUpperStar

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

- `leftDerivedUpperStarDerivedTensorRightIso_hom_app_comp_leftDerivedTensorRightIso_inv`
  (in the namespace `AlgebraicGeometry.Etale`): the comparison of `Lg^*` with `- ⊗ᴸ N`
  through `L(- ⊗ c) ≅ - ⊗ᴸ c`.
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

/-- Through `L(- ⊗ c) ≅ - ⊗ᴸ c`, the comparison `Lg^* L(K ⊗ c_Y) ⟶ L(Lg^* K ⊗ c_Z)` induced by an
isomorphism `κ : g^* c_Y ⟶ c_Z` of sheaves is the comparison `Lg^*(K ⊗ᴸ c_Y) ≅ Lg^* K ⊗ᴸ c_Z` of
`AlgebraicGeometry.Etale.leftDerivedUpperStarDerivedTensorRightIso`. -/
lemma leftDerivedUpperStarDerivedTensorRightIso_hom_app_comp_leftDerivedTensorRightIso_inv
    {c_Y : Sheaf Y.smallEtaleTopology A} {c_Z : Sheaf Z.smallEtaleTopology A}
    (κ : (g)^*[A].obj c_Y ⟶ c_Z) [IsIso κ] (K : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    (leftDerivedUpperStarDerivedTensorRightIso A g
        (asIso (leftDerivedUpperStarDerivedSingleMap g κ))).hom.app K ≫
        (leftDerivedTensorRightIso c_Z).inv.app (L((g)^*[A]).obj K) =
      L((g)^*[A]).map ((leftDerivedTensorRightIso c_Y).inv.app K) ≫
        (leftDerivedTensorRightUpperStarMap g κ).app K := by
  have h := leftDerivedTensorRightUpperStarMap_app_comp g κ K
  rw [leftDerivedUpperStarDerivedTensorRightIso_hom_app, asIso_hom, ← derivedTensor_obj_map,
    ← cancel_epi (L((g)^*[A]).map ((leftDerivedTensorRightIso c_Y).hom.app K)),
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.assoc, ← reassoc_of% h, Iso.hom_inv_id_app, Category.comp_id]

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

section Dualizable

variable {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
  {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)

/- The projection map of `Rf_!(c) = Rg_* ∘ i_!`, in the form of
`CategoryTheory.Adjunction.compProjectionMap`. -/
set_option quotPrecheck false in
local notation "𝚷" =>
  (derivedUpperStarLowerStarAdjunction A c.g).compProjectionMap
    (leftDerivedUpperStarTensorComparison A c.g) D((c.i)_!open[A])
    (fun K N ↦ ((derivedOpenImmersionLowerShriekProjectionIso A c.i).inv.app K).app N)
    (fun L ↦ (leftDerivedUpperStarCompactificationIso A c).hom.app L)

/-- **The right adjoint of `Rf_!` commutes with tensoring by a dualizable object.** For a
dualizable `N_Y`, an isomorphism `a : Lf^* N_Y ≅ N_X` and a right adjoint `G` of `Rf_!`, the
mate `G M ⊗ᴸ N_X ⟶ G (M ⊗ᴸ N_Y)` of the inverse of the comparison
`Rf_! K ⊗ᴸ N_Y ⟶ Rf_!(K ⊗ᴸ N_X)` is an isomorphism: the projection map of `Rf_!` is compatible
with the unit and the tensor structure of `Lf^*`, and invertible at `N_Y` and at its dual. -/
theorem isIso_mateEquiv_app_inv_rightDerivedLowerShriekDerivedTensorRightMap
    {G : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A)} (adj : Rf_!(c)[A] ⊣ G)
    {NY : DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {NX : DerivedCategory (Sheaf X.smallEtaleTopology A)} (a : L((f)^*[A]).obj NY ≅ NX)
    (hN : IsDualizable NY) [IsIso (rightDerivedLowerShriekDerivedTensorRightMap A c a.hom)]
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    IsIso ((mateEquiv adj adj (inv (rightDerivedLowerShriekDerivedTensorRightMap A c a.hom))).app
      M) := by
  let := leftDerivedUpperStarMonoidal A f
  obtain ⟨_⟩ := _root_.DerivedCategory.nonempty_braidedCategory (Sheaf Y.smallEtaleTopology A)
  obtain ⟨_⟩ := hN
  let := BraidedCategory.exactPairing_swap NY NYᘁ
  have hπ₁ (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) : IsIso (𝚷 K NY) := by
    have := hasProjectionFormulaOfCompactification_of_isDualizable A c K (L := NY)
      ⟨inferInstance⟩
    rwa [HasProjectionFormulaOfCompactification,
      projectionMapOfCompactification_app_app_eq_compProjectionMap] at this
  have hπ₂ (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) : IsIso (𝚷 K NYᘁ) := by
    have := hasProjectionFormulaOfCompactification_of_isDualizable A c K (L := NYᘁ)
      ⟨{ rightDual := NY }⟩
    rwa [HasProjectionFormulaOfCompactification,
      projectionMapOfCompactification_app_app_eq_compProjectionMap] at this
  have hη : Functor.OplaxMonoidal.η L((f)^*[A]) = (leftDerivedUpperStarUnitIso A f).hom :=
    leftDerivedUpperStarOplaxMonoidal_η A f
  refine Adjunction.isIso_mateEquiv_app_of_projection' adj (π := 𝚷)
    (fun φ N ↦ compactificationProjectionMap_naturality_left A c φ N)
    (fun K _ _ φ ↦ compactificationProjectionMap_naturality_right A c K φ)
    (fun K ↦ ?_) (fun K B C ↦ compactificationProjectionMap_associativity A c K B C)
    NYᘁ NY a _ (fun K ↦ ?_) M
  · rw [hη]
    exact compactificationProjectionMap_rightUnitality A c K
  · rw [NatIso.isIso_inv_app]
    apply IsIso.inv_eq_of_hom_inv_id
    rw [rightDerivedLowerShriekDerivedTensorRightMap_app,
      projectionMapOfCompactification_app_app_eq_compProjectionMap]
    simp only [Category.assoc, ← Functor.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
      Iso.hom_inv_id, MonoidalCategory.whiskerLeft_id]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact IsIso.hom_inv_id _

end Dualizable

end AlgebraicGeometry.Etale
