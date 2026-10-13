/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.ExtendScalars.Projection

/-!
# The derived projection map and the derived pullback

Let `S` be an `R`-algebra, `Ψ = L(S ⊗_R -)` derived extension of scalars of pro-étale sheaves and
`g : Z ⟶ Y`. Restricted back to `R`, `Ψ` is the derived tensor product with the sheaf `S_Y`
(`AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsProjection`), and the derived pullback
`Lg^*` carries `L(- ⊗ S_Y)` to `L(- ⊗ S_Z)`: the comparison `g^*(P ⊗ S_Y) ⟶ g^* P ⊗ S_Z` of
sheaves induces a natural transformation `Lg^* (L(- ⊗ S_Y) K) ⟶ L(- ⊗ S_Z) (Lg^* K)`.

We show that the transposes `Ψ (K ⊗ᴸ S_Y) ⟶ Ψ K` of the derived projection maps are compatible
with this comparison and with the commutation `Lg^* Ψ ≅ Ψ Lg^*`
(`AlgebraicGeometry.ProEtale.leftDerivedUpperStarExtendScalarsIso`). This is the input needed to
compare the base change map `Ψ (Rg_* M) ⟶ Rg_* (Ψ M)` with the projection map of `Rg_*` at
`S_Y` (blueprint `thm-trf-finite-coefficient-map`).

## Main definitions and results

- `AlgebraicGeometry.ProEtale.tensorRestrictScalarsUnitUpperStarMap`: the comparison
  `g^*(P ⊗ S_Y) ⟶ g^* P ⊗ S_Z` of sheaves.
- `AlgebraicGeometry.ProEtale.leftDerivedTensorRestrictScalarsUnitUpperStarMap`: the induced
  natural transformation `L(- ⊗ S_Y) ⋙ Lg^* ⟶ Lg^* ⋙ L(- ⊗ S_Z)`.
- `AlgebraicGeometry.ProEtale.leftDerivedSheafExtendScalarsProjection_transpose_upperStar`: the
  compatibility of the transposed derived projection maps with the derived pullback.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory HomologicalComplex Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

-- `GrothendieckTopology.W.monoidal` gives the monoidality of `W` directly; the instance going
-- through enough points of the site is tried first and makes the search time out.
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]
  {Y Z : Scheme.{u}} (g : Z ⟶ Y)

/-- The comparison `g^*(P ⊗ S_Y) ⟶ g^* P ⊗ S_Z` of pro-étale sheaves: the comonoidal structure
of the pullback followed by the identification `g^* S_Y ≅ S_Z` of
`AlgebraicGeometry.ProEtale.upperStarSheafRestrictScalarsUnitMap`. -/
noncomputable def tensorRestrictScalarsUnitUpperStarMap :
    tensorRight (sheafRestrictScalarsUnit R S Y) ⋙ ProEtale.upperStar (ModuleCat.{u + 1} R) g ⟶
      ProEtale.upperStar (ModuleCat.{u + 1} R) g ⋙
        tensorRight (sheafRestrictScalarsUnit R S Z) where
  app P := δ (ProEtale.upperStar (ModuleCat.{u + 1} R) g) P (sheafRestrictScalarsUnit R S Y) ≫
    (_ ◁ upperStarSheafRestrictScalarsUnitMap R S g)
  naturality P Q f := by
    dsimp
    rw [← δ_natural_left_assoc, Category.assoc, whisker_exchange]

/-- The transposes `S ⊗_R (P ⊗ S_Y) ⟶ S ⊗_R P` of the projection maps are compatible with the
pullback: the square
```
g^* (S ⊗_R (P ⊗ S_Y)) ──g^* π♯──▶ g^* (S ⊗_R P)
        │ ≅                              │ ≅
        ▼                                ▼
S ⊗_R g^* (P ⊗ S_Y) ──▶ S ⊗_R (g^* P ⊗ S_Z) ──π♯──▶ S ⊗_R g^* P
```
commutes. It is the transpose of `AlgebraicGeometry.ProEtale.sheafExtendScalarsProjection_upperStar`
along the adjunction between extension and restriction of scalars. -/
lemma sheafExtendScalarsProjectionTranspose_upperStar
    (P : Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) :
    (ProEtale.upperStar (ModuleCat.{u + 1} S) g).map
        ((sheafExtendScalarsProjectionTranspose R S Y).app P) ≫
      (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom.app P =
    (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom.app
        (P ⊗ sheafRestrictScalarsUnit R S Y) ≫
      (sheafExtendScalars (algebraMap R S) Z).map
        ((tensorRestrictScalarsUnitUpperStarMap R S g).app P) ≫
      (sheafExtendScalarsProjectionTranspose R S Z).app
        ((ProEtale.upperStar (ModuleCat.{u + 1} R) g).obj P) := by
  have h₀ : (tensorRestrictScalarsUnitUpperStarMap R S g).app P ≫
      (sheafExtendScalarsProjection R S Z).app ((ProEtale.upperStar (ModuleCat.{u + 1} R) g).obj P) =
      (ProEtale.upperStar (ModuleCat.{u + 1} R) g).map ((sheafExtendScalarsProjection R S Y).app P) ≫
        (upperStarRestrictScalarsMap R S g).app ((sheafExtendScalars (algebraMap R S) Y).obj P) ≫
        (sheafCompose (ProEt.topology Z) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map
          ((sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom.app P) := by
    rw [sheafExtendScalarsProjection_upperStar]
    simp [tensorRestrictScalarsUnitUpperStarMap]
  have hU : (sheafExtendScalars (algebraMap R S) Z).map
        ((upperStarRestrictScalarsMap R S g).app ((sheafExtendScalars (algebraMap R S) Y).obj P)) ≫
      (sheafExtendScalarsAdjunction (algebraMap R S) Z).counit.app _ =
      (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).inv.app _ ≫
        (ProEtale.upperStar (ModuleCat.{u + 1} S) g).map
          ((sheafExtendScalarsAdjunction (algebraMap R S) Y).counit.app _) :=
    mateEquiv_counit (sheafExtendScalarsAdjunction (algebraMap R S) Y)
      (sheafExtendScalarsAdjunction (algebraMap R S) Z)
      (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).inv
      ((sheafExtendScalars (algebraMap R S) Y).obj P)
  have hσ := (sheafExtendScalarsCompUpperStarIso (algebraMap R S) g).hom.naturality
    ((sheafExtendScalarsProjection R S Y).app P)
  dsimp at hσ
  simp only [sheafExtendScalarsProjectionTranspose, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  rw [← Functor.map_comp_assoc, h₀]
  simp only [Functor.map_comp, Category.assoc]
  rw [Adjunction.counit_naturality, reassoc_of% hU, ← reassoc_of% hσ,
    Iso.hom_inv_id_app_assoc]

section Derived

variable [IsNoetherianRing R]

/-- The counit of `L(- ⊗ S_Y) ⋙ Lg^*`: the counit of `L(- ⊗ S_Y)` followed by the counit of
`Lg^*`. -/
noncomputable def leftDerivedTensorRestrictScalarsUnitUpperStarCounit :
    DerivedCategory.Qh ⋙ L(tensorRight (sheafRestrictScalarsUnit R S Y)) ⋙
        L((g)^*[ModuleCat.{u + 1} R]) ⟶
      (tensorRight (sheafRestrictScalarsUnit R S Y)).mapHomotopyCategory (.up ℤ) ⋙
        (g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight (tensorRight (sheafRestrictScalarsUnit R S Y)).leftDerivedFunctorCounit
      L((g)^*[ModuleCat.{u + 1} R]) ≫
    Functor.whiskerLeft
      ((tensorRight (sheafRestrictScalarsUnit R S Y)).mapHomotopyCategory (.up ℤ))
      (g)^*[ModuleCat.{u + 1} R].leftDerivedFunctorCounit

/-- The counit of `Lg^* ⋙ L(- ⊗ S_Z)`: the counit of `Lg^*` followed by the counit of
`L(- ⊗ S_Z)`. -/
noncomputable def leftDerivedUpperStarTensorRestrictScalarsUnitCounit :
    DerivedCategory.Qh ⋙ L((g)^*[ModuleCat.{u + 1} R]) ⋙
        L(tensorRight (sheafRestrictScalarsUnit R S Z)) ⟶
      (g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ) ⋙
        (tensorRight (sheafRestrictScalarsUnit R S Z)).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh :=
  Functor.whiskerRight (g)^*[ModuleCat.{u + 1} R].leftDerivedFunctorCounit
      L(tensorRight (sheafRestrictScalarsUnit R S Z)) ≫
    Functor.whiskerLeft ((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ))
      (tensorRight (sheafRestrictScalarsUnit R S Z)).leftDerivedFunctorCounit

omit [IsNoetherianRing R] in
/-- On a complex whose pullback by `g` is K-flat, the counit of `L(- ⊗ S_Z)` at the pullback is
an isomorphism. -/
lemma isIso_leftDerivedFunctorCounit_tensorRight_app_mapHomotopyCategory_obj
    (K : CochainComplex (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) ℤ)
    (hK : kFlatUpperStar (ModuleCat.{u + 1} R) g ((HomotopyCategory.quotient _ _).obj K)) :
    IsIso ((tensorRight (sheafRestrictScalarsUnit R S Z)).leftDerivedFunctorCounit.app
      (((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj K))) := by
  have hK₀ := kFlat_mapHomologicalComplex_obj_of_kFlatUpperStar _ g hK
  have := (tensorRight (sheafRestrictScalarsUnit R S Z)).isIso_leftDerivedFunctorCounit_app_of_kFlat
    _ hK₀
  exact (NatTrans.isIso_app_iff_of_iso _
    (((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategoryFactors (.up ℤ)).app K)).2 this

instance isLeftDerivedFunctor_leftDerivedUpperStarTensorRestrictScalarsUnit :
    (L((g)^*[ModuleCat.{u + 1} R]) ⋙
      L(tensorRight (sheafRestrictScalarsUnit R S Z))).IsLeftDerivedFunctor
      (leftDerivedUpperStarTensorRestrictScalarsUnitCounit R S g)
      (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIsoLocalizerMorphism (kFlatUpperStar (ModuleCat.{u + 1} R) g)) _
    (fun K ↦ ?_)
  have := isIso_leftDerivedFunctorCounit_tensorRight_app_mapHomotopyCategory_obj R S g K.obj.as
    K.property
  simp only [leftDerivedUpperStarTensorRestrictScalarsUnitCounit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  exact IsIso.comp_isIso' inferInstance this

/-- The comparison `g^*(P ⊗ S_Y) ⟶ g^* P ⊗ S_Z` on homotopy categories. -/
noncomputable def mapHomotopyCategoryTensorRestrictScalarsUnitUpperStarMap :
    (tensorRight (sheafRestrictScalarsUnit R S Y)).mapHomotopyCategory (.up ℤ) ⋙
        (g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ) ⟶
      (g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ) ⋙
        (tensorRight (sheafRestrictScalarsUnit R S Z)).mapHomotopyCategory (.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso (Iso.refl _) _).hom ≫
    NatTrans.mapHomotopyCategory (tensorRestrictScalarsUnitUpperStarMap R S g) (.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) _).inv

/-- The comparison `Lg^* (K ⊗ᴸ S_Y) ⟶ Lg^* K ⊗ᴸ S_Z` induced by the comparison
`g^*(P ⊗ S_Y) ⟶ g^* P ⊗ S_Z` of sheaves, where `- ⊗ᴸ S_Y` is the left derived functor of
`- ⊗ S_Y`. -/
noncomputable def leftDerivedTensorRestrictScalarsUnitUpperStarMap :
    L(tensorRight (sheafRestrictScalarsUnit R S Y)) ⋙ L((g)^*[ModuleCat.{u + 1} R]) ⟶
      L((g)^*[ModuleCat.{u + 1} R]) ⋙ L(tensorRight (sheafRestrictScalarsUnit R S Z)) :=
  Functor.leftDerivedNatTrans _ _ (leftDerivedTensorRestrictScalarsUnitUpperStarCounit R S g)
    (leftDerivedUpperStarTensorRestrictScalarsUnitCounit R S g)
    (HomotopyCategory.quasiIso _ (.up ℤ))
    (Functor.whiskerRight (mapHomotopyCategoryTensorRestrictScalarsUnitUpperStarMap R S g)
      DerivedCategory.Qh)

/-- The defining property of `leftDerivedTensorRestrictScalarsUnitUpperStarMap`. -/
@[reassoc]
lemma leftDerivedTensorRestrictScalarsUnitUpperStarMap_app_comp_counit
    (K : HomotopyCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (leftDerivedTensorRestrictScalarsUnitUpperStarMap R S g).app (DerivedCategory.Qh.obj K) ≫
        (leftDerivedUpperStarTensorRestrictScalarsUnitCounit R S g).app K =
      (leftDerivedTensorRestrictScalarsUnitUpperStarCounit R S g).app K ≫
        DerivedCategory.Qh.map
          ((mapHomotopyCategoryTensorRestrictScalarsUnitUpperStarMap R S g).app K) :=
  Functor.leftDerivedNatTrans_app _ _ _ _ _ _ K

omit [IsNoetherianRing R] in
/-- The isomorphism `Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G))` has identity inverse
components. -/
private lemma mapHomotopyCategoryCompIso_refl_inv_app {V W V' : Type*} [Category V] [Category W]
    [Category V'] [Preadditive V] [Preadditive W] [Preadditive V'] (F : V ⥤ W) (G : W ⥤ V')
    [F.Additive] [G.Additive] (K : HomotopyCategory V (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app K = 𝟙 _ := by
  rw [← cancel_epi ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom.app K),
    Iso.hom_inv_id_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id]

omit [IsNoetherianRing R] in
/-- `AlgebraicGeometry.ProEtale.sheafExtendScalarsProjectionTranspose_upperStar` on homotopy
categories. -/
lemma mapHomotopyCategory_sheafExtendScalarsProjectionTranspose_upperStar
    (K : HomotopyCategory (Sheaf (ProEt.topology Y) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    ((g)^*[ModuleCat.{u + 1} S].mapHomotopyCategory (.up ℤ)).map
        ((Functor.mapHomotopyCategoryCompIso
            (Iso.refl (tensorRight (sheafRestrictScalarsUnit R S Y) ⋙
              sheafExtendScalars (algebraMap R S) Y)) (.up ℤ)).hom.app K ≫
          (NatTrans.mapHomotopyCategory (sheafExtendScalarsProjectionTranspose R S Y)
            (.up ℤ)).app K) ≫
      (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).hom.app K =
    (mapHomotopyCategorySheafExtendScalarsCompUpperStarIso R S g).hom.app
        (((tensorRight (sheafRestrictScalarsUnit R S Y)).mapHomotopyCategory (.up ℤ)).obj K) ≫
      ((sheafExtendScalars (algebraMap R S) Z).mapHomotopyCategory (.up ℤ)).map
        ((mapHomotopyCategoryTensorRestrictScalarsUnitUpperStarMap R S g).app K) ≫
      (Functor.mapHomotopyCategoryCompIso
          (Iso.refl (tensorRight (sheafRestrictScalarsUnit R S Z) ⋙
            sheafExtendScalars (algebraMap R S) Z)) (.up ℤ)).hom.app
        (((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ)).obj K) ≫
      (NatTrans.mapHomotopyCategory (sheafExtendScalarsProjectionTranspose R S Z) (.up ℤ)).app
        (((g)^*[ModuleCat.{u + 1} R].mapHomotopyCategory (.up ℤ)).obj K) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [mapHomotopyCategorySheafExtendScalarsCompUpperStarIso,
    mapHomotopyCategoryTensorRestrictScalarsUnitUpperStarMap, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    mapHomotopyCategoryCompIso_refl_inv_app, Category.id_comp, Category.comp_id,
    NatTrans.mapHomotopyCategory, HomotopyCategory.quotient_obj_as,
    Functor.mapHomotopyCategory_map]
  simp only [← Functor.map_comp]
  congr 1
  refine HomologicalComplex.hom_ext _ _ (fun n ↦ ?_)
  have h := sheafExtendScalarsProjectionTranspose_upperStar R S g (K.X n)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f]
  exact h

end Derived

end AlgebraicGeometry.ProEtale
