/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.Completion
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.ProZero
public import WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality

/-!
# Maps of coefficient towers with pro-zero cones

Let `A` be a monoidal closed braided Grothendieck abelian category with functorial flat
resolutions and let `ε : P ⟶ P'` be a map of coefficient towers
`P, P' : ℕᵒᵖ ⥤ CochainComplex A ℤ`. If the tower of mapping cones `m ↦ cone(εₘ)` is pro-zero in
`D(A)`, then for every `K ∈ D(A)` the induced map of reduction towers `K ⊗ᴸ Pₘ ⟶ K ⊗ᴸ P'ₘ`
induces an isomorphism on derived limits `R lim`
(`DerivedCategory.isIso_rlim_map_reductionTowerMap_app`).

Representing `K` by a K-flat complex `X`, the map of reduction towers is the image of the map of
complexes of towers `u : (X ⊗ Pₘ)ₘ ⟶ (X ⊗ P'ₘ)ₘ`. Its mapping cone is, levelwise, the cone of
`X ⊗ εₘ`, that is `X ⊗ cone(εₘ)` (`CochainComplex.mapBifunctorMappingCone₂Iso`), so the derived
limit of the cone vanishes (`CategoryTheory.Pretriangulated.IsHomotopyLimit.isZero_of_isProZero`)
and `R lim` of `u`, a triangulated functor applied to a distinguished triangle, is an
isomorphism.

## Main definitions

- `CochainComplex.mappingConeFunctor`: the diagram of mapping cones of a morphism of diagrams
  of cochain complexes.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

namespace CategoryTheory.Functor.IsProZero

variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- Being pro-zero is invariant under isomorphisms of towers. -/
lemma of_iso {F G : ℕᵒᵖ ⥤ C} (e : F ≅ G) (hF : F.IsProZero) : G.IsProZero := fun n ↦ by
  obtain ⟨m, h, hm⟩ := hF n
  exact ⟨m, h, by rw [← NatIso.naturality_2 e, hm, zero_comp, comp_zero]⟩

/-- A tower whose transition maps become zero after applying a functor which preserves zero
morphisms stays pro-zero after applying it. -/
lemma comp {D : Type*} [Category D] [HasZeroMorphisms D] {F : ℕᵒᵖ ⥤ C} (hF : F.IsProZero)
    (G : C ⥤ D) [G.PreservesZeroMorphisms] : (F ⋙ G).IsProZero := fun n ↦ by
  obtain ⟨m, h, hm⟩ := hF n
  exact ⟨m, h, by rw [Functor.comp_map, hm, G.map_zero]⟩

end CategoryTheory.Functor.IsProZero

namespace CochainComplex

open HomComplex mappingCone

section

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The comparison isomorphism `H (cone φ) ≅ cone (H φ)` is natural in the additive functor
`H`. -/
@[reassoc]
lemma mappingCone.mapHomologicalComplexIso_hom_naturality {K L : CochainComplex C ℤ}
    (φ : K ⟶ L) {H H' : C ⥤ D} [H.Additive] [H'.Additive] (τ : H ⟶ H') :
    (NatTrans.mapHomologicalComplex τ _).app (mappingCone φ) ≫
        (mapHomologicalComplexIso φ H').hom =
      (mapHomologicalComplexIso φ H).hom ≫
        mappingCone.map _ _ ((NatTrans.mapHomologicalComplex τ _).app K)
          ((NatTrans.mapHomologicalComplex τ _).app L)
          ((NatTrans.mapHomologicalComplex τ _).naturality φ).symm := by
  ext n
  dsimp [mapHomologicalComplexIso]
  simp only [mapHomologicalComplexXIso_eq φ _ n (n + 1) rfl, ext_to_iff _ _ _ rfl,
    mapHomologicalComplexXIso'_hom, mappingCone.map, Preadditive.comp_add, Preadditive.add_comp,
    Category.assoc, inl_v_fst_v, inr_f_fst_v, inl_v_snd_v, inr_f_snd_v,
    Category.comp_id, comp_zero, add_zero, zero_add]
  constructor
  · simp [Cochain.comp_v _ _ (zero_add (-1)) (n + 1) (n + 1) n (by lia) (by lia)]
  · simp

variable {J : Type*} [Category J]

/-- The diagram of mapping cones `j ↦ cone(uⱼ)` of a morphism `u : G ⟶ G'` of diagrams of
cochain complexes. -/
@[simps]
noncomputable def mappingConeFunctor {G G' : J ⥤ CochainComplex C ℤ} (u : G ⟶ G') :
    J ⥤ CochainComplex C ℤ where
  obj j := mappingCone (u.app j)
  map f := mappingCone.map _ _ (G.map f) (G'.map f) (u.naturality f).symm
  map_id j := by
    simp only [CategoryTheory.Functor.map_id]
    exact mappingCone.map_id _
  map_comp f g := by
    simp only [Functor.map_comp]
    exact mappingCone.map_comp _ _ _ _ _ _ _ _ _

end

section

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C] {J : Type*} [Category J]

set_option backward.defeqAttrib.useBackward true in
/-- Evaluating the mapping cone of a morphism of complexes of diagrams gives the diagram of
mapping cones of the evaluations. -/
noncomputable def functorEquivalenceFunctorObjMappingConeIso {Y Y' : CochainComplex (J ⥤ C) ℤ}
    (u : Y ⟶ Y') :
    (HomologicalComplex.functorEquivalence C (.up ℤ) J).functor.obj (mappingCone u) ≅
      mappingConeFunctor ((HomologicalComplex.functorEquivalence C (.up ℤ) J).functor.map u) :=
  NatIso.ofComponents (fun j ↦ mapHomologicalComplexIso u ((evaluation J C).obj j))
    fun f ↦ mappingCone.mapHomologicalComplexIso_hom_naturality u ((evaluation J C).map f)

end

end CochainComplex

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A] [IsGrothendieckAbelian.{v} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]
  [Abelian.HasFunctorialFlatResolution A]

local instance : HasColimitsOfSize.{0, 0} A := hasColimitsOfSizeShrink A

open CochainComplex

/-- If the tower underlying the mapping cone of a map `u` of complexes of towers is pro-zero in
`D(A)`, then `R lim` sends `u` to an isomorphism. -/
lemma isIso_rlim_map_Q_map_of_isProZero {Y Y' : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (u : Y ⟶ Y')
    (hu : ((HomologicalComplex.functorEquivalence A (.up ℤ) ℕᵒᵖ).functor.obj (mappingCone u) ⋙
      Q).IsProZero) :
    IsIso ((rlim A).map (Q.map u)) := by
  have hT := (rlim A).map_distinguished _ (mappingCone_triangle_distinguished u)
  have hZ : IsZero ((rlim A).obj (Q.obj (mappingCone u))) :=
    IsHomotopyLimit.isZero_of_isProZero (hu.of_iso ((towerDiagramQIso A).app _).symm)
      (isHomotopyLimit_rlimCone (Q.obj (mappingCone u)))
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hZ

/-- For a K-flat complex `X`, the image in `D(A)` of `X ⊗ g` vanishes when that of `g` does. -/
lemma Q_map_whiskerLeft_eq_zero (X : CochainComplex.KFlat A) {M N : CochainComplex A ℤ}
    {g : M ⟶ N} (hg : Q.map g = 0) : Q.map (X.1 ◁ g) = 0 := by
  have hL : (TensorCommShift₂.L A).map g = 0 := by
    have := (quotientCompQhIso A).hom.naturality g
    dsimp at this
    rw [← cancel_mono ((quotientCompQhIso A).hom.app N), zero_comp, this, hg, comp_zero]
  have h := ((TensorCommShift₂.liftingIsoHom A).app X).naturality g
  dsimp at h
  rw [hL, MonoidalCategory.whiskerLeft_zero, zero_comp] at h
  have h' : (TensorCommShift₂.L A).map (X.1 ◁ g) = 0 := by
    rw [← cancel_epi (((TensorCommShift₂.liftingIsoHom A).app X).app M)]
    simpa using h.symm
  have := (quotientCompQhIso A).hom.naturality (X.1 ◁ g)
  dsimp at this
  rw [← cancel_epi ((quotientCompQhIso A).hom.app _), ← this, h', zero_comp, comp_zero]

/-- The levels of the mapping cone of `(X ⊗ Pₘ)ₘ ⟶ (X ⊗ P'ₘ)ₘ` are the complexes
`X ⊗ cone(εₘ)`. -/
noncomputable def tensorTowerFunctorMapMappingConeIso {P P' : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (ε : P ⟶ P') (X : CochainComplex A ℤ) :
    (HomologicalComplex.functorEquivalence A (.up ℤ) ℕᵒᵖ).functor.obj
        (mappingCone ((tensorTowerFunctorMap ε).app X)) ≅
      mappingConeFunctor ε ⋙ (curriedTensor (CochainComplex A ℤ)).obj X :=
  functorEquivalenceFunctorObjMappingConeIso _ ≪≫
    NatIso.ofComponents (fun m ↦ (mapBifunctorMappingCone₂Iso X (ε.app m) _).symm)
      fun {m m'} f ↦ by
        rw [← cancel_epi (mapBifunctorMappingCone₂Iso X (ε.app m) _).hom]
        simp only [Iso.symm_hom, Iso.hom_inv_id_assoc]
        rw [← cancel_mono (mapBifunctorMappingCone₂Iso X (ε.app m') _).hom, Category.assoc,
          Category.assoc, Iso.inv_hom_id, Category.comp_id]
        exact (mapBifunctorMappingCone₂Iso_hom_naturality _ (𝟙 X) (ε.app m) (ε.app m')
          (P.map f) (P'.map f) (ε.naturality f).symm).symm

/-- **Maps of coefficient towers with pro-zero cones.** If the tower of mapping cones
`m ↦ cone(εₘ)` of a map of coefficient towers `ε : P ⟶ P'` is pro-zero in `D(A)`, then for
every `K ∈ D(A)` the map of reduction towers `K ⊗ᴸ P ⟶ K ⊗ᴸ P'` induces an isomorphism on
derived limits. -/
theorem isIso_rlim_map_reductionTowerMap_app {P P' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (ε : P ⟶ P')
    (hε : (mappingConeFunctor ε ⋙ Q).IsProZero) (K : DerivedCategory A) :
    IsIso ((rlim A).map ((reductionTowerMap ε).app K)) := by
  have key (X : CochainComplex.KFlat A) :
      IsIso ((rlim A).map ((reductionTowerMap ε).app ((TensorCommShift₂.LKFlat A).obj X))) := by
    rw [reductionTowerMap, Localization.liftNatTrans_app]
    simp only [Functor.map_comp]
    have : IsIso ((rlim A).map (Q.map ((tensorTowerFunctorMap ε).app X.1))) := by
      refine isIso_rlim_map_Q_map_of_isProZero _ ?_
      refine Functor.IsProZero.of_iso
        (Functor.isoWhiskerRight (tensorTowerFunctorMapMappingConeIso ε X.1) Q).symm ?_
      intro n
      obtain ⟨m, h, hm⟩ := hε n
      exact ⟨m, h, Q_map_whiskerLeft_eq_zero X hm⟩
    change IsIso (_ ≫ (rlim A).map (Q.map ((tensorTowerFunctorMap ε).app X.1)) ≫ _)
    infer_instance
  obtain ⟨X, ⟨e⟩⟩ : ∃ X, Nonempty ((TensorCommShift₂.LKFlat A).obj X ≅ K) :=
    ⟨_, ⟨(TensorCommShift₂.LKFlat A).objObjPreimageIso K⟩⟩
  have h := (Functor.whiskerRight (reductionTowerMap ε) (rlim A)).naturality e.hom
  simp only [Functor.comp_map, Functor.whiskerRight_app] at h
  have hK : (rlim A).map ((reductionTowerMap ε).app K) =
      (rlim A).map ((reductionTower P).map e.inv) ≫
        (rlim A).map ((reductionTowerMap ε).app ((TensorCommShift₂.LKFlat A).obj X)) ≫
          (rlim A).map ((reductionTower P').map e.hom) := by
    rw [h, ← Functor.map_comp_assoc, ← Functor.map_comp, e.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have := key X
  rw [hK]
  infer_instance

end DerivedCategory
