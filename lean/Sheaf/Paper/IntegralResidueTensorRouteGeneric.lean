/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE.
-/
module

public import Sheaf.Paper.IntegralResidueTensorModel
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided

/-! # Counit-normalized tensor-route calculation

The abstract calculation and ordinary internal-module braiding used by the concrete
residue tensor route. Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15.
(blueprint: new-integral-residue-tensor-route-generic)
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open CategoryTheory.Category
open scoped CategoryTheory.Obj CategoryTheory.Functor
local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

section OrdinaryBraiding

universe v v' u₁ u₂
open MonObj
variable {C : Type u₁} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  {D : Type u₂} [Category.{v'} D] [Abelian D] [IsGrothendieckAbelian.{v'} D]
  [MonoidalCategory D] [SymmetricCategory D] [MonoidalClosed D]
  {R : C} [MonObj R] [IsCommMonObj R] {S : D} [MonObj S] [IsCommMonObj S]
  {G : C ⥤ D} [G.Braided] [G.PreservesEpimorphisms] (ρ : S ⟶ G.obj R) [IsMonHom ρ] [IsIso ρ]
  [PreservesColimitsOfShape WalkingParallelPair (Mod.mapModComap ρ)]

private theorem ordinary_braiding (M N : Mod C R) :
    letI := Mod.ResidueOrdinary.mapModComapMonoidal ρ
    (Mod.mapModComap ρ).map (β_ M N).hom ≫
        Functor.OplaxMonoidal.δ (Mod.mapModComap ρ) N M =
      Functor.OplaxMonoidal.δ (Mod.mapModComap ρ) M N ≫
        (β_ ((Mod.mapModComap ρ).obj M) ((Mod.mapModComap ρ).obj N)).hom := by
  letI := Mod.ResidueOrdinary.mapModComapMonoidal ρ
  change (Mod.mapModComap ρ).map (β_ M N).hom ≫
      (Mod.ResidueOrdinary.tensorComparison ρ N M).hom =
    (Mod.ResidueOrdinary.tensorComparison ρ M N).hom ≫ _
  apply Mod.hom_ext
  rw [← cancel_epi (G.map (Mod.tensorObjπ M N))]
  simp only [Mod.comp_hom']
  erw [← G.map_comp_assoc, Mod.tensorObjπ_braidingHomX, G.map_comp_assoc,
    Mod.ResidueOrdinary.tensorComparison_π,
    reassoc_of% Mod.ResidueOrdinary.tensorComparison_π,
    Mod.tensorObjπ_braidingHomX]
  rw [← cancel_epi (Functor.LaxMonoidal.μ G M.X N.X)]
  simp only [IsIso.hom_inv_id_assoc]
  rw [Functor.LaxBraided.braided_assoc, IsIso.hom_inv_id_assoc]
  rfl

end OrdinaryBraiding

section TransportBraiding
variable {C D : Type*} [Category* C] [Category* D]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalCategory D] [BraidedCategory D]
  {F G : C ⥤ D} [F.Monoidal]

private theorem transport_braiding (e : F ≅ G)
    (h : ∀ X Y, F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X =
      Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom) (X Y : C) :
    letI := Functor.Monoidal.transport e
    G.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ G Y X =
      Functor.OplaxMonoidal.δ G X Y ≫ (β_ (G.obj X) (G.obj Y)).hom := by
  simp only [Functor.Monoidal.transport_δ, Category.assoc]
  rw [e.inv.naturality_assoc, reassoc_of% h,
    BraidedCategory.braiding_naturality]

end TransportBraiding

section TensorPresentationNormalization

universe v u₁
variable {C : Type u₁} [Category.{v + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{v + 1} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

@[instance_reducible]
private noncomputable def sourceBraiding : BraidedCategory (DerivedCategory C) :=
  DerivedCategory.braidedCategory C

attribute [local instance] sourceBraiding

private theorem derived_braiding_μ (P Q : HomotopyCategory C (.up ℤ)) :
    (β_ (DerivedCategory.Qh.obj P) (DerivedCategory.Qh.obj Q)).hom ≫
        Functor.LaxMonoidal.μ DerivedCategory.Qh Q P =
      Functor.LaxMonoidal.μ DerivedCategory.Qh P Q ≫
        DerivedCategory.Qh.map (β_ P Q).hom :=
  DerivedMonoidal.braiding_hom_μ _ _ P Q



universe u₂
variable {D : Type u₂} [Category.{v + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{v + 1} D] [MonoidalCategory D] [MonoidalClosed D]
  [MonoidalPreadditive D] [BraidedCategory D] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]

noncomputable local instance : BraidedCategory (DerivedCategory D) :=
  DerivedCategory.braidedCategory D



private theorem derived_braiding_Qh
    (m : F.leftDerivedFunctor.OplaxMonoidal)
    (hm : ∀ K M : DerivedCategory C,
      letI := m
      Functor.OplaxMonoidal.δ F.leftDerivedFunctor K M =
        (F.leftDerivedTensorComparison.app K).app M)
    (hF : ∀ X Y, F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X =
      Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    (P Q : HomotopyCategory C (.up ℤ)) (hP : F.kFlatMap P) :
    letI := m
    F.leftDerivedFunctor.map (β_ (DerivedCategory.Qh.obj P)
        (DerivedCategory.Qh.obj Q)).hom ≫
        Functor.OplaxMonoidal.δ F.leftDerivedFunctor
          (DerivedCategory.Qh.obj Q) (DerivedCategory.Qh.obj P) =
      Functor.OplaxMonoidal.δ F.leftDerivedFunctor
          (DerivedCategory.Qh.obj P) (DerivedCategory.Qh.obj Q) ≫
        (β_ (F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P))
          (F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj Q))).hom := by
  letI := m
  have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((F.mapHomotopyCategory (.up ℤ)).obj Q)
      ((F.mapHomotopyCategory (.up ℤ)).obj P)) :=
    Functor.isIso_μNatTrans_Qh_app_app_of_kFlat _ _ hP
  rw [← cancel_mono ((F.leftDerivedFunctorCounit.app Q ⊗ₘ
    F.leftDerivedFunctorCounit.app P) ≫
    Functor.LaxMonoidal.μ DerivedCategory.Qh ((F.mapHomotopyCategory (.up ℤ)).obj Q)
      ((F.mapHomotopyCategory (.up ℤ)).obj P))]
  simp only [hm, Category.assoc]
  rw [Functor.leftDerivedTensorComparison_app_app_comp_tensorHom,
    ← BraidedCategory.braiding_naturality_assoc]
  simp only [Functor.comp_obj]
  rw [derived_braiding_μ]
  rw [Functor.leftDerivedTensorComparison_app_app_comp_tensorHom_assoc]
  rw [← F.leftDerivedFunctor.map_comp_assoc,
    derived_braiding_μ,
    F.leftDerivedFunctor.map_comp_assoc]
  have hn := F.leftDerivedFunctorCounit.naturality (β_ P Q).hom
  erw [reassoc_of% hn]
  rw [← DerivedCategory.Qh.map_comp, ← DerivedCategory.Qh.map_comp]
  have hb : (F.mapHomotopyCategory (.up ℤ)).map (β_ P Q).hom ≫
      Functor.OplaxMonoidal.δ (F.mapHomotopyCategory (.up ℤ)) Q P =
      Functor.OplaxMonoidal.δ (F.mapHomotopyCategory (.up ℤ)) P Q ≫
        (β_ ((F.mapHomotopyCategory (.up ℤ)).obj P)
          ((F.mapHomotopyCategory (.up ℤ)).obj Q)).hom := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective Q
    have hc : (F.mapHomologicalComplex (.up ℤ)).map (β_ K L).hom ≫
        ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app L).app K =
        ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app K).app L ≫
          (β_ ((F.mapHomologicalComplex (.up ℤ)).obj K)
            ((F.mapHomologicalComplex (.up ℤ)).obj L)).hom := by
      ext n
      refine mapBifunctor.hom_ext_of_map F (fun p q h ↦ ?_)
      simp only [Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans_app_app,
        comp_f, mapBifunctorComparison_f, Functor.mapHomologicalComplex_map_f]
      have h₁ := CochainComplex.Monoidal.ι_braiding_hom (K := K) (L := L) p q n h
      have h₂ := CochainComplex.Monoidal.ι_braiding_hom
        (K := (F.mapHomologicalComplex (.up ℤ)).obj K)
        (L := (F.mapHomologicalComplex (.up ℤ)).obj L) p q n h
      erw [← F.map_comp_assoc, h₁, map_ιMapBifunctor_mapBifunctorComparisonX_assoc, h₂]
      rw [F.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
        F.map_comp, Category.assoc]
      erw [map_ιMapBifunctor_mapBifunctorComparisonX]
      simp only [mapBifunctorComparisonApp, Functor.OplaxMonoidal.δNatTrans_app_app]
      rw [reassoc_of% hF]
      rfl
    have h := (HomotopyCategory.quotient D (.up ℤ)).congr_map hc
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h
  simp only [Functor.mapHomotopyCategory_δ] at hb
  rw [hb]

private theorem derived_braiding
    (m : F.leftDerivedFunctor.OplaxMonoidal)
    (hm : ∀ K M : DerivedCategory C,
      letI := m
      Functor.OplaxMonoidal.δ F.leftDerivedFunctor K M =
        (F.leftDerivedTensorComparison.app K).app M)
    (hF : ∀ X Y, F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X =
      Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    (K M : DerivedCategory C) :
    letI := m
    F.leftDerivedFunctor.map (β_ K M).hom ≫
        Functor.OplaxMonoidal.δ F.leftDerivedFunctor M K =
      Functor.OplaxMonoidal.δ F.leftDerivedFunctor K M ≫
        (β_ (F.leftDerivedFunctor.obj K) (F.leftDerivedFunctor.obj M)).hom := by
  letI := m
  obtain ⟨P, hP, ⟨eP⟩⟩ := F.residue_exists_kFlatMap_iso K
  obtain ⟨Q, -, ⟨eQ⟩⟩ := F.residue_exists_kFlatMap_iso M
  rw [← cancel_epi (F.leftDerivedFunctor.map (eP.hom ⊗ₘ eQ.hom)),
    ← F.leftDerivedFunctor.map_comp_assoc, BraidedCategory.braiding_naturality,
    F.leftDerivedFunctor.map_comp_assoc, ← Functor.OplaxMonoidal.δ_natural,
    reassoc_of% derived_braiding_Qh F m hm hF P Q hP,
    ← Functor.OplaxMonoidal.δ_natural_assoc, BraidedCategory.braiding_naturality]

/-- An exact braided monoidal functor carries the canonical derived tensor presentation
into its ordinary homotopy tensor model.
Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15; functorial derived tensor counits.
(blueprint: new-integral-residue-tensor-route-generic)

Proof. Check the ordinary comparison on each Koszul tensor summand of complexes,
then pass through the homotopy quotient. Compute derived braiding on representatives
whose image under F is K-flat,
using the Qh tensor comparison and the left-derived counit. Cancel the invertible tensor
comparison there, then transport the identity along K-flat resolutions for arbitrary
objects. Move inverse braiding through the derived comparison. Naturality moves the
single-object coefficient comparison through it. The defining tensor-comparison equation
then replaces the derived comparison and its two counits by the ordinary comparison.
The normalization of the tensor presentation cancels its inverse coefficient comparison
and braiding. Finally naturality of the F-counit gives exactly tensorModelMap. -/
theorem residue_tensor_route_model_generic
    (m : F.leftDerivedFunctor.Monoidal)
    (hm : ∀ K M : DerivedCategory C,
      letI := m
      Functor.OplaxMonoidal.δ F.leftDerivedFunctor K M =
        (F.leftDerivedTensorComparison.app K).app M)
    (B : C)
    (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (t : H ≅ tensorRight ((DerivedCategory.singleFunctor C 0).obj B))
    (ht : t = derivedTensorPresentationIso B H ε)
    (hF : ∀ X Y, F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X =
      Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom)
    (P : HomotopyCategory C (.up ℤ))
    (a : F.leftDerivedFunctor.obj (DerivedCategory.Qh.obj P) ⊗
        F.leftDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj B) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P))
    (ha : a = F.tensorModelTarget B P)
    (b : F.leftDerivedFunctor.obj (H.obj (DerivedCategory.Qh.obj P)) ⟶
      DerivedCategory.Qh.obj
        ((F.mapHomotopyCategory (.up ℤ)).obj (Functor.tensorModelCoefficient B) ⊗
          (F.mapHomotopyCategory (.up ℤ)).obj P))
    (hb : b = F.tensorModelMap B H ε P) :
    letI := m
    F.leftDerivedFunctor.map (t.hom.app (DerivedCategory.Qh.obj P)) ≫
        Functor.OplaxMonoidal.δ F.leftDerivedFunctor (DerivedCategory.Qh.obj P)
          ((DerivedCategory.singleFunctor C 0).obj B) ≫ a = b := by
  letI := m
  rw [ht, ha, hb]
  let LF := F.leftDerivedFunctor
  let M := DerivedCategory.Qh.obj P
  let B₀ := (DerivedCategory.singleFunctor C 0).obj B
  have hb : Functor.OplaxMonoidal.δ LF M B₀ ≫
        (β_ (LF.obj B₀) (LF.obj M)).inv =
      LF.map (β_ B₀ M).inv ≫ Functor.OplaxMonoidal.δ LF B₀ M := by
    rw [← cancel_epi (LF.map (β_ B₀ M).hom)]
    simp only [← LF.map_comp_assoc, Iso.hom_inv_id, LF.map_id, Category.id_comp]
    rw [reassoc_of% derived_braiding F m.toOplaxMonoidal hm hF B₀ M,
      Iso.hom_inv_id, Category.comp_id]
  delta Functor.tensorModelTarget Functor.tensorModelMap
  rw [reassoc_of% hb]
  rw [← MonoidalCategory.whiskerRight_comp_tensorHom]
  simp only [Category.assoc]
  rw [Functor.OplaxMonoidal.δ_natural_left_assoc]
  dsimp only [LF, M, B₀]
  rw [hm]
  rw [Functor.leftDerivedTensorComparison_app_app_comp_tensorHom]
  rw [← LF.map_comp_assoc, ← LF.map_comp_assoc, ← LF.map_comp_assoc]
  simp only [Category.assoc]
  rw [Functor.derivedTensorPresentationIso_normalization]
  rw [LF.map_comp, Category.assoc]
  have hn := F.leftDerivedFunctorCounit.naturality ((homotopyTensorSingleIso B).inv.app P)
  erw [reassoc_of% hn]
  rw [DerivedCategory.Qh.map_comp]


end TensorPresentationNormalization




namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
  [NormedAlgebra ℚ_[ℓ] E]

/-- Braiding compatibility for ordinary residue pullback.
Source: Bhatt--Scholze, Lemma 6.5.9(3); the balanced tensor presentation of internal modules.
(blueprint: new-integral-residue-tensor-route-generic)

Proof. For mapModComap, precompose with the tensor presentation epimorphism. The tensor
comparison formula and the ambient braided functor identity identify the two composites.
Cancel that epimorphism, then transport the identity along the canonical isomorphism
from mapModComap to ordinary pullback. -/
theorem residue_ordinary_pull_braiding {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) Y)) :
    letI := residueExchangeOrdinaryPullMonoidal ℓ E f
    (f)^*⟦integralCoeff ℓ E⟧.map (β_ M N).hom ≫
        Functor.OplaxMonoidal.δ (f)^*⟦integralCoeff ℓ E⟧ N M =
      Functor.OplaxMonoidal.δ (f)^*⟦integralCoeff ℓ E⟧ M N ≫
        (β_ ((f)^*⟦integralCoeff ℓ E⟧.obj M)
          ((f)^*⟦integralCoeff ℓ E⟧.obj N)).hom := by
  let G := (f)^*[Ab.{u + 1}]
  letI : G.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := G) X Y }
  let ρ := (asIso (condensedPullbackHom (integralCoeff ℓ E) f)).inv
  letI : (Mod.mapModComap ρ).Monoidal := Mod.ResidueOrdinary.mapModComapMonoidal ρ
  exact transport_braiding
    (Functor.isoWhiskerLeft (G.mapMod (condensedRingObj (integralCoeff ℓ E) Y))
      (Mod.extendScalarsIsoComapInv (condensedPullbackHom (integralCoeff ℓ E) f))).symm
    (ordinary_braiding ρ) M N

end AlgebraicGeometry.ProEtale.CondensedRing
