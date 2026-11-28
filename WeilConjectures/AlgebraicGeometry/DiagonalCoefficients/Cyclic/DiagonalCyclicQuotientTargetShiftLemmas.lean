/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Cyclic.DiagonalCyclicFunctorCalculus
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.ExactRealizationTargetZero
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Local.DiagonalLocalShiftedLimitProjection

/-! # Shift and transport lemmas for the cyclic normalized target endpoint

Category-theoretic lemmas about shifted single objects in derived categories, used to
assemble the target half of the normalized cyclic endpoint argument.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

section

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- The derived isomorphism of an isomorphism of exact functors is the derived
natural transformation of its forward map. -/
theorem mapDerivedCategoryNatIso_hom_eq {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    (Functor.mapDerivedCategoryNatIso e).hom = NatTrans.mapDerivedCategory e.hom := by
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (fun K ↦ ?_)
  rw [NatTrans.mapDerivedCategory_app_Q_obj,
    ← cancel_mono (G.mapDerivedCategoryFactors.hom.app K),
    Functor.mapDerivedCategoryNatIso_fac]
  simp

instance mapDerivedCategoryNatIso_commShift {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    NatTrans.CommShift (Functor.mapDerivedCategoryNatIso e).hom ℤ := by
  rw [mapDerivedCategoryNatIso_hom_eq]
  infer_instance

end

/-- Composing a mapped shift comparison with the outer shift comparison. -/
theorem map_commShiftIso_comp_shift
    {C D K : Type*} [Category C] [Category D] [Category K]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift K ℤ]
    (F : C ⥤ D) (G : D ⥤ K) [F.CommShift ℤ] [G.CommShift ℤ]
    {M : C} {N : D} {P : K} (f : F.obj M ⟶ N) (g : G.obj N ⟶ P) (k : ℤ) :
    G.map ((F.commShiftIso k).hom.app M ≫ f⟦k⟧') ≫
        (G.commShiftIso k).hom.app N ≫ g⟦k⟧' =
      ((F ⋙ G).commShiftIso k).hom.app M ≫ (G.map f ≫ g)⟦k⟧' := by
  simp only [Functor.map_comp, Functor.commShiftIso_comp_hom_app,
    (shiftFunctor K k).map_comp, Category.assoc]
  rw [G.commShiftIso_hom_naturality_assoc]

/-- The shifted completed target of an exact realization composite is the shift of its
unshifted target, after the composite shift isomorphism. -/
theorem completedFunctorTarget_eq_shift
    {A₀ A₁ A₂ A₃ A₄ : Type*} [Category A₀] [Category A₁] [Category A₂] [Category A₃]
    [Category A₄] [Abelian A₀] [Abelian A₁] [Abelian A₂] [Abelian A₃] [Abelian A₄]
    [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory A₂]
    [HasDerivedCategory A₃] [HasDerivedCategory A₄]
    (E : A₀ ⥤ A₁) [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
    (T : DerivedCategory A₁ ⥤ DerivedCategory A₂) [T.CommShift ℤ]
    (G : A₂ ⥤ A₃) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (H : A₃ ⥤ A₄) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (k : ℕ) {Y₀ : A₀} {L : A₁} {N : A₂} {Q : A₃} (i : E.obj Y₀ ≅ L)
    (j : T.obj ((DerivedCategory.singleFunctor A₁ 0).obj L) ≅
      (DerivedCategory.singleFunctor A₂ 0).obj N) (q : G.obj N ≅ Q) :
    completedFunctorTarget E (T ⋙ G.mapDerivedCategory ⋙ H.mapDerivedCategory) k i
        (threeFunctorTarget T G H k
          ((T.commShiftIso (k : ℤ)).hom.app _ ≫ j.hom⟦(k : ℤ)⟧') q) =
      ((E.mapDerivedCategory ⋙ T ⋙ G.mapDerivedCategory ⋙ H.mapDerivedCategory).commShiftIso
          (k : ℤ)).hom.app ((DerivedCategory.singleFunctor A₀ 0).obj Y₀) ≫
        (exactRealizationTargetZero E T G H i.hom j.hom q.hom)⟦(k : ℤ)⟧' := by
  have h1 := map_commShiftIso_comp_shift T G.mapDerivedCategory j.hom
    ((G.mapDerivedCategorySingleFunctor 0).hom.app N ≫
      (DerivedCategory.singleFunctor A₃ 0).map q.hom) k
  have h2 := map_commShiftIso_comp_shift (T ⋙ G.mapDerivedCategory) H.mapDerivedCategory
    (G.mapDerivedCategory.map j.hom ≫ (G.mapDerivedCategorySingleFunctor 0).hom.app N ≫
      (DerivedCategory.singleFunctor A₃ 0).map q.hom)
    ((H.mapDerivedCategorySingleFunctor 0).hom.app Q) k
  have h3 := map_commShiftIso_comp_shift E.mapDerivedCategory
    ((T ⋙ G.mapDerivedCategory) ⋙ H.mapDerivedCategory)
    ((E.mapDerivedCategorySingleFunctor 0).hom.app Y₀ ≫
      (DerivedCategory.singleFunctor A₁ 0).map i.hom)
    (H.mapDerivedCategory.map (G.mapDerivedCategory.map j.hom ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app N ≫
        (DerivedCategory.singleFunctor A₃ 0).map q.hom) ≫
      (H.mapDerivedCategorySingleFunctor 0).hom.app Q) k
  unfold completedFunctorTarget threeFunctorTarget exactRealizationTargetZero
  simp only [Functor.map_comp, Category.assoc, Functor.comp_map,
    (shiftFunctor (DerivedCategory A₃) (k : ℤ)).map_comp,
    (shiftFunctor (DerivedCategory A₁) (k : ℤ)).map_comp] at h1 h2 h3 ⊢
  have h1' := congrArg H.mapDerivedCategory.map h1
  simp only [Functor.map_comp] at h1'
  rw [reassoc_of% h1', h2, h3]
  congr 1
  simp only [Functor.commShiftIso_comp_hom_app, Functor.comp_map, Functor.map_comp,
    Category.assoc]
  rfl

/-- A shifted map between single objects is the shift of a given single map once its
underlying image, after an epimorphic underlying projection, has the prescribed form. -/
theorem shifted_single_eq_of_epi
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (U : A ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [U.Faithful] {Y₀ : DerivedCategory A} {P₀ P Q : A}
    (κ : Y₀ ⟶ (DerivedCategory.singleFunctor A 0).obj P₀) [IsIso κ]
    (π : P₀ ⟶ P) [Epi (U.map π)] (t : P ⟶ Q) (ρ : U.obj P₀ ⟶ U.obj Q)
    (α : U.mapDerivedCategory.obj Y₀ ⟶
      U.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj Q))
    (Ψ : ((DerivedCategory.singleFunctor A 0).obj P)⟦(2 : ℤ)⟧ ⟶
      ((DerivedCategory.singleFunctor A 0).obj Q)⟦(2 : ℤ)⟧)
    (hα : α ≫ (U.mapDerivedCategorySingleFunctor 0).hom.app Q =
      U.mapDerivedCategory.map κ ≫ (U.mapDerivedCategorySingleFunctor 0).hom.app P₀ ≫
        (DerivedCategory.singleFunctor B 0).map ρ)
    (hmain : U.mapDerivedCategory.map
        ((κ ≫ (DerivedCategory.singleFunctor A 0).map π)⟦(2 : ℤ)⟧') ≫
        U.mapDerivedCategory.map Ψ =
      (U.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app Y₀ ≫ α⟦(2 : ℤ)⟧' ≫
        (U.mapDerivedCategory.commShiftIso (2 : ℤ)).inv.app _)
    (hρ : U.map π ≫ U.map t = ρ) :
    Ψ = ((DerivedCategory.singleFunctor A 0).map t)⟦(2 : ℤ)⟧' := by
  obtain ⟨Ψ₀, rfl⟩ := (shiftFunctor (DerivedCategory A) (2 : ℤ)).map_surjective Ψ
  obtain ⟨ψ, rfl⟩ := (DerivedCategory.singleFunctor A 0).map_surjective Ψ₀
  congr 2
  apply U.map_injective
  apply (cancel_epi (U.map π)).1
  rw [hρ]
  rw [← Functor.map_comp, ← Functor.map_comp] at hmain
  have h₂ := hmain =≫ (U.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _
  rw [Functor.commShiftIso_hom_naturality] at h₂
  simp only [Category.assoc, Iso.inv_hom_id_app] at h₂
  rw [cancel_epi] at h₂
  erw [Category.comp_id] at h₂
  have h₁ := (shiftFunctor (DerivedCategory B) (2 : ℤ)).map_injective h₂ =≫
    (U.mapDerivedCategorySingleFunctor 0).hom.app Q
  rw [hα, Functor.map_comp, Category.assoc, cancel_epi] at h₁
  have hn := (U.mapDerivedCategorySingleFunctor 0).hom.naturality π
  have hn' := (U.mapDerivedCategorySingleFunctor 0).hom.naturality ψ
  dsimp only [Functor.comp_map] at hn hn'
  rw [Functor.map_comp, Category.assoc, hn', reassoc_of% hn, cancel_epi,
    ← Functor.map_comp] at h₁
  exact (DerivedCategory.singleFunctor B 0).map_injective h₁

/-- The finite projection of the shifted single limit comparison is the shift of the
ordinary limit projection. -/
theorem shiftedSingleLimitComparison_projection
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory (ℕᵒᵖ ⥤ B)] [HasLimitsOfShape ℕᵒᵖ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (L : DiagonalRlim B) (P : A) (H : ℕᵒᵖ ⥤ B) (K : DerivedCategory (ℕᵒᵖ ⥤ B))
    (s : F.obj P ≅ limit H)
    (a : K ≅ ((DerivedCategory.singleFunctor _ 0).obj H)⟦(2 : ℤ)⟧) (n : ℕ) :
    diagonalShiftedSingleLimitComparison F L P H K s a ≫ (L.projection n).app K ≫
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.map a.hom ≫
        (((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app _ ≫
        ((((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategorySingleFunctor 0).hom.app
          H)⟦(2 : ℤ)⟧' =
      (F.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app
          ((DerivedCategory.singleFunctor A 0).obj P) ≫
        ((F.mapDerivedCategorySingleFunctor 0).hom.app P ≫
          (DerivedCategory.singleFunctor B 0).map (s.hom ≫ limit.π H (op n)))⟦(2 : ℤ)⟧' := by
  have hp := DiagonalTrace.local_shifted_limit_projection L H n (2 : ℤ)
  have hn := (L.projection n).naturality a.inv
  unfold diagonalShiftedSingleLimitComparison
  simp only [Category.assoc]
  rw [reassoc_of% hn, ← Functor.map_comp_assoc, a.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  rw [hp]

/-- Transport an augmentation equation along a projection square and the comparison of
the augmentation with a quotient unit. -/
theorem augmentation_endpoint_transport {C D : Type*} [Category C] [Category D]
    (U : C ⥤ D) {X X' A₂ A₃ A₄ B S T : C}
    (c : X ⟶ S) [IsIso c] (μ : X ⟶ X') (a : X' ⟶ A₂) (a' : A₂ ⟶ X') (b : A₂ ⟶ A₃)
    (b' : A₃ ⟶ A₂) (ε : A₃ ⟶ A₄) (ε' : A₄ ⟶ A₃) (e : B ⟶ X') (e' : X' ⟶ B)
    (ha : a ≫ a' = 𝟙 X') (hb : b ≫ b' = 𝟙 A₂) (hε : ε ≫ ε' = 𝟙 A₃)
    (he' : e ≫ e' = 𝟙 B) (τ : B ⟶ T) (α : U.obj X ⟶ U.obj B) (g : S ⟶ A₄)
    (R : U.obj S ⟶ U.obj T)
    (hproj : μ ≫ a ≫ b ≫ ε = c ≫ g)
    (he : α ≫ U.map e = U.map μ) (haug : α ≫ U.map τ = U.map c ≫ R) :
    U.map g ≫ U.map (ε' ≫ b' ≫ a' ≫ e' ≫ τ) = R := by
  have hg : g = CategoryTheory.inv c ≫ μ ≫ a ≫ b ≫ ε := by
    rw [hproj, IsIso.inv_hom_id_assoc]
  have hα : U.map μ ≫ U.map e' = α := by
    rw [← he, Category.assoc, ← U.map_comp, he', U.map_id, Category.comp_id]
  rw [hg, ← U.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hε, reassoc_of% hb, reassoc_of% ha]
  rw [U.map_comp, U.map_comp, U.map_comp, reassoc_of% hα, haug,
    ← U.map_comp_assoc, IsIso.inv_hom_id, U.map_id, Category.id_comp]

/-- Composing a shifted augmentation with a shifted target, in terms of the shift
comparison of the functor applied to the target. -/
theorem augmented_shift_comp {D E : Type*} [Category D] [Category E]
    [HasShift D ℤ] [HasShift E ℤ] (U : D ⥤ E) [U.CommShift ℤ]
    {B B₀ T₀ : D} {A A' S₀ : E} (c : B ⟶ B₀⟦(2 : ℤ)⟧) (τ₀ : B₀ ⟶ T₀)
    (k₁ : A ⟶ A') (k₂ : A' ⟶ S₀⟦(2 : ℤ)⟧) (a₀ : S₀ ⟶ U.obj B₀)
    (ψ : (U.obj B₀)⟦(2 : ℤ)⟧ ⟶ U.obj B)
    (hψ : ψ ≫ U.map c = (U.commShiftIso (2 : ℤ)).inv.app B₀) :
    ((k₁ ≫ k₂) ≫ a₀⟦(2 : ℤ)⟧' ≫ ψ) ≫ U.map (c ≫ τ₀⟦(2 : ℤ)⟧') =
      k₁ ≫ k₂ ≫ (a₀ ≫ U.map τ₀)⟦(2 : ℤ)⟧' ≫ (U.commShiftIso (2 : ℤ)).inv.app T₀ := by
  simp only [U.map_comp, Category.assoc]
  rw [reassoc_of% hψ, ← Functor.commShiftIso_inv_naturality]
  simp only [Functor.map_comp, Category.assoc]

/-- Assemble the target endpoint equation from the limit projection square, the
augmentation of the quotient unit, the shifted augmentation of the target, its unshifted
underlying form, and an epimorphic underlying projection. -/
theorem target_endpoint_assembly
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (U : A ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [U.Faithful] {X X' A₂ A₃ A₄ Bc Y₀ Lm : DerivedCategory A} {P₀ P Q : A}
    (μ : X ⟶ X') (a : X' ≅ A₂) (tlm : X ⟶ Lm) (pr : Lm ⟶ A₂)
    (β₁ : A₂ ⟶ A₃) (β₂ : A₃ ⟶ A₂) (hβ : β₁ ≫ β₂ = 𝟙 A₂)
    (ε₁ : A₃ ⟶ A₄) (ε₂ : A₄ ⟶ ((DerivedCategory.singleFunctor A 0).obj P)⟦(2 : ℤ)⟧)
    (hε₁ : IsIso ε₁) (hε₂ : IsIso ε₂)
    (e₁ : Bc ⟶ X') (e₂ : X' ⟶ Bc) (he' : e₁ ≫ e₂ = 𝟙 Bc)
    (τ : Bc ⟶ ((DerivedCategory.singleFunctor A 0).obj Q)⟦(2 : ℤ)⟧)
    (c : X ⟶ Y₀⟦(2 : ℤ)⟧) (hc : IsIso c)
    (κ : Y₀ ⟶ (DerivedCategory.singleFunctor A 0).obj P₀) (hκ : IsIso κ)
    (π : P₀ ⟶ P) [Epi (U.map π)] (t : P ⟶ Q) (ρ : U.obj P₀ ⟶ U.obj Q)
    (αQ : U.mapDerivedCategory.obj X ⟶ U.mapDerivedCategory.obj Bc)
    (α : U.mapDerivedCategory.obj Y₀ ⟶
      U.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj Q))
    (hta : μ ≫ a.hom = tlm ≫ pr)
    (hP : tlm ≫ pr ≫ β₁ ≫ ε₁ ≫ ε₂ =
      c ≫ (κ ≫ (DerivedCategory.singleFunctor A 0).map π)⟦(2 : ℤ)⟧')
    (he : αQ ≫ U.mapDerivedCategory.map e₁ = U.mapDerivedCategory.map μ)
    (haug : αQ ≫ U.mapDerivedCategory.map τ =
      U.mapDerivedCategory.map c ≫ (U.mapDerivedCategory.commShiftIso (2 : ℤ)).hom.app Y₀ ≫
        α⟦(2 : ℤ)⟧' ≫ (U.mapDerivedCategory.commShiftIso (2 : ℤ)).inv.app _)
    (hα : α ≫ (U.mapDerivedCategorySingleFunctor 0).hom.app Q =
      U.mapDerivedCategory.map κ ≫ (U.mapDerivedCategorySingleFunctor 0).hom.app P₀ ≫
        (DerivedCategory.singleFunctor B 0).map ρ)
    (hρ : U.map π ≫ U.map t = ρ) :
    β₂ ≫ a.inv ≫ e₂ ≫ τ =
      ε₁ ≫ ε₂ ≫ ((DerivedCategory.singleFunctor A 0).map t)⟦(2 : ℤ)⟧' := by
  have := hε₁
  have := hε₂
  have := hc
  have := hκ
  have hproj : μ ≫ a.hom ≫ β₁ ≫ (ε₁ ≫ ε₂) =
      c ≫ (κ ≫ (DerivedCategory.singleFunctor A 0).map π)⟦(2 : ℤ)⟧' := by
    rw [← Category.assoc μ, hta, Category.assoc, hP]
  have hmain := augmentation_endpoint_transport U.mapDerivedCategory c μ a.hom a.inv β₁ β₂
    (ε₁ ≫ ε₂) (CategoryTheory.inv (ε₁ ≫ ε₂)) e₁ e₂ a.hom_inv_id hβ (IsIso.hom_inv_id _) he' τ
    αQ _ _ hproj he haug
  have hkey := shifted_single_eq_of_epi U κ π t ρ α _ hα hmain hρ
  rw [← hkey]
  rw [← Category.assoc ε₁, IsIso.hom_inv_id_assoc]

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
