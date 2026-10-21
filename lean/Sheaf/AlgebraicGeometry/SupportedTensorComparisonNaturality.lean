/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module
public import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
public import Sheaf.CategoryTheory.DerivedExactMate
import all Sheaf.AlgebraicGeometry.SupportedExteriorProduct
import all Sheaf.AlgebraicGeometry.SupportedCoefficientDerivedOpenMate
/-! # Naturality of normalized derived tensor comparisons

The normalization on total complexes makes the derived comparison functorial in
all three exact coefficient functors.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
@[reassoc]
private theorem exactMap_complex
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F G : C ⥤ D} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (α : F ⟶ G) (P : CochainComplex C ℤ) :
    (Functor.exactDerivedMap α).app (DerivedCategory.Q.obj P) ≫
        G.mapDerivedCategoryFactors.hom.app P =
      F.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (.up ℤ)).app P) := by
  have fac (H : C ⥤ D) [H.Additive]
      [PreservesFiniteLimits H] [PreservesFiniteColimits H] :
      H.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
        H.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app P) ≫
          H.mapDerivedCategoryFactors.hom.app P ≫
            (DerivedCategory.quotientCompQhIso D).inv.app
              ((H.mapHomologicalComplex (.up ℤ)).obj P) := by
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    dsimp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
    erw [DerivedCategory.Qh.map_id, Category.comp_id]
  have h := exactMap_fac α ((HomotopyCategory.quotient C (.up ℤ)).obj P)
  rw [fac F, fac G] at h
  have hnt : (NatTrans.mapHomotopyCategory α (.up ℤ)).app
      ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      (HomotopyCategory.quotient D (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (.up ℤ)).app P) := rfl
  rw [hnt] at h
  simp only [Category.assoc] at h
  rw [← NatTrans.naturality_assoc,
    ← DerivedCategory.quotientCompQhIso_inv_naturality] at h
  apply (cancel_epi
    (F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app P))).1
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso D).inv.app
    ((G.mapHomologicalComplex (.up ℤ)).obj P))).1
  simpa only [Category.assoc] using h

section Tensor
variable {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
  {D : Type w} [Category.{u + 1} D] [Abelian D]
  [IsGrothendieckAbelian.{u + 1} D] [HasDerivedCategory.{u + 1} D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution D]
  (G F₁ F₂ G' F₁' F₂' : C ⥤ D)
  [G.Additive] [F₁.Additive] [F₂.Additive]
  [G'.Additive] [F₁'.Additive] [F₂'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits F₁'] [PreservesFiniteColimits F₁']
  [PreservesFiniteLimits F₂'] [PreservesFiniteColimits F₂']

private def comparisonNat
    (t : supportedDerivedComparisonHom G F₁ F₂)
    (ht : ∀ M M' N N' a b,
      G.mapDerivedCategory.map (a ⊗ₘ b) ≫ t M' N' =
        t M N ≫ (F₁.mapDerivedCategory.map a ⊗ₘ F₂.mapDerivedCategory.map b)) :
    (Functor.postcompose₂.obj G.mapDerivedCategory).obj
        (curriedTensor (DerivedCategory C)) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
        F₂.mapDerivedCategory).obj (curriedTensor (DerivedCategory D)) where
  app M :=
    { app N := t M N
      naturality N N' b := by
        change G.mapDerivedCategory.map (M ◁ b) ≫ t M N' =
          t M N ≫ (F₁.mapDerivedCategory.obj M ◁ F₂.mapDerivedCategory.map b)
        simpa only [id_tensorHom, CategoryTheory.Functor.map_id] using ht M M N N' (𝟙 M) b }
  naturality M M' a := by
    ext N
    change G.mapDerivedCategory.map (a ▷ N) ≫ t M' N =
      t M N ≫ (F₁.mapDerivedCategory.map a ▷ F₂.mapDerivedCategory.obj N)
    simpa only [tensorHom_id, CategoryTheory.Functor.map_id] using ht M M' N N a (𝟙 N)

private theorem derived_tensor_naturality [F₂.PreservesFlat] [F₂.IsLeftAdjoint]
    (τ : (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor (CochainComplex C ℤ)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
        (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _))
    (τ' : (Functor.postcompose₂.obj (G'.mapHomologicalComplex (.up ℤ))).obj
        (curriedTensor (CochainComplex C ℤ)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁'.mapHomologicalComplex (.up ℤ))).obj
        (F₂'.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _))
    (t : supportedDerivedComparisonHom G F₁ F₂)
    (t' : supportedDerivedComparisonHom G' F₁' F₂')
    (ht : supportedDerivedComparisonCondition G F₁ F₂ τ t)
    (ht' : supportedDerivedComparisonCondition G' F₁' F₂' τ' t')
    (a₀ : G' ⟶ G) (a₁ : F₁' ⟶ F₁) (a₂ : F₂' ⟶ F₂)
    (ha : ∀ P Q : CochainComplex C ℤ,
      (NatTrans.mapHomologicalComplex a₀ (.up ℤ)).app (P ⊗ Q) ≫ (τ.app P).app Q =
        (τ'.app P).app Q ≫
          ((NatTrans.mapHomologicalComplex a₁ (.up ℤ)).app P ⊗ₘ
            (NatTrans.mapHomologicalComplex a₂ (.up ℤ)).app Q))
    (M N : DerivedCategory C) :
    (Functor.exactDerivedMap a₀).app (M ⊗ N) ≫ t M N =
      t' M N ≫ ((Functor.exactDerivedMap a₁).app M ⊗ₘ
        (Functor.exactDerivedMap a₂).app N) := by
  let U := (Functor.postcompose₂.obj G'.mapDerivedCategory).obj
    (curriedTensor (DerivedCategory C))
  let V := (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
    F₂.mapDerivedCategory).obj (curriedTensor (DerivedCategory D))
  let γ := comparisonNat G F₁ F₂ t ht.1
  let γ' := comparisonNat G' F₁' F₂' t' ht'.1
  let α₀ := (Functor.postcompose₂.map (Functor.exactDerivedMap a₀)).app
    (curriedTensor (DerivedCategory C))
  let α₁₂ :
      (((Functor.whiskeringLeft₂ _).obj F₁'.mapDerivedCategory).obj
        F₂'.mapDerivedCategory).obj (curriedTensor (DerivedCategory D)) ⟶ V :=
    { app M :=
        { app N := (Functor.exactDerivedMap a₁).app M ⊗ₘ
            (Functor.exactDerivedMap a₂).app N
          naturality N N' b := by
            change (F₁'.mapDerivedCategory.obj M ◁ F₂'.mapDerivedCategory.map b) ≫
              (_ ⊗ₘ _) = (_ ⊗ₘ _) ≫ (F₁.mapDerivedCategory.obj M ◁ F₂.mapDerivedCategory.map b)
            rw [← id_tensorHom, ← id_tensorHom]
            simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
            rw [(Functor.exactDerivedMap a₂).naturality] }
      naturality M M' a := by
        ext N
        change (F₁'.mapDerivedCategory.map a ▷ F₂'.mapDerivedCategory.obj N) ≫
          (_ ⊗ₘ _) = (_ ⊗ₘ _) ≫ (F₁.mapDerivedCategory.map a ▷ F₂.mapDerivedCategory.obj N)
        rw [← tensorHom_id, ← tensorHom_id]
        simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
        rw [(Functor.exactDerivedMap a₁).naturality] }
  have : V.IsLeftDerivedFunctor₂ (mixedTensorCounit F₁ F₂)
      (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.quasiIso C (.up ℤ)) := mixedTensor_isLeftDerived F₁ F₂
  have h : α₀ ≫ γ = γ' ≫ α₁₂ := by
    apply V.leftDerived₂_ext (mixedTensorCounit F₁ F₂)
      (HomologicalComplex.quasiIso C (.up ℤ))
      (HomologicalComplex.quasiIso C (.up ℤ)) U
    ext P Q
    change ((Functor.exactDerivedMap a₀).app _ ≫ t _ _) ≫ _ =
      (t' _ _ ≫ ((Functor.exactDerivedMap a₁).app _ ⊗ₘ
        (Functor.exactDerivedMap a₂).app _)) ≫ _
    have hn := ht.2 P Q
    have hn' := ht'.2 P Q
    simp only [tensorLocalization_model_eq] at hn hn'
    have hα : ((mixedTensorCounit F₁ F₂).app P).app Q =
        (F₁.mapDerivedCategoryFactors.hom.app P ⊗ₘ
          F₂.mapDerivedCategoryFactors.hom.app Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
          ((F₂.mapHomologicalComplex (.up ℤ)).obj Q) := by
      change (_ ▷ _) ≫ (_ ◁ _) ≫ _ = (_ ⊗ₘ _) ≫ _
      rw [MonoidalCategory.tensorHom_def, Category.assoc]
      rfl
    rw [hα]
    simp only [Category.assoc]
    rw [← hn, ← (Functor.exactDerivedMap a₀).naturality_assoc,
      exactMap_complex_assoc]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc, exactMap_complex, exactMap_complex,
      ← tensorHom_comp_tensorHom, Category.assoc,
      Functor.LaxMonoidal.μ_natural]
    rw [← reassoc_of% hn']
    simp only [← CategoryTheory.Functor.map_comp]
    rw [ha]
  exact congrArg (fun η ↦ (η.app M).app N) h

omit [HasDerivedCategory C] [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory D] [Abelian.HasFunctorialFlatResolution D]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits F₁'] [PreservesFiniteColimits F₁']
  [PreservesFiniteLimits F₂'] [PreservesFiniteColimits F₂'] in
private theorem complex_tensor_naturality [G.IsLeftAdjoint] [G'.IsLeftAdjoint]
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F₁).obj F₂).obj (curriedTensor D))
    (τ' : (Functor.postcompose₂.obj G').obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F₁').obj F₂').obj (curriedTensor D))
    (a₀ : G' ⟶ G) (a₁ : F₁' ⟶ F₁) (a₂ : F₂' ⟶ F₂)
    (ha : ∀ M N, a₀.app (M ⊗ N) ≫ (τ.app M).app N =
      (τ'.app M).app N ≫ (a₁.app M ⊗ₘ a₂.app N))
    (P Q : CochainComplex C ℤ) :
    (NatTrans.mapHomologicalComplex a₀ (.up ℤ)).app (P ⊗ Q) ≫
      HomologicalComplex.mapBifunctorComparison τ (.up ℤ) P Q =
    HomologicalComplex.mapBifunctorComparison τ' (.up ℤ) P Q ≫
      ((NatTrans.mapHomologicalComplex a₁ (.up ℤ)).app P ⊗ₘ
        (NatTrans.mapHomologicalComplex a₂ (.up ℤ)).app Q) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f]
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map G'
  intro r s hrs
  rw [← Category.assoc]
  erw [a₀.naturality]
  rw [Category.assoc]
  erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX]
  erw [HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX_assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simpa only [HomologicalComplex.mapBifunctorComparisonApp,
    NatTrans.mapHomologicalComplex_app_f, curriedTensor, MonoidalCategory.tensorHom_def,
    Category.assoc, Functor.mapHomologicalComplex, Functor.comp_obj] using
    congrArg (fun k ↦ k ≫ HomologicalComplex.ιMapBifunctor
      ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
      ((F₂.mapHomologicalComplex (.up ℤ)).obj Q)
      (curriedTensor D) (.up ℤ) r s n hrs) (ha (P.X r) (Q.X s))


/-- A square of exact coefficient tensor comparisons remains commutative after derivation.
Source: Stacks Tag 0F1E, naturality of the tensor pairing under coefficient maps
(blueprint: lem-pur-supported-tensor-comparison-naturality).
Proof: the ordinary square gives the square on each bidegree summand of the signed
total complexes. The universal property of their coproducts gives equality of chain
maps. The mixed tensor functor is the left derived bifunctor of this complex tensor:
the second coefficient functor preserves flat objects. Its universal property
therefore tests the derived square after precomposition with the localization
comparison. Both normalizations then reduce it to the proved complex square. -/
theorem supportedDerivedComparison_naturality
    [G.IsLeftAdjoint] [G'.IsLeftAdjoint] [F₂.PreservesFlat] [F₂.IsLeftAdjoint]
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F₁).obj F₂).obj (curriedTensor D))
    (τ' : (Functor.postcompose₂.obj G').obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F₁').obj F₂').obj (curriedTensor D))
    (t : supportedDerivedComparisonHom G F₁ F₂)
    (t' : supportedDerivedComparisonHom G' F₁' F₂')
    (ht : supportedDerivedComparisonCondition G F₁ F₂
      (HomologicalComplex.mapBifunctorComparisonNatTrans τ (.up ℤ)) t)
    (ht' : supportedDerivedComparisonCondition G' F₁' F₂'
      (HomologicalComplex.mapBifunctorComparisonNatTrans τ' (.up ℤ)) t')
    (a₀ : G' ⟶ G) (a₁ : F₁' ⟶ F₁) (a₂ : F₂' ⟶ F₂)
    (ha : ∀ M N, a₀.app (M ⊗ N) ≫ (τ.app M).app N =
      (τ'.app M).app N ≫ (a₁.app M ⊗ₘ a₂.app N))
    (M N : DerivedCategory C) :
    (Functor.exactDerivedMap a₀).app (M ⊗ N) ≫ t M N =
      t' M N ≫ ((Functor.exactDerivedMap a₁).app M ⊗ₘ
        (Functor.exactDerivedMap a₂).app N) := by
  exact derived_tensor_naturality G F₁ F₂ G' F₁' F₂' _ _ t t' ht ht' a₀ a₁ a₂
    (complex_tensor_naturality G F₁ F₂ G' F₁' F₂' τ τ' a₀ a₁ a₂ ha) M N

end Tensor
end AlgebraicGeometry.Etale

