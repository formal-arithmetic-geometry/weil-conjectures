/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionHomReductionSquare

/-! Split compatibility squares for integral finite-extension reduction pairing. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.derivedInternalHomOfUniverses
  CategoryTheory.homComplexFunctor
  WeilConjectures.IntegralHom.totalTensor WeilConjectures.IntegralHom.homModelMap
  WeilConjectures.IntegralHom.projection WeilConjectures.IntegralHom.evaluate

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

private theorem comparison_natural_right {C C' : Type*} [Category* C] [Category* C']
    (T : C × C ⥤ C) (H : Cᵒᵖ × C ⥤ C)
    (T' : C' × C' ⥤ C') (H' : C'ᵒᵖ × C' ⥤ C')
    (adj : ∀ K, (Functor.curry.obj T).obj K ⊣ (Functor.curry.obj H).obj (op K))
    (adj' : ∀ K, (Functor.curry.obj T').obj K ⊣ (Functor.curry.obj H').obj (op K))
    (F : C ⥤ C') (mu : T ⋙ F ≅ F.prod F ⋙ T')
    (K : C) {M M' : C} (g : M ⟶ M') :
    F.map (H.map (Prod.mkHom (𝟙 (op K)) g)) ≫
        (adj' (F.obj K)).homEquiv _ _
          (mu.inv.app (K, H.obj (op K, M')) ≫ F.map ((adj K).counit.app M')) =
      (adj' (F.obj K)).homEquiv _ _
          (mu.inv.app (K, H.obj (op K, M)) ≫ F.map ((adj K).counit.app M)) ≫
        H'.map (Prod.mkHom (𝟙 (op (F.obj K))) (F.map g)) := by
  apply ((adj' (F.obj K)).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  have hr := (adj' (F.obj K)).homEquiv_naturality_right
    (mu.inv.app (K, H.obj (op K, M)) ≫ F.map ((adj K).counit.app M)) (F.map g)
  dsimp only [Functor.curry_obj_obj_map] at hr
  rw [← hr]
  simp only [Functor.id_obj, Equiv.symm_apply_apply]
  have hn := mu.inv.naturality (Prod.mkHom (𝟙 K) (H.map (Prod.mkHom (𝟙 (op K)) g)))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [F.map_id] at hn
  change T'.map (Prod.mkHom (𝟙 (F.obj K))
      (F.map (H.map (Prod.mkHom (𝟙 (op K)) g)))) ≫ _ = _
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp]
  have he := (adj K).counit.naturality g
  change T.map (Prod.mkHom (𝟙 K) (H.map (Prod.mkHom (𝟙 (op K)) g))) ≫
      (adj K).counit.app M' = (adj K).counit.app M ≫ g at he
  rw [he, F.map_comp, Category.assoc]

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
  (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

variable (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)


-- The unchanged statement contains unused HE and DL let bindings.
set_option linter.unusedVariables false in
/-- Finite Verdier reduction square.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, paragraphs 5-7
(blueprint: lem-sf-integral-finite-extension-reduction-pairing).

Proof: Postcompose the finite Hom reduction square with the counit-defined finite dualizing
map. The u_reduction equation and naturality in the second Hom argument yield the beta
square at every quotient level. -/
theorem CoefIntegralFiniteExtensionBetaReductionSquare
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (sE : IntegralVerdier.SignedSymmetry X _ a)
    (sL : IntegralVerdier.SignedSymmetry X _ b)
    (mE : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (mL : ∀ n : ℕ, IntegralHom.ReductionPresentation l L X D hl b n)
    (hnatE : ∀ (K M K' M' : IntegralVerdier.Ambient l E X)
      (f : K ⟶ K') (g : M ⟶ M'),
      a.tensor.map (Prod.mkHom f g) ≫ (sE.swap K' M').hom =
        (sE.swap K M).hom ≫ a.tensor.map (Prod.mkHom g f))
    (hnatL : ∀ (K M K' M' : IntegralVerdier.Ambient l L X)
      (f : K ⟶ K') (g : M ⟶ M'),
      b.tensor.map (Prod.mkHom f g) ≫ (sL.swap K' M').hom =
        (sL.swap K M).hom ≫ b.tensor.map (Prod.mkHom g f))
    (hevalE : ∀ (K K' M : IntegralVerdier.Ambient l E X) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l E X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (a.adjunction K').counit.app M =
        a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app M)
    (hevalL : ∀ (K K' M : IntegralVerdier.Ambient l L X) (f : K' ⟶ K),
      b.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l L X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (b.adjunction K').counit.app M =
        b.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (b.adjunction K).counit.app M)
    (hfinE : ∀ (n : ℕ) (K K' W : DerivedCategory (scalarReductionTarget l E X n))
      (f : K' ⟶ K),
      (mE n).target.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
          (Prod.mkHom f.op (𝟙 W)))) ≫ ((mE n).target.adjunction K').counit.app W =
      (mE n).target.tensor.map (Prod.mkHom f (𝟙 _)) ≫
        ((mE n).target.adjunction K).counit.app W)
    (hfinL : ∀ (n : ℕ) (K K' W : DerivedCategory (scalarReductionTarget l L X n))
      (f : K' ⟶ K),
      (mL n).target.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l L X n)).map
          (Prod.mkHom f.op (𝟙 W)))) ≫ ((mL n).target.adjunction K').counit.app W =
      (mL n).target.tensor.map (Prod.mkHom f (𝟙 _)) ≫
        ((mL n).target.adjunction K).counit.app W) :
    let T := integralScalarExtensionOfUniverses l E L ι X
    let HE := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)
    let DE := IntegralVerdier.dual l E X wE.omega.obj
    let DL := IntegralVerdier.dual l L X wL.omega.obj
    (∀ (n : ℕ) (K : sfIntegralConstructibleCategory l E X),
      let rE := scalarReductionDerivedExtension l E X n
      let rL := scalarReductionDerivedExtension l L X n
      let F := pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)
      let Hn := IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l L X n)
      rL.map (beta l E L ι X D hl wE wL a b K.obj K.property.1) ≫
          IntegralVerdier.comparison l L X D hl (mL n) wL.omega wL.reduction (T.obj K.obj) =
        (quotient l E L ι X n (DE.obj (op K.obj))
          (scalarInternalHom_complete l E X K.obj wE.omega.obj wE.omega.property.1)).hom ≫
          F.map (IntegralVerdier.comparison l E X D hl (mE n) wE.omega wE.reduction K.obj) ≫
          homMap X (integralScalarQuotientSheafMap l E L ι X n)
            (mE n).target (mL n).target (rE.obj K.obj) (integralDualizingFiniteTerm l E D X n) ≫
          Hn.map (Prod.mkHom (quotient l E L ι X n K.obj K.property.1).hom.op
            (finiteU l E L ι X D n))) := by
  dsimp only
  intro n K
  let T := integralScalarExtensionOfUniverses l E L ι X
  let H := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)
  let rE := scalarReductionDerivedExtension l E X n
  let rL := scalarReductionDerivedExtension l L X n
  let F := pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)
  let Hn := IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l L X n)
  let qK := quotient l E L ι X n K.obj K.property.1
  let qW := quotient l E L ι X n wE.omega.obj wE.omega.property.1
  have hc : rL.map (H.map (Prod.mkHom (𝟙 (op (T.obj K.obj)))
        (u l E L ι X D hl wE wL))) ≫
      IntegralHom.comparison l L X D hl (mL n) (T.obj K.obj) wL.omega.obj =
    IntegralHom.comparison l L X D hl (mL n) (T.obj K.obj) (T.obj wE.omega.obj) ≫
      Hn.map (Prod.mkHom (𝟙 (op (rL.obj (T.obj K.obj))))
        (rL.map (u l E L ι X D hl wE wL))) :=
    comparison_natural_right b.tensor H (mL n).target.tensor Hn
      b.adjunction (mL n).target.adjunction rL (mL n).mu
      (T.obj K.obj) (u l E L ι X D hl wE wL)
  have hv := CoefIntegralFiniteExtensionHomReductionSquare l E L ι X D hl wE wL
    a b sE sL mE mL hnatE hnatL hevalE hevalL hfinE hfinL n K wE.omega
  have hu : qW.inv ≫ rL.map (u l E L ι X D hl wE wL) ≫ (wL.reduction n).hom =
      F.map (wE.reduction n).hom ≫ finiteU l E L ι X D n := by
    rw [u_reduction l E L ι X D hl wE wL n]
    exact qW.inv_hom_id_assoc _
  have hf : F.map
        ((IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
          (Prod.mkHom (𝟙 (op (rE.obj K.obj))) (wE.reduction n).hom)) ≫
      homMap X (integralScalarQuotientSheafMap l E L ι X n)
        (mE n).target (mL n).target (rE.obj K.obj) (integralDualizingFiniteTerm l E D X n) =
    homMap X (integralScalarQuotientSheafMap l E L ι X n)
        (mE n).target (mL n).target (rE.obj K.obj) (rE.obj wE.omega.obj) ≫
      Hn.map (Prod.mkHom (𝟙 (op (F.obj (rE.obj K.obj))))
        (F.map (wE.reduction n).hom)) :=
    comparison_natural_right (mE n).target.tensor _ (mL n).target.tensor Hn
      (mE n).target.adjunction (mL n).target.adjunction F
      (PurCompactSupport.scalarTensor (integralScalarQuotientSheafMap l E L ι X n)
        (tensorModel X (mE n).target) (tensorModel X (mL n).target))
      (rE.obj K.obj) (wE.reduction n).hom
  let HE := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)
  let HEn := IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)
  let qH := quotient l E L ι X n (HE.obj (op K.obj, wE.omega.obj))
    (scalarInternalHom_complete l E X K.obj wE.omega.obj wE.omega.property.1)
  change rL.map (v l E L ι X a b K.obj wE.omega.obj K.property.1 wE.omega.property.1 ≫
      H.map (Prod.mkHom (𝟙 (op (T.obj K.obj))) (u l E L ι X D hl wE wL))) ≫
      (IntegralHom.comparison l L X D hl (mL n) (T.obj K.obj) wL.omega.obj ≫
        Hn.map (Prod.mkHom (𝟙 (op (rL.obj (T.obj K.obj)))) (wL.reduction n).hom)) =
    qH.hom ≫ F.map (IntegralHom.comparison l E X D hl (mE n) K.obj wE.omega.obj ≫
      HEn.map (Prod.mkHom (𝟙 (op (rE.obj K.obj))) (wE.reduction n).hom)) ≫
      homMap X (integralScalarQuotientSheafMap l E L ι X n)
        (mE n).target (mL n).target (rE.obj K.obj) (integralDualizingFiniteTerm l E D X n) ≫
      Hn.map (Prod.mkHom qK.hom.op (finiteU l E L ι X D n))
  rw [rL.map_comp]
  rw [Category.assoc, ← Category.assoc (rL.map (H.map _)), hc]
  simp only [Category.assoc]
  rw [← Category.assoc (rL.map (v l E L ι X a b K.obj wE.omega.obj
    K.property.1 wE.omega.property.1)), hv]
  simp only [Category.assoc]
  rw [← Hn.map_comp, ← Hn.map_comp]
  simp only [prod_comp, Category.comp_id]
  rw [hu]
  rw [F.map_comp, Category.assoc,
    ← Category.assoc (F.map (HEn.map _)), hf]
  simp only [Category.assoc, ← Hn.map_comp, prod_comp]
  erw [Category.comp_id, Category.id_comp]

end WeilConjectures.IntegralFiniteExtension
