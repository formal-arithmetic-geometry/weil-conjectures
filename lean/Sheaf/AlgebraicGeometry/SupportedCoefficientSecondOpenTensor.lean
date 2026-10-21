/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.AlgebraicGeometry.SupportedCoefficientOpenTensor
import Sheaf.AlgebraicGeometry.SupportedCoefficientOrdinarySecondOpenTensor
import Sheaf.AlgebraicGeometry.SupportedTensorComplexSquare
import Sheaf.CategoryTheory.DerivedExactMate
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.SixFunctors.OpenClosed.SupportedSections

/-!
# Open pullback in the second coefficient

Source: Stacks Project, Tags 09XP and 0F1E, the coefficient calculation in
lem-pur-supported-product-localization, steps 5 and 11.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale

/-- Pull the uncut first supported coefficient to the second open product.
Source: Stacks Tag 0F1E (blueprint: lem-pur-supported-coefficient-second-open-tensor). -/
noncomputable def supportSecondOpenFirstCoefficientMap (A : Type (u + 1)) [CommRing A]
    {S X Y B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X)
    [IsClosedImmersion b] (V : Y.Opens) (M : DerivedCategory (ModuleCat.{u + 1} A)) :
    (supportedFirstCoefficients A f (V.ι ≫ g) b).mapDerivedCategory.obj M ⟶
      (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.obj
        ((supportedFirstCoefficients A f g b).mapDerivedCategory.obj M) :=
  (supportFirstCoefficientProjectionIso A f (V.ι ≫ g) b).hom.app M ≫
    (supportPullbackProjectionIso (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
      (pullback.fst f g) (pullback.fst f (V.ι ≫ g))
      (supportedSecondOpenMap_fst f g V)
      ((supportedCoefficients A b).mapDerivedCategory.obj M)).inv ≫
    (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.map
      ((supportFirstCoefficientProjectionIso A f g b).inv.app M)

/-- Pull the second supported coefficient to the open product by the mate of restriction.
Source: Stacks Tag 0F1E (blueprint: lem-pur-supported-coefficient-second-open-tensor). -/
noncomputable def supportSecondOpenCoefficientMap (A : Type (u + 1)) [CommRing A]
    {S X Y D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y)
    [IsClosedImmersion d] (V : Y.Opens) (N : DerivedCategory (ModuleCat.{u + 1} A)) :
    (supportedSecondCoefficients A f (V.ι ≫ g) (supportOnOpen d V)).mapDerivedCategory.obj N ⟶
      (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.obj
        ((supportedSecondCoefficients A f g d).mapDerivedCategory.obj N) :=
  (supportSecondCoefficientProjectionIso A f (V.ι ≫ g) (supportOnOpen d V)).hom.app N ≫
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f (V.ι ≫ g))).leftDerivedFunctor.map
      ((supportCoefficientOpenMate A V.ι d (supportOnOpen d V)
        (supportOnOpen_complement d V)).app N) ≫
    (supportPullbackSquareIso (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
      (pullback.snd f g) (pullback.snd f (V.ι ≫ g)) V.ι
      (supportedSecondOpenMap_snd f g V)
      ((supportedCoefficients A d).mapDerivedCategory.obj N)).inv ≫
    (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.map
      ((supportSecondCoefficientProjectionIso A f g d).inv.app N)

attribute [local instance] supportedHasSheafify supportedHasWeakSheafify
-- Match the symmetry projection used by the generic coefficient constructions.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance high] sheafBraidedCategory

@[reassoc] private theorem map_natIso_inv_hom
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : D ⥤ E) {F G : C ⥤ D} (e : F ≅ G) (X : C) :
    J.map (e.inv.app X) ≫ J.map (e.hom.app X) = 𝟙 _ := by
  rw [← J.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]

section ExactFactors

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

private theorem factorsh_quotient (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 _) ≫ F.mapDerivedCategoryFactors.hom.app P ≫
    𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.comp_id]

private theorem exactMap_fac_h {F' : C ⥤ D} [F'.Additive]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (α : F' ⟶ F) (K : HomotopyCategory C (.up ℤ)) :
    (Functor.exactDerivedMap α).app (DerivedCategory.Qh.obj K) ≫
        F.mapDerivedCategoryFactorsh.hom.app K =
      F'.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory α (.up ℤ)).app K) := by
  simp only [Functor.exactDerivedMap, Localization.liftNatTrans_app,
    Functor.whiskerRight_app, Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  rfl

private theorem exactMap_fac {F' : C ⥤ D} [F'.Additive]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (α : F' ⟶ F) (P : CochainComplex C ℤ) :
    (Functor.exactDerivedMap α).app (DerivedCategory.Q.obj P) ≫
        F.mapDerivedCategoryFactors.hom.app P =
      F'.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (.up ℤ)).app P) := by
  have h := exactMap_fac_h F α ((HomotopyCategory.quotient C (.up ℤ)).obj P)
  rw [factorsh_quotient, factorsh_quotient] at h
  exact h

private theorem exactMap_iso {F' : C ⥤ D} [F'.Additive]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F'] (e : F' ≅ F) :
    Functor.exactDerivedMap e.hom = (Functor.mapDerivedCategoryNatIso e).hom := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro P
  apply (cancel_mono (F.mapDerivedCategoryFactors.hom.app P)).1
  rw [exactMap_fac, Functor.mapDerivedCategoryNatIso_fac]

omit [HasDerivedCategory C] [HasDerivedCategory D]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
private theorem mapH_quotient (P : CochainComplex C ℤ) :
    (F.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      (HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P) := rfl

private theorem Qh_quotient_obj (P : CochainComplex C ℤ) :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj P) =
      DerivedCategory.Q.obj P := rfl

private theorem Qh_quotient_map {P Q : CochainComplex C ℤ} (f : P ⟶ Q) :
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map f) =
      DerivedCategory.Q.map f := rfl

end ExactFactors

section TensorFactors

universe w₀

variable {C : Type*} [Category.{w₀} C] [Abelian C]
  [IsGrothendieckAbelian.{w₀} C] [HasDerivedCategory.{w₀} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

omit [HasDerivedCategory C] [Abelian.HasFunctorialFlatResolution C] in
private theorem quotient_tensor (P Q : CochainComplex C ℤ) :
    ((HomotopyCategory.quotient C (.up ℤ)).obj P ⊗
      (HomotopyCategory.quotient C (.up ℤ)).obj Q) =
      (HomotopyCategory.quotient C (.up ℤ)).obj (P ⊗ Q) := rfl

private theorem μQ_eq (P Q : CochainComplex C ℤ) :
    Functor.LaxMonoidal.μ DerivedCategory.Q P Q =
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        ((HomotopyCategory.quotient C (.up ℤ)).obj P)
        ((HomotopyCategory.quotient C (.up ℤ)).obj Q) := by
  change (𝟙 _ ⊗ₘ 𝟙 _) ≫ (_ ≫ DerivedCategory.Qh.map (𝟙 _)) ≫ 𝟙 _ = _
  simp only [tensorHom_id, id_whiskerRight, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]

end TensorFactors



section CochainTensorFactor

universe w
variable {C D : Type*} [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w} C] [IsGrothendieckAbelian.{w} D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [MonoidalClosed C] [MonoidalClosed D] [BraidedCategory C] [BraidedCategory D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [F.Monoidal] [PreservesColimitsOfSize.{0, 0} F]
  (κ : ∀ K L : DerivedCategory C,
    F.mapDerivedCategory.obj (K ⊗ L) ⟶
      F.mapDerivedCategory.obj K ⊗ F.mapDerivedCategory.obj L)

/-- Keep the cochain normalization folded when specializing its coefficient category. -/
@[irreducible]
private noncomputable def tensorFactorCondition (P Q : CochainComplex C ℤ) : Prop :=
  κ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
    (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ
      F.mapDerivedCategoryFactors.hom.app Q) ≫
    Functor.LaxMonoidal.μ DerivedCategory.Q
      ((F.mapHomologicalComplex (.up ℤ)).obj P)
      ((F.mapHomologicalComplex (.up ℤ)).obj Q) =
  F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
    F.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
    DerivedCategory.Q.map
      (Functor.OplaxMonoidal.δ (F.mapHomologicalComplex (.up ℤ)) P Q)

private theorem tensor_fac_of_homotopy
    (hf : ∀ K L : HomotopyCategory C (.up ℤ),
      κ (DerivedCategory.Qh.obj K) (DerivedCategory.Qh.obj L) ≫
        (F.mapDerivedCategoryFactorsh.hom.app K ⊗ₘ
          F.mapDerivedCategoryFactorsh.hom.app L) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Qh
          ((F.mapHomotopyCategory (.up ℤ)).obj K)
          ((F.mapHomotopyCategory (.up ℤ)).obj L) =
      F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Qh K L) ≫
        F.mapDerivedCategoryFactorsh.hom.app (K ⊗ L) ≫
        DerivedCategory.Qh.map
          (Functor.OplaxMonoidal.δ (F.mapHomotopyCategory (.up ℤ)) K L))
    (P Q : CochainComplex C ℤ) : tensorFactorCondition F κ P Q := by
  unfold tensorFactorCondition
  have e := hf ((HomotopyCategory.quotient C (.up ℤ)).obj P)
    ((HomotopyCategory.quotient C (.up ℤ)).obj Q)
  simpa only [mapH_quotient, quotient_tensor, HomotopyCategory.quotient_obj_as,
    factorsh_quotient, ← μQ_eq, Functor.mapHomotopyCategory_δ,
    Functor.OplaxMonoidal.mapHomotopyCategoryδNatTrans_app_app,
    ← Functor.mapCochainComplex_δ, Qh_quotient_obj, Qh_quotient_map] using e

private theorem tensorFactorCondition_congr
    (κ' : ∀ K L : DerivedCategory C,
      F.mapDerivedCategory.obj (K ⊗ L) ⟶
        F.mapDerivedCategory.obj K ⊗ F.mapDerivedCategory.obj L)
    (hκ : ∀ K L, κ K L = κ' K L) (P Q : CochainComplex C ℤ)
    (hf : tensorFactorCondition F κ P Q) : tensorFactorCondition F κ' P Q := by
  have he : κ = κ' := funext (fun K => funext (hκ K))
  cases he
  exact hf

end CochainTensorFactor

section ModelSquare

variable {C D E C' D' E' : Type*}
  [Category C] [Category D] [Category E]
  [Category C'] [Category D'] [Category E']
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [MonoidalCategory C'] [MonoidalCategory D'] [MonoidalCategory E']
  (L : C ⥤ C') (R : D ⥤ D') (S : E ⥤ E')
  [L.LaxMonoidal] [R.LaxMonoidal] [S.LaxMonoidal]
  (G F₁ F₂ : C ⥤ D) (G' F₁' F₂' : C ⥤ E) (H : D ⥤ E) [H.OplaxMonoidal]
  (DG DF₁ DF₂ : C' ⥤ D') (DG' DF₁' DF₂' : C' ⥤ E') (DH : D' ⥤ E')
  (eG : L ⋙ DG ≅ G ⋙ R) (e₁ : L ⋙ DF₁ ≅ F₁ ⋙ R)
  (e₂ : L ⋙ DF₂ ≅ F₂ ⋙ R) (eG' : L ⋙ DG' ≅ G' ⋙ S)
  (e₁' : L ⋙ DF₁' ≅ F₁' ⋙ S) (e₂' : L ⋙ DF₂' ≅ F₂' ⋙ S)
  (eH : R ⋙ DH ≅ H ⋙ S)
  (a₀ : G' ⟶ G ⋙ H) (a₁ : F₁' ⟶ F₁ ⋙ H) (a₂ : F₂' ⟶ F₂ ⋙ H)
  (d₀ : DG' ⟶ DG ⋙ DH) (d₁ : DF₁' ⟶ DF₁ ⋙ DH) (d₂ : DF₂' ⟶ DF₂ ⋙ DH)
  (κ : (Functor.postcompose₂.obj DH).obj (curriedTensor D') ⟶
    (((Functor.whiskeringLeft₂ E').obj DH).obj DH).obj (curriedTensor E'))

private theorem tensorSquare_model
    (τ : ∀ M N, G.obj (M ⊗ N) ⟶ F₁.obj M ⊗ F₂.obj N)
    (τ' : ∀ M N, G'.obj (M ⊗ N) ⟶ F₁'.obj M ⊗ F₂'.obj N)
    (t : ∀ M N, DG.obj (M ⊗ N) ⟶ DF₁.obj M ⊗ DF₂.obj N)
    (t' : ∀ M N, DG'.obj (M ⊗ N) ⟶ DF₁'.obj M ⊗ DF₂'.obj N)
    (h₀ : ∀ P, d₀.app (L.obj P) ≫ DH.map (eG.hom.app P) ≫ eH.hom.app (G.obj P) =
      eG'.hom.app P ≫ S.map (a₀.app P))
    (h₁ : ∀ P, d₁.app (L.obj P) ≫ DH.map (e₁.hom.app P) ≫ eH.hom.app (F₁.obj P) =
      e₁'.hom.app P ≫ S.map (a₁.app P))
    (h₂ : ∀ P, d₂.app (L.obj P) ≫ DH.map (e₂.hom.app P) ≫ eH.hom.app (F₂.obj P) =
      e₂'.hom.app P ≫ S.map (a₂.app P))
    (hκ : ∀ P Q, (κ.app (R.obj P)).app (R.obj Q) ≫
      (eH.hom.app P ⊗ₘ eH.hom.app Q) ≫
        Functor.LaxMonoidal.μ S (H.obj P) (H.obj Q) =
      DH.map (Functor.LaxMonoidal.μ R P Q) ≫ eH.hom.app (P ⊗ Q) ≫
        S.map (Functor.OplaxMonoidal.δ H P Q))
    (ht : ∀ P Q, DG.map (Functor.LaxMonoidal.μ L P Q) ≫ eG.hom.app (P ⊗ Q) ≫
      R.map (τ P Q) = t (L.obj P) (L.obj Q) ≫
        (e₁.hom.app P ⊗ₘ e₂.hom.app Q) ≫ Functor.LaxMonoidal.μ R _ _)
    (ht' : ∀ P Q, DG'.map (Functor.LaxMonoidal.μ L P Q) ≫ eG'.hom.app (P ⊗ Q) ≫
      S.map (τ' P Q) = t' (L.obj P) (L.obj Q) ≫
        (e₁'.hom.app P ⊗ₘ e₂'.hom.app Q) ≫ Functor.LaxMonoidal.μ S _ _)
    (ha : ∀ P Q, a₀.app (P ⊗ Q) ≫ H.map (τ P Q) ≫
      Functor.OplaxMonoidal.δ H (F₁.obj P) (F₂.obj Q) =
      τ' P Q ≫ (a₁.app P ⊗ₘ a₂.app Q))
    (P Q : C) [Mono (Functor.LaxMonoidal.μ S (H.obj (F₁.obj P)) (H.obj (F₂.obj Q)))] :
    d₀.app (L.obj P ⊗ L.obj Q) ≫ DH.map (t (L.obj P) (L.obj Q)) ≫
      (κ.app (DF₁.obj (L.obj P))).app (DF₂.obj (L.obj Q)) =
    t' (L.obj P) (L.obj Q) ≫ (d₁.app (L.obj P) ⊗ₘ d₂.app (L.obj Q)) := by
  apply (cancel_mono ((DH.map (e₁.hom.app P) ≫ eH.hom.app (F₁.obj P) ⊗ₘ
      DH.map (e₂.hom.app Q) ≫ eH.hom.app (F₂.obj Q)) ≫
        Functor.LaxMonoidal.μ S _ _)).1
  have hn := congr_app (κ.naturality (e₁.hom.app P)) (DF₂.obj (L.obj Q))
  have hm := (κ.app (R.obj (F₁.obj P))).naturality (e₂.hom.app Q)
  change DH.map (e₁.hom.app P ▷ _) ≫ _ =
    _ ≫ (DH.map (e₁.hom.app P) ▷ _) at hn
  change DH.map (_ ◁ e₂.hom.app Q) ≫ _ =
    _ ≫ (_ ◁ DH.map (e₂.hom.app Q)) at hm
  have hnat : DH.map (e₁.hom.app P ⊗ₘ e₂.hom.app Q) ≫
      (κ.app (R.obj (F₁.obj P))).app (R.obj (F₂.obj Q)) =
    (κ.app (DF₁.obj (L.obj P))).app (DF₂.obj (L.obj Q)) ≫
      (DH.map (e₁.hom.app P) ⊗ₘ DH.map (e₂.hom.app Q)) := by
    rw [MonoidalCategory.tensorHom_def, Functor.map_comp, Category.assoc]
    erw [hm, ← Category.assoc, hn]
    simp only [MonoidalCategory.tensorHom_def, Category.assoc]
    rfl
  simp only [Category.assoc, ← tensorHom_comp_tensorHom]
  rw [← Category.assoc _ (DH.map (e₁.hom.app P) ⊗ₘ DH.map (e₂.hom.app Q)),
    ← hnat]
  simp only [Category.assoc]
  rw [hκ]
  simp only [← DH.map_comp_assoc]
  rw [← ht]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (eH.hom.naturality (τ P Q))]
  erw [← reassoc_of% (d₀.naturality (Functor.LaxMonoidal.μ L P Q))]
  rw [reassoc_of% (h₀ (P ⊗ Q))]
  rw [← S.map_comp, ← S.map_comp, ha, S.map_comp]
  rw [reassoc_of% (ht' P Q)]
  rw [← Functor.LaxMonoidal.μ_natural]
  erw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  rw [← h₁, ← h₂]
  erw [tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rfl

private theorem tensorComparison_natural
    {P P' Q Q' : D'} (a : P ⟶ P') (b : Q ⟶ Q') :
    DH.map (a ⊗ₘ b) ≫ (κ.app P').app Q' =
      (κ.app P).app Q ≫ (DH.map a ⊗ₘ DH.map b) := by
  have hn := congr_app (κ.naturality a) Q
  have hm := (κ.app P').naturality b
  change DH.map (a ▷ _) ≫ _ = _ ≫ (DH.map a ▷ _) at hn
  change DH.map (_ ◁ b) ≫ _ = _ ≫ (_ ◁ DH.map b) at hm
  rw [MonoidalCategory.tensorHom_def, Functor.map_comp, Category.assoc]
  erw [hm, ← Category.assoc, hn]
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]

private theorem tensorSquare_left_natural
    (t : ∀ M N, DG.obj (M ⊗ N) ⟶ DF₁.obj M ⊗ DF₂.obj N)
    (ht : ∀ M M' N N' (a : M ⟶ M') (b : N ⟶ N'),
      DG.map (a ⊗ₘ b) ≫ t M' N' = t M N ≫ (DF₁.map a ⊗ₘ DF₂.map b))
    {M M' N N' : C'} (a : M ⟶ M') (b : N ⟶ N') :
    DG'.map (a ⊗ₘ b) ≫
        (d₀.app (M' ⊗ N') ≫ DH.map (t M' N') ≫ (κ.app (DF₁.obj M')).app (DF₂.obj N')) =
      (d₀.app (M ⊗ N) ≫ DH.map (t M N) ≫ (κ.app (DF₁.obj M)).app (DF₂.obj N)) ≫
        (DH.map (DF₁.map a) ⊗ₘ DH.map (DF₂.map b)) := by
  rw [← Category.assoc, d₀.naturality]
  dsimp only [Functor.comp_map]
  simp only [Category.assoc]
  rw [← DH.map_comp_assoc, ht, DH.map_comp, Category.assoc,
    tensorComparison_natural]

omit [MonoidalCategory D'] in
private theorem tensorSquare_right_natural
    (t' : ∀ M N, DG'.obj (M ⊗ N) ⟶ DF₁'.obj M ⊗ DF₂'.obj N)
    (ht' : ∀ M M' N N' (a : M ⟶ M') (b : N ⟶ N'),
      DG'.map (a ⊗ₘ b) ≫ t' M' N' = t' M N ≫ (DF₁'.map a ⊗ₘ DF₂'.map b))
    {M M' N N' : C'} (a : M ⟶ M') (b : N ⟶ N') :
    DG'.map (a ⊗ₘ b) ≫ (t' M' N' ≫ (d₁.app M' ⊗ₘ d₂.app N')) =
      (t' M N ≫ (d₁.app M ⊗ₘ d₂.app N)) ≫
        (DH.map (DF₁.map a) ⊗ₘ DH.map (DF₂.map b)) := by
  rw [← Category.assoc, ht']
  simp only [Category.assoc, tensorHom_comp_tensorHom]
  erw [d₁.naturality, d₂.naturality]
  rfl

end ModelSquare

private theorem family_eq_of_models
    {C D E : Type*} [Category C] [Category D] [Category E] [MonoidalCategory C]
    [MonoidalCategory E] (G : C ⥤ D) (F₁ F₂ : C ⥤ E) (H : E ⥤ D)
    (s t : ∀ M N, G.obj (M ⊗ N) ⟶ H.obj (F₁.obj M ⊗ F₂.obj N))
    (hs : ∀ M M' N N' (a : M ⟶ M') (b : N ⟶ N'),
      G.map (a ⊗ₘ b) ≫ s M' N' = s M N ≫ H.map (F₁.map a ⊗ₘ F₂.map b))
    (ht : ∀ M M' N N' (a : M ⟶ M') (b : N ⟶ N'),
      G.map (a ⊗ₘ b) ≫ t M' N' = t M N ≫ H.map (F₁.map a ⊗ₘ F₂.map b))
    (hmodels : ∀ M N, ∃ P Q, s P Q = t P Q ∧ Nonempty (P ≅ M) ∧ Nonempty (Q ≅ N))
    (M N : C) : s M N = t M N := by
  obtain ⟨P, Q, h, ⟨e⟩, ⟨d⟩⟩ := hmodels M N
  apply (cancel_epi (G.map (e.hom ⊗ₘ d.hom))).1
  rw [hs, ht, h]



section ExactNaturality

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

private theorem exactMap_comp
    {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (α : F ⟶ G) (β : G ⟶ H) :
    Functor.exactDerivedMap (α ≫ β) =
      Functor.exactDerivedMap α ≫ Functor.exactDerivedMap β := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro P
  apply (cancel_mono (H.mapDerivedCategoryFactors.hom.app P)).1
  simp only [NatTrans.comp_app, Category.assoc]
  rw [exactMap_fac, exactMap_fac, ← Category.assoc, exactMap_fac]
  simp only [NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]

private theorem exactMap_whiskerRight
    {F F' : C ⥤ D} (G : D ⥤ E) [F.Additive] [F'.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (α : F' ⟶ F) :
    Functor.exactDerivedMap (Functor.whiskerRight α G) ≫
        (Functor.mapDerivedCategoryCompIso F G).hom =
      (Functor.mapDerivedCategoryCompIso F' G).hom ≫
        Functor.whiskerRight (Functor.exactDerivedMap α) G.mapDerivedCategory := by
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro P
  apply (cancel_mono (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P))).1
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors, exactMap_fac]
  rw [← G.mapDerivedCategory.map_comp_assoc, exactMap_fac, Functor.map_comp, Category.assoc]
  erw [G.mapDerivedCategoryFactors.hom.naturality]
  erw [reassoc_of% (Functor.mapDerivedCategoryCompIso_hom_app_factors F' G P)]
  congr 2

end ExactNaturality

private theorem triangle_fac
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (H : D ⥤ E) (F' : C ⥤ E)
    [F.Additive] [H.Additive] [F'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (α : F' ⟶ F ⋙ H) (P : CochainComplex C ℤ) :
    ((Functor.exactDerivedMap α).app (DerivedCategory.Q.obj P) ≫
        (Functor.mapDerivedCategoryCompIso F H).hom.app (DerivedCategory.Q.obj P)) ≫
      H.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
    F'.mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map (Functor.mapHomologicalComplexCompNatTrans F H F' α P) := by
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors, exactMap_fac]
  congr 2
  ext n
  simp only [Functor.mapHomologicalComplexCompNatTrans_f,
    NatTrans.mapHomologicalComplex_app_f]

private theorem triangle_unique_h
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (H : D ⥤ E) (F' : C ⥤ E)
    [F.Additive] [H.Additive] [F'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (α : F' ⟶ F ⋙ H)
    (d : F'.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (hd : ∀ K : HomotopyCategory C (.up ℤ),
      d.app (DerivedCategory.Qh.obj K) ≫
        H.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        H.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
      F'.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory α (.up ℤ)).app K)) :
    d = Functor.exactDerivedMap α ≫ (Functor.mapDerivedCategoryCompIso F H).hom := by
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono (H.mapDerivedCategory.map
    (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      H.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K))).1
  simp only [NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factorsh]
  erw [exactMap_fac_h]
  exact hd K

section

attribute [local irreducible] supportCoefficientOpenMate supportCoefficientMate
  Functor.exactDerivedMap

private theorem openMate_eq (A : Type (u + 1)) [CommRing A]
    {T S B D : Scheme.{u}} (h : S ⟶ T) [IsOpenImmersion h]
    (b : B ⟶ T) (d : D ⟶ S) [IsClosedImmersion b] [IsClosedImmersion d]
    (hd : d.openComplement = h ⁻¹ᵁ b.openComplement) :
    supportCoefficientOpenMate A h b d hd =
      Functor.exactDerivedMap
        (supportCoefficientMate (supportedCoefficientAdjunction A b)
          (supportedCoefficientAdjunction A d) (upperStar (ModuleCat.{u + 1} A) h)
          (supportTransport A h b d hd)) ≫
        (Functor.mapDerivedCategoryCompIso (supportedCoefficients A b)
          (upperStar (ModuleCat.{u + 1} A) h)).hom := by
  exact triangle_unique_h (supportedCoefficients A b)
    (upperStar (ModuleCat.{u + 1} A) h) (supportedCoefficients A d)
    (supportCoefficientMate (supportedCoefficientAdjunction A b)
      (supportedCoefficientAdjunction A d) (upperStar (ModuleCat.{u + 1} A) h)
      (supportTransport A h b d hd))
    (supportCoefficientOpenMate A h b d hd)
    (supportedCoefficientDerivedOpenMate_fac A h b d hd)

end

set_option backward.isDefEq.respectTransparency true in
private theorem triangle_whisker
    {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
    [Abelian C] [Abelian D] [Abelian E] [Abelian E']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory E']
    (F : C ⥤ D) (P : D ⥤ E) (Q : D ⥤ E') (H : E ⥤ E')
    [F.Additive] [P.Additive] [Q.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : Q ≅ P ⋙ H) (M : DerivedCategory C) :
    (Functor.mapDerivedCategoryCompIso F Q).hom.app M ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app (F.mapDerivedCategory.obj M) ≫
      (Functor.mapDerivedCategoryCompIso P H).hom.app (F.mapDerivedCategory.obj M) ≫
      H.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso F P).inv.app M) =
    (Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft F e)).hom.app M ≫
      (Functor.mapDerivedCategoryCompIso (F ⋙ P) H).hom.app M := by
  have hw := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F e) M
  have hc := congr_app (Functor.mapDerivedCategoryCompIso_assoc F P H) M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hw hc
  rw [← Category.assoc, ← hw]
  simp only [Category.assoc]
  rw [reassoc_of% hc]
  rw [← H.mapDerivedCategory.map_comp, Iso.hom_inv_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency true in
private theorem triangle_whiskerRight
    {C D E E' : Type*} [Category C] [Category D] [Category E] [Category E']
    [Abelian C] [Abelian D] [Abelian E] [Abelian E']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory E']
    (F : C ⥤ D) (J : D ⥤ E) (F' : C ⥤ E) (Q : E ⥤ E')
    [F.Additive] [J.Additive] [F'.Additive] [Q.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (β : F' ⟶ F ⋙ J) (M : DerivedCategory C) :
    (Functor.mapDerivedCategoryCompIso F' Q).hom.app M ≫
      Q.mapDerivedCategory.map ((Functor.exactDerivedMap β).app M ≫
        (Functor.mapDerivedCategoryCompIso F J).hom.app M) ≫
      (Functor.mapDerivedCategoryCompIso J Q).inv.app (F.mapDerivedCategory.obj M) =
    (Functor.exactDerivedMap (Functor.whiskerRight β Q)).app M ≫
      (Functor.mapDerivedCategoryCompIso F (J ⋙ Q)).hom.app M := by
  have hw := congr_app (exactMap_whiskerRight Q β) M
  have hc := congr_app (Functor.mapDerivedCategoryCompIso_assoc F J Q) M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hw hc
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, ← hw]
  simp only [Category.assoc]
  rw [← reassoc_of% hc]
  simp only [Iso.hom_inv_id_app, Category.comp_id]

private theorem triangle_square
    {C D E T T' : Type*} [Category C] [Category D] [Category E] [Category T] [Category T']
    [Abelian C] [Abelian D] [Abelian E] [Abelian T] [Abelian T']
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [HasDerivedCategory T] [HasDerivedCategory T']
    (F : C ⥤ D) (J : D ⥤ E) (F' : C ⥤ E) (P : D ⥤ T)
    (Q : E ⥤ T') (H : T ⥤ T')
    [F.Additive] [J.Additive] [F'.Additive] [P.Additive] [Q.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (β : F' ⟶ F ⋙ J) (e : J ⋙ Q ≅ P ⋙ H) (M : DerivedCategory C) :
    (Functor.mapDerivedCategoryCompIso F' Q).hom.app M ≫
      Q.mapDerivedCategory.map ((Functor.exactDerivedMap β).app M ≫
        (Functor.mapDerivedCategoryCompIso F J).hom.app M) ≫
      (Functor.mapDerivedCategoryCompIso J Q).inv.app (F.mapDerivedCategory.obj M) ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app (F.mapDerivedCategory.obj M) ≫
      (Functor.mapDerivedCategoryCompIso P H).hom.app (F.mapDerivedCategory.obj M) ≫
      H.mapDerivedCategory.map ((Functor.mapDerivedCategoryCompIso F P).inv.app M) =
    (Functor.exactDerivedMap (Functor.whiskerRight β Q ≫
      Functor.whiskerLeft F e.hom)).app M ≫
      (Functor.mapDerivedCategoryCompIso (F ⋙ P) H).hom.app M := by
  rw [exactMap_comp]
  change _ = ((Functor.exactDerivedMap (Functor.whiskerRight β Q)).app M ≫
    (Functor.exactDerivedMap (Functor.isoWhiskerLeft F e).hom).app M) ≫ _
  rw [exactMap_iso]
  simp only [Category.assoc]
  rw [reassoc_of% (triangle_whiskerRight F J F' Q β M)]
  rw [triangle_whisker]

private theorem firstMap_eq (A : Type (u + 1)) [CommRing A]
    {S X Y B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X)
    [IsClosedImmersion b] (V : Y.Opens) (M : DerivedCategory (ModuleCat.{u + 1} A)) :
    supportSecondOpenFirstCoefficientMap A f g b V M =
      (Functor.exactDerivedMap
        (supportSecondOrdinaryOpenFirstCoefficientNatTrans A f g b V)).app M ≫
        (Functor.mapDerivedCategoryCompIso (supportedFirstCoefficients A f g b)
          (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V))).hom.app M := by
  dsimp only [supportSecondOpenFirstCoefficientMap, supportFirstCoefficientProjectionIso,
    supportPullbackProjectionIso, leftDerivedUpperStarComp,
    leftDerivedUpperStarIsoMapDerivedCategory, Iso.app,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  simp only [map_natIso_inv_hom_assoc]
  have he : supportSecondOrdinaryOpenFirstCoefficientNatTrans A f g b V =
      (Functor.isoWhiskerLeft (supportedCoefficients A b)
        (upperStarComp (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
          (pullback.fst f g) (pullback.fst f (V.ι ≫ g))
          (supportedSecondOpenMap_fst f g V).symm)).hom := by
    ext K
    simp only [supportSecondOrdinaryOpenFirstCoefficientNatTrans,
      NatTrans.comp_app, Functor.associator_inv_app, Category.comp_id]
    rfl
  rw [he, exactMap_iso]
  exact triangle_whisker _ _ _ _ _ M

private theorem mapSquare_hom
    (E : Type v₁) [Category.{u + 1} E] [Abelian E]
    [IsGrothendieckAbelian.{u + 1} E] [HasSmallSiteSheafify E]
    {T X Y Z : Scheme.{u}} (h : Z ⟶ T) (p : T ⟶ X) (q : Z ⟶ Y) (a : Y ⟶ X)
    (hp : h ≫ p = q ≫ a) (K : DerivedCategory (Sheaf X.smallEtaleTopology E)) :
    (Functor.mapDerivedCategoryNatIso (squareUpperStarIso E (CommSq.mk hp))).hom.app K =
      (Functor.mapDerivedCategoryNatIso (upperStarComp E q a (h ≫ p) hp)).inv.app K ≫
        (Functor.mapDerivedCategoryNatIso (upperStarComp E h p)).hom.app K := by
  unfold squareUpperStarIso
  rw [Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    NatTrans.comp_app]

private theorem secondMap_eq (A : Type (u + 1)) [CommRing A]
    {S X Y D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y)
    [IsClosedImmersion d] (V : Y.Opens) (M : DerivedCategory (ModuleCat.{u + 1} A)) :
    supportSecondOpenCoefficientMap A f g d V M =
      (Functor.exactDerivedMap
        (supportSecondOrdinaryOpenCoefficientNatTrans A f g d V)).app M ≫
        (Functor.mapDerivedCategoryCompIso (supportedSecondCoefficients A f g d)
          (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V))).hom.app M := by
  dsimp only [supportSecondOpenCoefficientMap, supportSecondCoefficientProjectionIso,
    supportPullbackSquareIso, leftDerivedUpperStarComp,
    leftDerivedUpperStarIsoMapDerivedCategory, Iso.app,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.mapIso_inv]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [← (upperStar (ModuleCat.{u + 1} A)
    (pullback.snd f (V.ι ≫ g))).leftDerivedFunctorIsoMapDerivedCategory.inv.naturality_assoc]
  erw [← (upperStar (ModuleCat.{u + 1} A)
    (pullback.snd f (V.ι ≫ g))).leftDerivedFunctorIsoMapDerivedCategory.inv.naturality_assoc]
  simp only [Iso.inv_hom_id_app_assoc, map_natIso_inv_hom_assoc]
  let F := supportedCoefficients A d
  let J := upperStar (ModuleCat.{u + 1} A) V.ι
  let F' := supportedCoefficients A (supportOnOpen d V)
  let P := upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)
  let Q := upperStar (ModuleCat.{u + 1} A) (pullback.snd f (V.ι ≫ g))
  let H := upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
  let β := supportCoefficientMate (supportedCoefficientAdjunction A d)
    (supportedCoefficientAdjunction A (supportOnOpen d V)) J
    (supportTransport A V.ι d (supportOnOpen d V) (supportOnOpen_complement d V))
  let e := squareUpperStarIso (ModuleCat.{u + 1} A)
    (CommSq.mk (supportedSecondOpenMap_snd f g V))
  have he : supportSecondOrdinaryOpenCoefficientNatTrans A f g d V =
      Functor.whiskerRight β Q ≫ Functor.whiskerLeft F e.hom := by
    ext K
    simp only [supportSecondOrdinaryOpenCoefficientNatTrans, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id]
    rfl
  rw [← reassoc_of% (mapSquare_hom (ModuleCat.{u + 1} A)
    (supportedSecondOpenMap f g V) (pullback.snd f g)
    (pullback.snd f (V.ι ≫ g)) V.ι (supportedSecondOpenMap_snd f g V)
    (F.mapDerivedCategory.obj M))]
  rw [openMate_eq A V.ι d (supportOnOpen d V) (supportOnOpen_complement d V)]
  rw [he]
  have hz := triangle_square F J F' P Q H β e M
  exact hz


private noncomputable def transportBifunctorIso
    {C D : Type*} [Category C] [Category D] (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    {L H : C ⥤ D} (τ : L ≅ H)
    (δ : (Functor.postcompose₂.obj L).obj T ≅
      (((Functor.whiskeringLeft₂ _).obj L).obj L).obj T') :
    (Functor.postcompose₂.obj H).obj T ≅
      (((Functor.whiskeringLeft₂ _).obj H).obj H).obj T' :=
  (Functor.postcompose₂.mapIso τ.symm).app T ≪≫ δ ≪≫
    (((Functor.whiskeringLeft₂ _).mapIso τ).app L).app T' ≪≫
    (((Functor.whiskeringLeft₂ _).obj H).mapIso τ).app T'

private theorem transportBifunctorIso_app
    {C D : Type*} [Category C] [Category D] (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    {L H : C ⥤ D} (τ : L ≅ H)
    (δ : (Functor.postcompose₂.obj L).obj T ≅
      (((Functor.whiskeringLeft₂ _).obj L).obj L).obj T') (X Y : C) :
    ((transportBifunctorIso T T' τ δ).hom.app X).app Y =
      τ.inv.app ((T.obj X).obj Y) ≫ (δ.hom.app X).app Y ≫
      (T'.map (τ.hom.app X)).app (L.obj Y) ≫ (T'.obj (H.obj X)).map (τ.hom.app Y) := by
  rfl

private theorem transportTensor_fac
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']
    (R : C ⥤ C') (S : D ⥤ D') [R.LaxMonoidal] [S.LaxMonoidal]
    (H : C ⥤ D) [H.OplaxMonoidal] {L J : C' ⥤ D'} (τ : L ≅ J)
    (δ : (Functor.postcompose₂.obj L).obj (curriedTensor C') ≅
      (((Functor.whiskeringLeft₂ _).obj L).obj L).obj (curriedTensor D'))
    (e : R ⋙ J ≅ H ⋙ S) (c : ∀ P, L.obj (R.obj P) ⟶ S.obj (H.obj P))
    (hc : ∀ P, τ.hom.app (R.obj P) ≫ e.hom.app P = c P)
    (hδ : ∀ P Q, (δ.hom.app (R.obj P)).app (R.obj Q) ≫ (c P ⊗ₘ c Q) ≫
        Functor.LaxMonoidal.μ S (H.obj P) (H.obj Q) =
      L.map (Functor.LaxMonoidal.μ R P Q) ≫ c (P ⊗ Q) ≫
        S.map (Functor.OplaxMonoidal.δ H P Q)) (P Q : C) :
    ((transportBifunctorIso (curriedTensor C') (curriedTensor D') τ δ).hom.app
        (R.obj P)).app (R.obj Q) ≫ (e.hom.app P ⊗ₘ e.hom.app Q) ≫
        Functor.LaxMonoidal.μ S (H.obj P) (H.obj Q) =
      J.map (Functor.LaxMonoidal.μ R P Q) ≫ e.hom.app (P ⊗ Q) ≫
        S.map (Functor.OplaxMonoidal.δ H P Q) := by
  rw [transportBifunctorIso_app]
  change (τ.inv.app (R.obj P ⊗ R.obj Q) ≫ (δ.hom.app (R.obj P)).app (R.obj Q) ≫
      (τ.hom.app (R.obj P) ▷ L.obj (R.obj Q)) ≫
      (J.obj (R.obj P) ◁ τ.hom.app (R.obj Q))) ≫ _ = _
  rw [← MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, hc, hc, hδ, ← hc]
  erw [← τ.inv.naturality_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

section TensorPullback


variable (E : Type v₁) [Category.{u + 1} E] [Abelian E]
  [IsGrothendieckAbelian.{u + 1} E] [MonoidalCategory E] [MonoidalPreadditive E]
  [SymmetricCategory E] [MonoidalClosed E] [Abelian.HasFunctorialFlatResolution E]
  [UpperStarPreservesFlat E]

omit [UpperStarPreservesFlat E] in
private theorem derivedTensorMap_eq (X : Scheme.{u})
    {M M' N N' : DerivedCategory (Sheaf X.smallEtaleTopology E)}
    (a : M ⟶ M') (b : N ⟶ N') :
    ((derivedTensor E X).map a).app N ≫ ((derivedTensor E X).obj M').map b = a ⊗ₘ b := by
  exact (MonoidalCategory.tensorHom_def a b).symm

private noncomputable def exactTensorNatIso
    {P Q : Scheme.{u}} (h : Q ⟶ P) :
    (Functor.postcompose₂.obj (upperStar E h).mapDerivedCategory).obj
        (curriedTensor (DerivedCategory (Sheaf P.smallEtaleTopology E))) ≅
      (((Functor.whiskeringLeft₂ _).obj
        (upperStar E h).mapDerivedCategory).obj
        (upperStar E h).mapDerivedCategory).obj (curriedTensor _) :=
  transportBifunctorIso (derivedTensor E P)
    (derivedTensor E Q)
    (leftDerivedUpperStarIsoMapDerivedCategory E h)
    (leftDerivedUpperStarTensorNatIso E h)

private theorem exactTensorNatIso_app
    {P Q : Scheme.{u}} (h : Q ⟶ P)
    (K L : DerivedCategory (Sheaf P.smallEtaleTopology E)) :
    ((exactTensorNatIso E h).hom.app K).app L =
      (supportExactPullbackTensorIso E h K L).hom := by
  exact transportBifunctorIso_app (derivedTensor E P)
    (derivedTensor E Q)
    (leftDerivedUpperStarIsoMapDerivedCategory E h)
    (leftDerivedUpperStarTensorNatIso E h) K L

private theorem exactTensor_fac_h
    {P Q : Scheme.{u}} (h : Q ⟶ P)
    (K L : HomotopyCategory (Sheaf P.smallEtaleTopology E) (.up ℤ)) :
    ((exactTensorNatIso E h).hom.app (DerivedCategory.Qh.obj K)).app
        (DerivedCategory.Qh.obj L) ≫
      ((upperStar E h).mapDerivedCategoryFactorsh.hom.app K ⊗ₘ
        (upperStar E h).mapDerivedCategoryFactorsh.hom.app L) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh
        (((upperStar E h).mapHomotopyCategory (.up ℤ)).obj K)
        (((upperStar E h).mapHomotopyCategory (.up ℤ)).obj L) =
    (upperStar E h).mapDerivedCategory.map
        (Functor.LaxMonoidal.μ DerivedCategory.Qh K L) ≫
      (upperStar E h).mapDerivedCategoryFactorsh.hom.app (K ⊗ L) ≫
      DerivedCategory.Qh.map (Functor.OplaxMonoidal.δ
        ((upperStar E h).mapHomotopyCategory (.up ℤ)) K L) := by
  exact transportTensor_fac
    (DerivedCategory.Qh (C := Sheaf P.smallEtaleTopology E))
    (DerivedCategory.Qh (C := Sheaf Q.smallEtaleTopology E))
    ((upperStar E h).mapHomotopyCategory (.up ℤ))
    (leftDerivedUpperStarIsoMapDerivedCategory E h)
    (leftDerivedUpperStarTensorNatIso E h)
    (upperStar E h).mapDerivedCategoryFactorsh
    (fun K => (upperStar E h).leftDerivedFunctorCounit.app K)
    (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac _)
    (by
      intro K L
      simpa only [leftDerivedUpperStarTensorNatIso_hom] using
        leftDerivedUpperStarTensorComparison_app_app_comp E h K L) K L

private theorem exactTensor_fac
    {X Y : Scheme.{u}} (h : X ⟶ Y)
    (P Q : CochainComplex (Sheaf Y.smallEtaleTopology E) ℤ) :
    tensorFactorCondition (upperStar E h)
      (fun K L => ((exactTensorNatIso E h).hom.app K).app L) P Q := by
  exact tensor_fac_of_homotopy (upperStar E h)
    (fun K L => ((exactTensorNatIso E h).hom.app K).app L)
    (exactTensor_fac_h E h) P Q

/-- Give the canonical tensor comparison directly as the components of a transformation. -/
@[reducible]
private noncomputable def exactTensorHom
    {P Q : Scheme.{u}} (h : Q ⟶ P) :
    (Functor.postcompose₂.obj (upperStar E h).mapDerivedCategory).obj
        (curriedTensor (DerivedCategory (Sheaf P.smallEtaleTopology E))) ⟶
      (((Functor.whiskeringLeft₂ _).obj
        (upperStar E h).mapDerivedCategory).obj
        (upperStar E h).mapDerivedCategory).obj (curriedTensor _) where
  app K :=
    { app L := (supportExactPullbackTensorIso E h K L).hom
      naturality L L' b := by
        have hn := ((exactTensorNatIso E h).hom.app K).naturality b
        simpa only [exactTensorNatIso_app] using hn }
  naturality K K' a := by
    apply NatTrans.ext
    funext L
    have hn := congr_app ((exactTensorNatIso E h).hom.naturality a) L
    simpa only [NatTrans.comp_app, exactTensorNatIso_app] using hn

private theorem exactTensorHom_fac
    {X Y : Scheme.{u}} (h : X ⟶ Y)
    (P Q : CochainComplex (Sheaf Y.smallEtaleTopology E) ℤ) :
    tensorFactorCondition (upperStar E h)
      (fun K L => ((exactTensorHom E h).app K).app L) P Q := by
  exact tensorFactorCondition_congr (upperStar E h)
    (fun K L => ((exactTensorNatIso E h).hom.app K).app L)
    (fun K L => ((exactTensorHom E h).app K).app L)
    (exactTensorNatIso_app E h) P Q (exactTensor_fac E h P Q)

end TensorPullback


section ExactSquare

universe w
variable {C D E : Type*} [Category.{w + 1} C] [Category.{w + 1} D] [Category.{w + 1} E]
  [Abelian C] [Abelian D] [Abelian E]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [IsGrothendieckAbelian.{w + 1} E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [MonoidalPreadditive E]
  [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]
  [BraidedCategory C] [BraidedCategory D] [BraidedCategory E]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [Abelian.HasFunctorialFlatResolution E]
  [HasDerivedCategory.{w + 1} C] [HasDerivedCategory.{w + 1} D] [HasDerivedCategory.{w + 1} E]
  (G F₁ F₂ : C ⥤ D) (G' F₁' F₂' : C ⥤ E) (H : D ⥤ E)
  [G.Additive] [F₁.Additive] [F₂.Additive]
  [G'.Additive] [F₁'.Additive] [F₂'.Additive] [H.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits F₁'] [PreservesFiniteColimits F₁']
  [PreservesFiniteLimits F₂'] [PreservesFiniteColimits F₂']
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [H.Monoidal] [H.IsLeftAdjoint]
  [(F₂ ⋙ H).PreservesFlat] [(F₂ ⋙ H).IsLeftAdjoint]
  (a₀ : G' ⟶ G ⋙ H) (a₁ : F₁' ⟶ F₁ ⋙ H) (a₂ : F₂' ⟶ F₂ ⋙ H)
  (κ : (Functor.postcompose₂.obj H.mapDerivedCategory).obj
      (curriedTensor (DerivedCategory D)) ⟶
    (((Functor.whiskeringLeft₂ _).obj H.mapDerivedCategory).obj
      H.mapDerivedCategory).obj (curriedTensor (DerivedCategory E)))
  (τ : (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
      (curriedTensor (CochainComplex C ℤ)) ⟶
    (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
      (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor (CochainComplex D ℤ)))
  (τ' : (Functor.postcompose₂.obj (G'.mapHomologicalComplex (.up ℤ))).obj
      (curriedTensor (CochainComplex C ℤ)) ⟶
    (((Functor.whiskeringLeft₂ _).obj (F₁'.mapHomologicalComplex (.up ℤ))).obj
      (F₂'.mapHomologicalComplex (.up ℤ))).obj (curriedTensor (CochainComplex E ℤ)))
  (t : supportedDerivedComparisonHom G F₁ F₂)
  (t' : supportedDerivedComparisonHom G' F₁' F₂')

-- Keep the total-complex square folded when its coefficient categories are specialized.
omit [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [Abelian.HasFunctorialFlatResolution E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits F₁'] [PreservesFiniteColimits F₁']
  [PreservesFiniteLimits F₂'] [PreservesFiniteColimits F₂']
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [(F₂ ⋙ H).PreservesFlat] [(F₂ ⋙ H).IsLeftAdjoint] in
@[irreducible]
private noncomputable def exactComplexSquareCondition (P Q : CochainComplex C ℤ) : Prop :=
  Functor.mapHomologicalComplexCompNatTrans G H G' a₀ (P ⊗ Q) ≫
    (H.mapHomologicalComplex (.up ℤ)).map ((τ.app P).app Q) ≫
    Functor.OplaxMonoidal.δ (H.mapHomologicalComplex (.up ℤ))
      ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
      ((F₂.mapHomologicalComplex (.up ℤ)).obj Q) =
  (τ'.app P).app Q ≫
    (Functor.mapHomologicalComplexCompNatTrans F₁ H F₁' a₁ P ⊗ₘ
      Functor.mapHomologicalComplexCompNatTrans F₂ H F₂' a₂ Q)

omit [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [Abelian.HasFunctorialFlatResolution E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits F₁'] [PreservesFiniteColimits F₁']
  [PreservesFiniteLimits F₂'] [PreservesFiniteColimits F₂']
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [(F₂ ⋙ H).PreservesFlat] [(F₂ ⋙ H).IsLeftAdjoint] in
private theorem complexSquare
    [PreservesColimitsOfSize.{0, 0} G] [PreservesColimitsOfSize.{0, 0} G']
    (σ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj F₁).obj F₂).obj (curriedTensor D))
    (σ' : (Functor.postcompose₂.obj G').obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ E).obj F₁').obj F₂').obj (curriedTensor E))
    (ha : ∀ M N, a₀.app (M ⊗ N) ≫ H.map ((σ.app M).app N) ≫
      Functor.OplaxMonoidal.δ H (F₁.obj M) (F₂.obj N) =
      (σ'.app M).app N ≫ (a₁.app M ⊗ₘ a₂.app N))
    (P Q : CochainComplex C ℤ) :
    exactComplexSquareCondition G F₁ F₂ G' F₁' F₂' H a₀ a₁ a₂
      (supportedComplexComparisonNatTrans G F₁ F₂ σ)
      (supportedComplexComparisonNatTrans G' F₁' F₂' σ') P Q := by
  unfold exactComplexSquareCondition
  have e := supportedTensorComplex_square G F₁ F₂ G' F₁' F₂' H σ σ' a₀ a₁ a₂ ha P Q
  unfold supportedTensorComplexSquareCondition at e
  exact e

private theorem exactSquare
    (ht : supportedDerivedComparisonCondition G F₁ F₂ τ t)
    (ht' : supportedDerivedComparisonCondition G' F₁' F₂' τ' t')
    (hκ : ∀ P Q : CochainComplex D ℤ,
      tensorFactorCondition H (fun K L => (κ.app K).app L) P Q)
    (ha : ∀ P Q : CochainComplex C ℤ,
      exactComplexSquareCondition G F₁ F₂ G' F₁' F₂' H a₀ a₁ a₂ τ τ' P Q)
    (M N : DerivedCategory C) :
    ((Functor.exactDerivedMap a₀).app (M ⊗ N) ≫
        (Functor.mapDerivedCategoryCompIso G H).hom.app (M ⊗ N)) ≫
      H.mapDerivedCategory.map (t M N) ≫
      (κ.app (F₁.mapDerivedCategory.obj M)).app (F₂.mapDerivedCategory.obj N) =
    t' M N ≫
      (((Functor.exactDerivedMap a₁).app M ≫
        (Functor.mapDerivedCategoryCompIso F₁ H).hom.app M) ⊗ₘ
      ((Functor.exactDerivedMap a₂).app N ≫
        (Functor.mapDerivedCategoryCompIso F₂ H).hom.app N)) := by
  unfold tensorFactorCondition at hκ
  unfold exactComplexSquareCondition at ha
  let d₀ := Functor.exactDerivedMap a₀ ≫ (Functor.mapDerivedCategoryCompIso G H).hom
  let d₁ := Functor.exactDerivedMap a₁ ≫ (Functor.mapDerivedCategoryCompIso F₁ H).hom
  let d₂ := Functor.exactDerivedMap a₂ ≫ (Functor.mapDerivedCategoryCompIso F₂ H).hom
  refine family_eq_of_models G'.mapDerivedCategory
    (F₁.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (F₂.mapDerivedCategory ⋙ H.mapDerivedCategory) (𝟭 _)
    (fun M N => d₀.app (M ⊗ N) ≫ H.mapDerivedCategory.map (t M N) ≫
      (κ.app (F₁.mapDerivedCategory.obj M)).app (F₂.mapDerivedCategory.obj N))
    (fun M N => t' M N ≫ (d₁.app M ⊗ₘ d₂.app N)) ?_ ?_ ?_ M N
  · exact fun _ _ _ _ a b => tensorSquare_left_natural
      (DG := G.mapDerivedCategory) (DF₁ := F₁.mapDerivedCategory)
      (DF₂ := F₂.mapDerivedCategory) (DG' := G'.mapDerivedCategory)
      (DH := H.mapDerivedCategory) d₀ κ t ht.1 a b
  · exact fun _ _ _ _ a b => tensorSquare_right_natural
      (DF₁ := F₁.mapDerivedCategory) (DF₂ := F₂.mapDerivedCategory)
      (DG' := G'.mapDerivedCategory) (DF₁' := F₁'.mapDerivedCategory)
      (DF₂' := F₂'.mapDerivedCategory) (DH := H.mapDerivedCategory) d₁ d₂ t' ht'.1 a b
  · intro M N
    let := Localization.essSurj DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    let P := DerivedCategory.Q.objPreimage M
    let Q := DerivedCategory.Q.objPreimage N
    let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution C).some
    let R := Λ.reduced.resolutionFunctor.obj Q
    have hR : (HomologicalComplex.quasiIso E (.up ℤ)).kFlat
        ((H.mapHomologicalComplex (.up ℤ)).obj ((F₂.mapHomologicalComplex (.up ℤ)).obj R)) :=
      (F₂ ⋙ H).kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj Λ.reduced
        ObjectProperty.flat.essImage_ι_le Q
    have : IsIso (DerivedCategory.Q.map (Λ.reduced.resolutionNatTrans.app Q)) := by
      have := Λ.reduced.quasiIso_resolutionNatTrans_app Q
      infer_instance
    refine ⟨DerivedCategory.Q.obj P, DerivedCategory.Q.obj R, ?_,
      ⟨DerivedCategory.Q.objObjPreimageIso M⟩,
      ⟨asIso (DerivedCategory.Q.map (Λ.reduced.resolutionNatTrans.app Q)) ≪≫
        DerivedCategory.Q.objObjPreimageIso N⟩⟩
    have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
        ((H.mapHomologicalComplex (.up ℤ)).obj ((F₁.mapHomologicalComplex (.up ℤ)).obj P))
        ((H.mapHomologicalComplex (.up ℤ)).obj ((F₂.mapHomologicalComplex (.up ℤ)).obj R))) := by
      rw [μQ_eq]
      exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
        (HomotopyCategory.quasiIso E (.up ℤ)) _ _
        ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hR)
    apply tensorSquare_model DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
      (G.mapHomologicalComplex (.up ℤ)) (F₁.mapHomologicalComplex (.up ℤ))
      (F₂.mapHomologicalComplex (.up ℤ)) (G'.mapHomologicalComplex (.up ℤ))
      (F₁'.mapHomologicalComplex (.up ℤ)) (F₂'.mapHomologicalComplex (.up ℤ))
      (H.mapHomologicalComplex (.up ℤ)) G.mapDerivedCategory F₁.mapDerivedCategory
      F₂.mapDerivedCategory G'.mapDerivedCategory F₁'.mapDerivedCategory
      F₂'.mapDerivedCategory H.mapDerivedCategory
      G.mapDerivedCategoryFactors F₁.mapDerivedCategoryFactors F₂.mapDerivedCategoryFactors
      G'.mapDerivedCategoryFactors F₁'.mapDerivedCategoryFactors F₂'.mapDerivedCategoryFactors
      H.mapDerivedCategoryFactors
      (NatTrans.mapHomologicalComplex a₀ (.up ℤ) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (G ⋙ H)) (.up ℤ)).inv)
      (NatTrans.mapHomologicalComplex a₁ (.up ℤ) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F₁ ⋙ H)) (.up ℤ)).inv)
      (NatTrans.mapHomologicalComplex a₂ (.up ℤ) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F₂ ⋙ H)) (.up ℤ)).inv)
      d₀ d₁ d₂ κ (fun P Q => (τ.app P).app Q)
      (fun P Q => (τ'.app P).app Q) t t'
      (triangle_fac G H G' a₀) (triangle_fac F₁ H F₁' a₁)
      (triangle_fac F₂ H F₂' a₂) hκ ?_ ?_ ha P R
    · intro P Q
      have h := ht.2 P Q
      have he : eqToHom (supportedComplexTensor_eq
          ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
          ((F₂.mapHomologicalComplex (.up ℤ)).obj Q)) = 𝟙 _ := rfl
      rw [he, CategoryTheory.Functor.map_id, Category.comp_id] at h
      exact h
    · intro P Q
      have h := ht'.2 P Q
      have he : eqToHom (supportedComplexTensor_eq
          ((F₁'.mapHomologicalComplex (.up ℤ)).obj P)
          ((F₂'.mapHomologicalComplex (.up ℤ)).obj Q)) = 𝟙 _ := rfl
      rw [he, CategoryTheory.Functor.map_id, Category.comp_id] at h
      exact h

end ExactSquare

private theorem secondTensor_closedPushforward_flat
    (A : Type (u + 1)) [CommRing A] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hM : ObjectProperty.flat M) :
    ObjectProperty.flat ((lowerStar (ModuleCat.{u + 1} A) i).obj M) := by
  let C := ModuleCat.{u + 1} A
  let j := i.openComplement.ι
  let F := (lowerStar C i).obj M
  have hij : Set.range i.base = (Set.range j.base)ᶜ := by
    simp [j, Scheme.Hom.coe_openComplement, Scheme.Opens.range_ι]
  have hj : ObjectProperty.flat ((upperStar C j).obj F) :=
    ObjectProperty.flat_of_isZero
      (isZero_upperStar_lowerStar_of_disjoint_range C j i
        (disjoint_range_of_range_eq_compl j i hij) M)
  have hi : ObjectProperty.flat ((upperStar C i).obj F) :=
    ObjectProperty.prop_of_iso ObjectProperty.flat
      (asIso ((upperStarLowerStarAdjunction C i).counit.app M)).symm hM
  apply (flat_iff_forall_flat_sheafFiber_obj F).2
  intro Ω _ _ s
  obtain ⟨t, ht, -⟩ | ⟨t, ht, -⟩ :=
    existsUnique_fac_or_fac_of_range_eq_compl j i hij s
  · subst ht
    exact ObjectProperty.prop_of_iso ObjectProperty.flat
      ((upperStarCompUliftSheafFiberIso C j t).app F)
        ((flat_iff_forall_flat_sheafFiber_obj _).1 hj t)
  · subst ht
    exact ObjectProperty.prop_of_iso ObjectProperty.flat
      ((upperStarCompUliftSheafFiberIso C i t).app F)
        ((flat_iff_forall_flat_sheafFiber_obj _).1 hi t)

private theorem secondTensor_coefficients_preserveFlat
    (A : Type (u + 1)) [CommRing A] {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] : (supportedCoefficients A i).PreservesFlat := by
  constructor
  intro M hM
  exact secondTensor_closedPushforward_flat A i _
    (GrothendieckTopology.flat_presheafToSheaf_obj
      (ModuleCat.{u + 1} A) Z.smallEtaleTopology _ (fun _ ↦ hM))

private theorem tensorMap_eq (A : Type (u + 1)) [CommRing A] (X : Scheme.{u})
    {M M' N N' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (a : M ⟶ M') (b : N ⟶ N') :
    supportedDerivedTensorMap A X a b = a ⊗ₘ b := by
  exact derivedTensorMap_eq (ModuleCat.{u + 1} A) X a b

-- The comparison APIs below supply all required equalities; keep their data folded.
attribute [local irreducible] supportSecondOpenFirstCoefficientMap
  supportSecondOpenCoefficientMap supportCoefficientOpenMate supportExactPullbackTensorIso
  exactTensorNatIso supportedDerivedComparisonCondition supportedComplexComparisonNatTrans

/-- The coefficient tensor comparison commutes with open pullback in the second variable.
It is independent of supported-section inputs and evaluation maps.

Source: Stacks Tags 09XP and 0F1E, coefficient calculation in steps 5 and 11 of
lem-pur-supported-product-localization.
(blueprint: lem-pur-supported-coefficient-second-open-tensor).
Proof: normalize each ordinary coefficient comparison by its epic quotient from the
constant sheaf. The mates of support restriction carry this quotient to its pullback.
After precomposition with the constant quotient, both sides of the coefficient square
pull back and tensor the same local constants. Cancel the quotient. Apply this equality
in every bidegree of the signed total complex. The canonical tensor pullback comparison
has exactly this bidegree normalization. Descend along K-flat coefficient models using
the normalization of supportedCoefficientTensorDerived and derived-adjunction units.
Every derived coefficient object admits such a model, and naturality transports the
result along the model isomorphisms. Empty opens and supports give zero coefficient
sheaves, so the same calculation applies in those cases. -/
theorem supportedCoefficientTensor_openSecond (A : Type (u + 1)) [CommRing A]
    {S X Y B D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (V : Y.Opens)
    (M N : DerivedCategory (ModuleCat.{u + 1} A)) :
    (supportCoefficientOpenMate A (supportedSecondOpenMap f g V)
      (supportedProductImmersion f g b d)
      (supportedProductImmersion f (V.ι ≫ g) b (supportOnOpen d V))
      (supportedSecondOpenSupport_complement f g b d V)).app (M ⊗ N) ≫
      (upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)).mapDerivedCategory.map
        (supportedCoefficientTensorDerived A f g b d M N) ≫
      (supportExactPullbackTensorIso (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
        ((supportedFirstCoefficients A f g b).mapDerivedCategory.obj M)
        ((supportedSecondCoefficients A f g d).mapDerivedCategory.obj N)).hom =
    supportedCoefficientTensorDerived A f (V.ι ≫ g) b (supportOnOpen d V) M N ≫
      supportedDerivedTensorMap A (pullback f (V.ι ≫ g))
        (supportSecondOpenFirstCoefficientMap A f g b V M)
        (supportSecondOpenCoefficientMap A f g d V N) := by
  let H := upperStar (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)
  let G := supportedCoefficients A (supportedProductImmersion f g b d)
  let G' := supportedCoefficients A
    (supportedProductImmersion f (V.ι ≫ g) b (supportOnOpen d V))
  let F₁ := supportedFirstCoefficients A f g b
  let F₂ := supportedSecondCoefficients A f g d
  let F₁' := supportedFirstCoefficients A f (V.ι ≫ g) b
  let F₂' := supportedSecondCoefficients A f (V.ι ≫ g) (supportOnOpen d V)
  let a₀ := supportCoefficientMate
    (supportedCoefficientAdjunction A (supportedProductImmersion f g b d))
    (supportedCoefficientAdjunction A
      (supportedProductImmersion f (V.ι ≫ g) b (supportOnOpen d V))) H
    (supportTransport A (supportedSecondOpenMap f g V)
      (supportedProductImmersion f g b d)
      (supportedProductImmersion f (V.ι ≫ g) b (supportOnOpen d V))
      (supportedSecondOpenSupport_complement f g b d V))
  let a₁ := supportSecondOrdinaryOpenFirstCoefficientNatTrans A f g b V
  let a₂ := supportSecondOrdinaryOpenCoefficientNatTrans A f g d V
  let τ := supportedCoefficientTensorNatTrans A f g b d
  let τ' := supportedCoefficientTensorNatTrans A f (V.ι ≫ g) b (supportOnOpen d V)
  let t := (exists_unique_supportedCoefficientTensorDerived A f g b d).choose
  let t' := (exists_unique_supportedCoefficientTensorDerived A f (V.ι ≫ g) b
    (supportOnOpen d V)).choose
  have ht := (exists_unique_supportedCoefficientTensorDerived A f g b d).choose_spec.1
  have ht' := (exists_unique_supportedCoefficientTensorDerived A f (V.ι ≫ g) b
    (supportOnOpen d V)).choose_spec.1
  have : (supportedCoefficients A d).PreservesFlat :=
    secondTensor_coefficients_preserveFlat A d
  have : F₂.PreservesFlat := Functor.preservesFlat_comp
    (supportedCoefficients A d) (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g))
  have : F₂.IsLeftAdjoint := inferInstanceAs
    ((supportedCoefficients A d) ⋙
      upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).IsLeftAdjoint
  dsimp only [supportedCoefficientTensorDerived, supportedSchemeDerivedApply,
    supportedDerivedComparisonApply]
  rewrite [tensorMap_eq]
  rewrite [openMate_eq, NatTrans.comp_app]
  simp only [firstMap_eq A f g b V M, secondMap_eq A f g d V N]
  dsimp only [supportedCoefficientTensorDerivedCondition,
    supportedSchemeDerivedCondition] at ht ht'
  have ht₀ : supportedDerivedComparisonCondition G F₁ F₂
      (supportedComplexComparisonNatTrans G F₁ F₂ τ) t := ht
  have ht₁ : supportedDerivedComparisonCondition G' F₁' F₂'
      (supportedComplexComparisonNatTrans G' F₁' F₂' τ') t' := ht'
  have hs := complexSquare G F₁ F₂ G' F₁' F₂' H a₀ a₁ a₂ τ τ'
    (supportedCoefficientTensor_ordinaryOpenSecond A f g b d V)
  have he := exactSquare G F₁ F₂ G' F₁' F₂' H a₀ a₁ a₂
    (exactTensorHom (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V))
    (supportedComplexComparisonNatTrans G F₁ F₂ τ)
    (supportedComplexComparisonNatTrans G' F₁' F₂' τ') t t' ht₀ ht₁
    (exactTensorHom_fac (ModuleCat.{u + 1} A) (supportedSecondOpenMap f g V)) hs M N
  exact he

end AlgebraicGeometry.Etale
