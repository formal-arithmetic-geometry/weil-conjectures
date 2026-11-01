/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineZeroPurity.CoordinateZeroBaseChange
import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
import all WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import all WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
import WeilConjectures.SixFunctors.ProEtale.RingSheaf.UpperStarSquare

/-! # Closed-source comparison in coordinate base change -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open scoped CategoryTheory.Functor
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry WeilConjectures
set_option allowUnsafeReducibility true in
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor HasDerivedCategory.ofIsGrothendieckAbelian
  DerivedCategory.singleFunctors DerivedCategory.singleFunctor ProEtale.rightDerivedLowerShriek
  Adjunction.derivedAdjunction Functor.singleFunctorCompLeftDerivedFunctorIso
  Functor.singleFunctorCompRightDerivedFunctorIso
section
open MonoidalCategory
universe vC vD uC uD
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{vC} C] [HasDerivedCategory.{vD} D]
  [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]


private theorem single_mate (adj : f ⊣ g) (M : D) :
    (mateEquiv adj adj.derivedAdjunction
      f.singleFunctorCompLeftDerivedFunctorIso.hom).app M =
      g.singleFunctorCompRightDerivedFunctorIso.inv.app M := by
  have hm := CategoryTheory.mate_app_eq_adjunct adj adj.derivedAdjunction
    f.singleFunctorCompLeftDerivedFunctorIso.hom M
  apply (cancel_mono (g.singleFunctorCompRightDerivedFunctorIso.hom.app M)).1
  rw [hm, Adjunction.homEquiv_unit, Iso.inv_hom_id_app]
  rw [← Adjunction.derivedSingleUnit_eq]
  have h := Adjunction.derivedSingleUnit_comp_comparison adj (g.obj M) M
    (adj.counit.app M)
  rw [Adjunction.homEquiv_unit, Adjunction.right_triangle_components,
    (DerivedCategory.singleFunctor C 0).map_id] at h
  exact h

private theorem inverse_square {E : Type*} [Category E]
    {U V W X Y : E} (p : U ≅ V) (q : W ≅ U) (e : W ⟶ X) (e' : V ⟶ Y)
    (d : X ≅ Y) (h : q.hom ≫ p.hom ≫ e' = e ≫ d.hom) :
    p.inv ≫ q.inv ≫ e = e' ≫ d.inv := by
  apply (cancel_mono d.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h]
  simp only [Iso.inv_hom_id_assoc]

private theorem cancel_mate_cube {E : Type*} [Category E]
    {A B C D T F : E} (p : A ≅ B) (q : C ≅ D) (r : D ≅ T)
    (a : B ⟶ C) (b : A ⟶ F) (c : F ⟶ T)
    (h : a ≫ q.hom ≫ r.hom = p.inv ≫ b ≫ c) :
    b ≫ c ≫ r.inv ≫ q.inv = p.hom ≫ a := by
  have hh := congrArg (fun z ↦ p.hom ≫ z ≫ r.inv ≫ q.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using hh.symm

private theorem normalized_mate_unit
    {C₀ D₀ C₁ D₁ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    [MonoidalCategory C₀] [MonoidalCategory D₀]
    [MonoidalCategory C₁] [MonoidalCategory D₁]
    (U : C₀ ⥤ C₁) (V : D₀ ⥤ D₁) (R : C₀ ⥤ D₀) (R' : C₁ ⥤ D₁)
    [U.Monoidal] [V.Monoidal] [R.LaxMonoidal] [R'.LaxMonoidal]
    (m : R ⋙ V ⟶ U ⋙ R') [NatTrans.IsMonoidal m]
    {M : C₀} {N : D₀} {M' : C₁} {N' : D₁}
    (eM : M ≅ 𝟙_ C₀) (eN : N ≅ 𝟙_ D₀)
    (eM' : M' ≅ 𝟙_ C₁) (eN' : N' ≅ 𝟙_ D₁)
    (p : U.obj M ≅ M') (q : V.obj N ≅ N')
    (hp : p.hom ≫ eM'.hom = U.map eM.hom ≫ Functor.OplaxMonoidal.η U)
    (hq : q.hom ≫ eN'.hom = V.map eN.hom ≫ Functor.OplaxMonoidal.η V) :
    V.map (eN.hom ≫ Functor.LaxMonoidal.ε R ≫ R.map eM.inv) ≫
        m.app M ≫ R'.map p.hom =
      q.hom ≫ eN'.hom ≫ Functor.LaxMonoidal.ε R' ≫ R'.map eM'.inv := by
  have hg : U.map eM.inv ≫ p.hom = Functor.OplaxMonoidal.η U ≫ eM'.inv := by
    apply (cancel_mono eM'.hom).1
    simp only [Category.assoc, hp, ← U.map_comp_assoc, Iso.inv_hom_id,
      U.map_id, Category.id_comp, Category.comp_id]
  have hn := m.naturality eM.inv
  dsimp only [Functor.comp_map] at hn
  simp only [V.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← R'.map_comp, hg, R'.map_comp, reassoc_of% hq]
  apply (cancel_epi (V.map eN.hom)).2
  apply (cancel_epi (Functor.LaxMonoidal.ε V)).1
  have hu := NatTrans.IsMonoidal.unit (τ := m)
  dsimp only [Functor.LaxMonoidal.comp_ε] at hu
  rw [reassoc_of% hu]
  simp only [← R'.map_comp_assoc, Functor.Monoidal.ε_η,
    Functor.Monoidal.ε_η_assoc, R'.map_id, Category.id_comp]

private theorem normalized_exchange_unique
    {C₀ D₀ C₁ D₁ : Type*}
    [Category C₀] [Category D₀] [Category C₁] [Category D₁]
    [MonoidalCategory C₀] [MonoidalCategory D₀]
    [MonoidalCategory C₁] [MonoidalCategory D₁]
    (U : C₀ ⥤ C₁) (V : D₀ ⥤ D₁) (R : C₀ ⥤ D₀) (R' : C₁ ⥤ D₁)
    [U.Monoidal] [V.Monoidal] [R.LaxMonoidal] [R'.LaxMonoidal]
    (m : R ⋙ V ⟶ U ⋙ R') [NatTrans.IsMonoidal m]
    {M : C₀} {N : D₀} {M' : C₁} {N' : D₁}
    (eM : M ≅ 𝟙_ C₀) (eN : N ≅ 𝟙_ D₀)
    (eM' : M' ≅ 𝟙_ C₁) (eN' : N' ≅ 𝟙_ D₁)
    (p : U.obj M ≅ M') (q : V.obj N ≅ N')
    (hp : p.hom ≫ eM'.hom = U.map eM.hom ≫ Functor.OplaxMonoidal.η U)
    (hq : q.hom ≫ eN'.hom = V.map eN.hom ≫ Functor.OplaxMonoidal.η V)
    (r : N ⟶ R.obj M) (r' : N' ⟶ R'.obj M') [Epi (V.map r)]
    (t : V.obj (R.obj M) ⟶ R'.obj M')
    (hr : r = eN.hom ≫ Functor.LaxMonoidal.ε R ≫ R.map eM.inv)
    (hr' : r' = eN'.hom ≫ Functor.LaxMonoidal.ε R' ≫ R'.map eM'.inv)
    (ht : V.map r ≫ t = q.hom ≫ r') :
    m.app M ≫ R'.map p.hom = t := by
  apply (cancel_epi (V.map r)).1
  calc
    V.map r ≫ (m.app M ≫ R'.map p.hom) = q.hom ≫ r' := by
      rw [hr, hr']
      exact normalized_mate_unit U V R R' m eM eN eM' eN' p q hp hq
    _ = V.map r ≫ t := ht.symm

private theorem exact_mate_isMonoidal
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory C] [MonoidalCategory D]
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    [F.Monoidal] [K.Monoidal] [G.Monoidal] [H.Monoidal]
    [R.LaxMonoidal] [S.LaxMonoidal]
    (a : F ⊣ R) (b : K ⊣ S) [a.IsMonoidal] [b.IsMonoidal]
    (θ : G ⋙ K ⟶ F ⋙ H) [NatTrans.IsMonoidal θ] :
    NatTrans.IsMonoidal (mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).natTrans := by
  change NatTrans.IsMonoidal (_ ≫ _ ≫ _ ≫ _ ≫ _ ≫ _ ≫ _ ≫ _ ≫ _)
  infer_instance

private theorem normalized_single_exchange
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (aF : F ⊣ R) (aK : K ⊣ S) (aF' : F' ⊣ R') (aK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (pF : a ⋙ F' ≅ F ⋙ b) (pG : a ⋙ G' ≅ G ⋙ c)
    (pH : b ⋙ H' ≅ H ⋙ d) (pK : c ⋙ K' ≅ K ⋙ d)
    (qF : b ⋙ R' ≅ R ⋙ a) (qK : d ⋙ S' ≅ S ⋙ c)
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      K'.map (pG.hom.app X) ≫ pK.hom.app (G.obj X) ≫ d.map (θ.app X) =
        θ'.app (a.obj X) ≫ H'.map (pF.hom.app X) ≫ pH.hom.app (F.obj X))
    (E : B)
    (e : G.obj (R.obj E) ⟶ S.obj (H.obj E))
    (e' : G'.obj (R'.obj (b.obj E)) ⟶ S'.obj (H'.obj (b.obj E)))
    (he : (mateEquiv aF aK (TwoSquare.mk _ _ _ _ θ)).app E = e)
    (he' : (mateEquiv aF' aK' (TwoSquare.mk _ _ _ _ θ')).app (b.obj E) = e')
    (hF : (mateEquiv aF aF' (TwoSquare.mk _ _ _ _ pF.hom)).app E = qF.inv.app E)
    (hK : (mateEquiv aK aK' (TwoSquare.mk _ _ _ _ pK.hom)).app (H.obj E) =
      qK.inv.app (H.obj E)) :
    G'.map (qF.inv.app E) ≫ e' ≫
        S'.map (pH.hom.app E) ≫ qK.hom.app (H.obj E) =
      pG.hom.app (R.obj E) ≫ c.map e := by
  have h := CategoryTheory.exchangeMate_cube_all_normalized aF aK aF' aK' a b c d
    pF.symm pG.symm pH.symm pK.symm θ θ' hc E
    (qF.inv.app E) (qK.inv.app (H.obj E)) e e' he he' hF hK
  have hh := cancel_mate_cube (pG.app (R.obj E)) (qK.app (H.obj E)).symm
    (S'.mapIso (pH.app E).symm) _ _ _ h
  simpa only [Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_inv] using hh

section
variable {E : Type*} [Category E] [Abelian E] [HasDerivedCategory E]
  [MonoidalCategory D] [MonoidalPreadditive D] [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

attribute [local instance] Limits.comp_preservesFiniteLimits Limits.comp_preservesFiniteColimits

omit [HasKInjectiveResolutions D] in
private theorem composition_single (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : H ≅ F ⋙ G) (M : C) :
    ((Functor.leftDerivedFunctorNatIso H e) ≪≫
      Functor.leftDerivedFunctorCompIso F G).hom.app
        ((DerivedCategory.singleFunctor C 0).obj M) ≫
      G.leftDerivedFunctor.map (F.singleFunctorCompLeftDerivedFunctorIso.hom.app M) ≫
      G.singleFunctorCompLeftDerivedFunctorIso.hom.app (F.obj M) =
    H.singleFunctorCompLeftDerivedFunctorIso.hom.app M ≫
      (DerivedCategory.singleFunctor E 0).map (e.hom.app M) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.leftDerivedFunctorCompIso_hom_app_singleFunctor_obj,
    Functor.leftDerivedFunctorNatIso_hom_app_singleFunctor_obj]

end

private theorem normalize_single_exchange
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (s : A ⥤ C) (t : B ⥤ D) (F : A ⥤ B) (G : C ⥤ D)
    (q : s ⋙ G ≅ F ⋙ t) {M N : A} {L : C} {E : B} {X Y : D}
    (a : X ⟶ Y) (b : Y ⟶ G.obj L) (u : L ⟶ s.obj M) (p : L ⟶ s.obj N)
    (c : M ⟶ N) (δ : X ⟶ t.obj E) (e : E ⟶ F.obj M) (e' : E ⟶ F.obj N)
    (hp : p = u ≫ s.map c)
    (hm : a ≫ b ≫ G.map u ≫ q.hom.app M = δ ≫ t.map e)
    (he : e ≫ F.map c = e') :
    a ≫ b ≫ G.map p ≫ q.hom.app N = δ ≫ t.map e' := by
  have hn := q.hom.naturality c
  dsimp only [Functor.comp_map] at hn
  rw [hp, G.map_comp]
  simp only [Category.assoc]
  rw [hn, reassoc_of% hm, ← t.map_comp, he]

private theorem cancel_inv_comparison
    {C D : Type*} [Category C] [Category D] (V : C ⥤ D)
    {U W : C} {Y Z : D} (e : U ≅ W)
    (b : V.obj U ⟶ Y) (c : Y ⟶ Z) (δ : V.obj W ⟶ Z)
    (h : V.map e.inv ≫ b ≫ c = δ) :
    b ≫ c = V.map e.hom ≫ δ := by
  apply (cancel_epi (V.map e.inv)).1
  simpa only [Category.assoc, ← V.map_comp_assoc, Iso.inv_hom_id,
    V.map_id, Category.id_comp] using h

private theorem transport_proper_comparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    (V : C ⥤ D) (F G : E ⥤ D) (t' : F ≅ G)
    {U U₀ W : C} (t : U ≅ U₀) (a : U₀ ⟶ W)
    {K L : E} (p : K ≅ L) {W' : D} (a' : G.obj L ⟶ W')
    (q : V.obj U ≅ F.obj K) (e : U ≅ W) (e' : F.obj L ≅ W')
    (d : V.obj W ≅ W') (b : V.obj U₀ ⟶ G.obj K)
    (he : e.hom = t.hom ≫ a) (he' : e'.hom = t'.hom.app L ≫ a')
    (hq : q.hom = V.map t.hom ≫ b ≫ t'.inv.app K)
    (h : b ≫ G.map p.hom ≫ a' = V.map a ≫ d.hom) :
    F.map p.inv ≫ q.inv ≫ V.map e.hom = e'.hom ≫ d.inv := by
  have hf : q.hom ≫ F.map p.hom ≫ e'.hom = V.map e.hom ≫ d.hom := by
    rw [he, he', hq]
    simp only [V.map_comp, Category.assoc]
    rw [reassoc_of% NatIso.naturality_1 t' p.hom, h]
  exact inverse_square (F.mapIso p) q (V.map e.hom) e'.hom d hf

end

private theorem closed_single_hom
    {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{u + 1} C]
    [HasDerivedCategory.{u + 1} D] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : DerivedCategory C ⥤ DerivedCategory D) (t : G ≅ F.rightDerivedFunctor) (M : C) :
    (AlgebraicGeometry.ProEtale.AffineZeroPurity.closedSingleComparison F G t M).hom =
      t.hom.app ((DerivedCategory.singleFunctor C 0).obj M) ≫
        F.singleFunctorCompRightDerivedFunctorIso.hom.app M := by
  unfold AlgebraicGeometry.ProEtale.AffineZeroPurity.closedSingleComparison
    Functor.singleFunctorCompRightDerivedFunctorIso
  rfl

section
universe v₀ v₁ v₂ v₃ u₀ u₁ u₂ u₃
variable {C₀ : Type u₀} {D₀ : Type u₁} {C₁ : Type u₂} {D₁ : Type u₃}
  [Category.{v₀} C₀] [Category.{v₁} D₀] [Category.{v₂} C₁] [Category.{v₃} D₁]
  [Abelian C₀] [Abelian D₀] [Abelian C₁] [Abelian D₁]
  [HasDerivedCategory.{v₀} C₀] [HasDerivedCategory.{v₁} D₀]
  [HasDerivedCategory.{v₂} C₁] [HasDerivedCategory.{v₃} D₁]
  [HasKInjectiveResolutions D₀] [HasKInjectiveResolutions D₁]
  [MonoidalCategory C₀] [MonoidalPreadditive C₀] [HasCountableCoproducts C₀]
  [HasColimitsOfShape ℤ C₀] [HasExactColimitsOfShape ℤ C₀]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₀), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₀), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₀), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C₀), PreservesColimitsOfShape ℤ ((curriedTensor C₀).obj X)]
  [∀ (X : C₀), PreservesColimitsOfShape ℤ ((curriedTensor C₀).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₀]
  [MonoidalCategory D₀] [MonoidalPreadditive D₀] [HasCountableCoproducts D₀]
  [HasColimitsOfShape ℤ D₀] [HasExactColimitsOfShape ℤ D₀]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D₀), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D₀), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D₀), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D₀), PreservesColimitsOfShape ℤ ((curriedTensor D₀).obj X)]
  [∀ (X : D₀), PreservesColimitsOfShape ℤ ((curriedTensor D₀).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D₀]
  [MonoidalCategory C₁] [MonoidalPreadditive C₁] [HasCountableCoproducts C₁]
  [HasColimitsOfShape ℤ C₁] [HasExactColimitsOfShape ℤ C₁]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C₁), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C₁), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).obj X)]
  [∀ (X : C₁), PreservesColimitsOfShape ℤ ((curriedTensor C₁).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C₁]

private theorem exact_derived_exchange
    {F : C₀ ⥤ D₀} {R : D₀ ⥤ C₀} {G : C₀ ⥤ C₁} {H : D₀ ⥤ D₁}
    {K : C₁ ⥤ D₁} {S : D₁ ⥤ C₁}
    [F.Additive] [R.Additive] [G.Additive] [H.Additive] [K.Additive] [S.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (a : F ⊣ R) (b : K ⊣ S) (θ : G ⋙ K ⟶ F ⋙ H)
    (θ' : G.leftDerivedFunctor ⋙ K.leftDerivedFunctor ⟶
      F.leftDerivedFunctor ⋙ H.leftDerivedFunctor)
    (hc : ∀ X : C₀,
      K.leftDerivedFunctor.map (G.singleFunctorCompLeftDerivedFunctorIso.hom.app X) ≫
        K.singleFunctorCompLeftDerivedFunctorIso.hom.app (G.obj X) ≫
        (DerivedCategory.singleFunctor D₁ 0).map (θ.app X) =
      θ'.app ((DerivedCategory.singleFunctor C₀ 0).obj X) ≫
        H.leftDerivedFunctor.map (F.singleFunctorCompLeftDerivedFunctorIso.hom.app X) ≫
        H.singleFunctorCompLeftDerivedFunctorIso.hom.app (F.obj X)) (M : D₀) :
    G.leftDerivedFunctor.map (R.singleFunctorCompRightDerivedFunctorIso.inv.app M) ≫
        (mateEquiv a.derivedAdjunction b.derivedAdjunction θ').app
          ((DerivedCategory.singleFunctor D₀ 0).obj M) ≫
        S.rightDerivedFunctor.map (H.singleFunctorCompLeftDerivedFunctorIso.hom.app M) ≫
        S.singleFunctorCompRightDerivedFunctorIso.hom.app (H.obj M) =
      G.singleFunctorCompLeftDerivedFunctorIso.hom.app (R.obj M) ≫
        (DerivedCategory.singleFunctor C₁ 0).map ((mateEquiv a b θ).app M) := by
  exact normalized_single_exchange a b a.derivedAdjunction b.derivedAdjunction
    (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
    (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
    F.singleFunctorCompLeftDerivedFunctorIso G.singleFunctorCompLeftDerivedFunctorIso
    H.singleFunctorCompLeftDerivedFunctorIso K.singleFunctorCompLeftDerivedFunctorIso
    R.singleFunctorCompRightDerivedFunctorIso S.singleFunctorCompRightDerivedFunctorIso
    θ θ' hc M ((mateEquiv a b θ).app M)
    ((mateEquiv a.derivedAdjunction b.derivedAdjunction θ').app
      ((DerivedCategory.singleFunctor _ 0).obj M))
    rfl rfl (single_mate a M) (single_mate b (H.obj M))

end

namespace AlgebraicGeometry.ProEtale.AffineZeroPurity
open AffineSpacePurity

set_option backward.defeqAttrib.useBackward true
set_option allowUnsafeReducibility true in
attribute [local reducible] Functor.Monoidal.ofOplaxMonoidal
  Functor.CoreMonoidal.ofOplaxMonoidal Functor.CoreMonoidal.toMonoidal
  Functor.CoreMonoidal.toOplaxMonoidal Functor.CoreMonoidal.toLaxMonoidal
  ProEtale.monoidal_upperStar Etale.monoidal_upperStar monoidal_comparisonUpperStar
set_option allowUnsafeReducibility true in
attribute [local reducible] cupSingle inverseImage
  PurityFiniteSetting.constant PurityFiniteSetting.constantEtale
  PurityFiniteSetting.functorialCupSource PurityFiniteSetting.functorialCupRestriction
  PurityFiniteSetting.functorialCupInverseImage PurityFiniteSetting.functorialCupConstantPullback
attribute [local irreducible] ProEtale.upperStar ProEtale.lowerStar
  ProEtale.upperStarLowerStarAdjunction mateEquiv conjugateEquiv

private theorem pullback_comp_single (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.map
        ((upperStar (ModuleCat.{u + 1} A) g).singleFunctorCompLeftDerivedFunctorIso.hom.app M) ≫
      (upperStar (ModuleCat.{u + 1} A) f).singleFunctorCompLeftDerivedFunctorIso.hom.app
        ((upperStar (ModuleCat.{u + 1} A) g).obj M) =
    (upperStar (ModuleCat.{u + 1} A) (f ≫ g)).singleFunctorCompLeftDerivedFunctorIso.hom.app M ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((upperStarComp (ModuleCat.{u + 1} A) f g).hom.app M) := by
  exact composition_single (upperStar (ModuleCat.{u + 1} A) g)
    (upperStar (ModuleCat.{u + 1} A) f) (upperStar (ModuleCat.{u + 1} A) (f ≫ g))
    (upperStarComp (ModuleCat.{u + 1} A) f g) M

private theorem pullback_congr_single (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f g : X ⟶ Y} (e : f = g)
    (M : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) :
    (leftDerivedUpperStarCongr (ModuleCat.{u + 1} A) e).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) g).singleFunctorCompLeftDerivedFunctorIso.hom.app M =
    (upperStar (ModuleCat.{u + 1} A) f).singleFunctorCompLeftDerivedFunctorIso.hom.app M ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((upperStarCongr (ModuleCat.{u + 1} A) e).hom.app M) := by
  subst e
  simp [leftDerivedUpperStarCongr, upperStarCongr]

private theorem pullback_square_single (A : Type (u + 1)) [CommRing A]
    {Z' Z X' X : Scheme.{u}} {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    (sq : CommSq g i' i h)
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (upperStar (ModuleCat.{u + 1} A) i').leftDerivedFunctor.map
        ((upperStar (ModuleCat.{u + 1} A) h).singleFunctorCompLeftDerivedFunctorIso.hom.app M) ≫
      (upperStar (ModuleCat.{u + 1} A) i').singleFunctorCompLeftDerivedFunctorIso.hom.app
        ((upperStar (ModuleCat.{u + 1} A) h).obj M) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((upperStarCompIso (ModuleCat.{u + 1} A) sq.w.symm).hom.app M) =
    (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} A) sq).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.map
        ((upperStar (ModuleCat.{u + 1} A) i).singleFunctorCompLeftDerivedFunctorIso.hom.app M) ≫
      (upperStar (ModuleCat.{u + 1} A) g).singleFunctorCompLeftDerivedFunctorIso.hom.app
        ((upperStar (ModuleCat.{u + 1} A) i).obj M) := by
  apply (cancel_epi ((leftDerivedUpperStarComp
    (ModuleCat.{u + 1} A) i' h).hom.app ((DerivedCategory.singleFunctor _ 0).obj M))).1
  simp only [leftDerivedUpperStarSquareIso, upperStarCompIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% pullback_comp_single A i' h M, pullback_comp_single A g i M,
    reassoc_of% pullback_congr_single A sq.w.symm M]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]

set_option maxHeartbeats 400000 in
-- Checking the canonical derived comparison at sheaf instances needs a larger kernel budget.
private theorem derived_mate_single (A : Type (u + 1)) [CommRing A]
    {Z' Z X' X : Scheme.{u}} {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    [PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) i)]
    [PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) i')]
    (sq : CommSq g i' i h)
    (M : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)) :
    (upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.map
        ((lowerStar (ModuleCat.{u + 1} A) i).singleFunctorCompRightDerivedFunctorIso.inv.app M) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app
        ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      (lowerStar (ModuleCat.{u + 1} A) i').rightDerivedFunctor.map
        ((upperStar (ModuleCat.{u + 1} A) g).singleFunctorCompLeftDerivedFunctorIso.hom.app M) ≫
      (lowerStar (ModuleCat.{u + 1} A) i').singleFunctorCompRightDerivedFunctorIso.hom.app
        ((upperStar (ModuleCat.{u + 1} A) g).obj M) =
    (upperStar (ModuleCat.{u + 1} A) h).singleFunctorCompLeftDerivedFunctorIso.hom.app
        ((lowerStar (ModuleCat.{u + 1} A) i).obj M) ≫
      (DerivedCategory.singleFunctor _ 0).map
        ((mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i)
          (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i')
          (upperStarCompIso (ModuleCat.{u + 1} A) sq.w.symm).hom).app M) := by
  exact exact_derived_exchange
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i')
    (upperStarCompIso (ModuleCat.{u + 1} A) sq.w.symm).hom
    (leftDerivedUpperStarSquareIso (ModuleCat.{u + 1} A) sq).hom
    (pullback_square_single A sq) M

section

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

private def frameUnitIso (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) :
    P.constant X ≅ 𝟙_ (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} P.Coefficient)) := cupConstantIso P X

private theorem frame_restriction_unit (P : PurityFiniteSetting.{u})
    {Z X : Scheme.{u}} (i : Z ⟶ X) :
    cupCoefficientRestriction P i = (frameUnitIso P X).hom ≫
      Functor.LaxMonoidal.ε (lowerStar (ModuleCat.{u + 1} P.Coefficient) i) ≫
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) i).map (frameUnitIso P Z).inv := by
  exact cupRestriction_eq_laxUnit P i

private theorem frame_pullback_unit (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (P.frameConstantPullback f).hom ≫ (frameUnitIso P X).hom =
    (upperStar (ModuleCat.{u + 1} P.Coefficient) f).map (frameUnitIso P Y).hom ≫
      Functor.OplaxMonoidal.η (upperStar (ModuleCat.{u + 1} P.Coefficient) f) := by
  let A := ModuleCat.{u + 1} P.Coefficient
  let V := upperStar A f
  let FX := comparisonUpperStar A X
  let FY := comparisonUpperStar A Y
  let E := Etale.upperStar A f
  let τ := comparisonUpperStarCompUpperStarIso A f
  have hs : (Scheme.upperStarConstantSheafIso A f).hom.app
      (ModuleCat.of P.Coefficient P.Coefficient) =
      Functor.OplaxMonoidal.η E := Etale.upperStarConstantSheafIso_hom_app_tensorUnit A f
  change (τ.hom.app (P.constantEtale Y) ≫
    FX.map ((Scheme.upperStarConstantSheafIso A f).hom.app
      (ModuleCat.of P.Coefficient P.Coefficient))) ≫ (cupConstantIso P X).hom =
    V.map (cupConstantIso P Y).hom ≫ Functor.OplaxMonoidal.η V
  rw [hs, constant_iso_eta, constant_iso_eta]
  change (τ.hom.app (𝟙_ _ ) ≫ FX.map (Functor.OplaxMonoidal.η E)) ≫
    Functor.OplaxMonoidal.η FX =
    V.map (Functor.OplaxMonoidal.η FY) ≫ Functor.OplaxMonoidal.η V
  have hu := NatTrans.IsMonoidal.unit (τ := τ.hom)
  apply (cancel_epi (Functor.LaxMonoidal.ε V ≫
    V.map (Functor.LaxMonoidal.ε FY))).1
  dsimp only [Functor.LaxMonoidal.comp_ε] at hu
  simp only [Category.assoc] at hu ⊢
  rw [reassoc_of% hu]
  change Functor.LaxMonoidal.ε FX ≫
    FX.map (Functor.LaxMonoidal.ε E) ≫ FX.map (Functor.OplaxMonoidal.η E) ≫
    Functor.OplaxMonoidal.η FX =
    Functor.LaxMonoidal.ε V ≫ V.map (Functor.LaxMonoidal.ε FY) ≫
    V.map (Functor.OplaxMonoidal.η FY) ≫ Functor.OplaxMonoidal.η V
  erw [← FX.map_comp_assoc, Functor.Monoidal.ε_η E, FX.map_id, Category.id_comp,
    Functor.Monoidal.ε_η FX, ← V.map_comp_assoc, Functor.Monoidal.ε_η FY,
    V.map_id, Category.id_comp, Functor.Monoidal.ε_η V]

attribute [local irreducible] frameUnitIso

private theorem comp_monoidal (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (upperStarComp (ModuleCat.{u + 1} A) f g).inv := by
  exact RingSheaf.isMonoidal_upperStarComp_inv (R := A) f g

private theorem square_monoidal (A : Type (u + 1)) [CommRing A]
    {Z' Z X' X : Scheme.{u}} {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    (sq : CommSq g i' i h) :
    NatTrans.IsMonoidal (upperStarCompIso (ModuleCat.{u + 1} A) sq.w.symm).hom := by
  have := comp_monoidal A i' h
  have hc : NatTrans.IsMonoidal (upperStarComp (ModuleCat.{u + 1} A) g i).hom := by
    have : NatTrans.IsMonoidal (upperStarComp (ModuleCat.{u + 1} A) g i).symm.hom :=
      comp_monoidal A g i
    exact inferInstanceAs
      (NatTrans.IsMonoidal (upperStarComp (ModuleCat.{u + 1} A) g i).symm.inv)
  have he : NatTrans.IsMonoidal (upperStarCongr (ModuleCat.{u + 1} A) sq.w.symm).hom := by
    have hc {Y Z : Scheme.{u}} {a b : Y ⟶ Z} (e : a = b) :
        NatTrans.IsMonoidal (upperStarCongr (ModuleCat.{u + 1} A) e).hom := by
      subst e
      exact inferInstanceAs (NatTrans.IsMonoidal (𝟙 _))
    exact hc sq.w.symm
  dsimp [upperStarCompIso]
  infer_instance

private theorem ordinary_mate_monoidal (A : Type (u + 1)) [CommRing A]
    {Z' Z X' X : Scheme.{u}} {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    (sq : CommSq g i' i h) :
    NatTrans.IsMonoidal (mateEquiv
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i')
      (upperStarCompIso (ModuleCat.{u + 1} A) sq.w.symm).hom).natTrans := by
  have := square_monoidal A sq
  have hi : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i)
      Functor.Monoidal.toOplaxMonoidal _ := isMonoidal_upperStarLowerStarAdjunction _ _
  have hi' : @Adjunction.IsMonoidal _ _ _ _ _ _ _ _
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i')
      Functor.Monoidal.toOplaxMonoidal _ := isMonoidal_upperStarLowerStarAdjunction _ _
  exact exact_mate_isMonoidal
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i')
    (upperStarCompIso (ModuleCat.{u + 1} A) sq.w.symm).hom

set_option allowUnsafeReducibility true in
attribute [local irreducible] Sheaf.monoidalCategory
  PurityFiniteSetting.constant PurityFiniteSetting.constantEtale
  cupConstantIso cupCoefficientRestriction

private theorem ordinary_exchange (P : PurityFiniteSetting.{u})
    {Z' Z X' X : Scheme.{u}} (g : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (h : X' ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion i']
    (sq : ChosenCartesianSquare g i' i h) :
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) i)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) i')
      (upperStarCompIso (ModuleCat.{u + 1} P.Coefficient) sq.toCommSq.w.symm).hom).app
        (P.constant Z) ≫
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) i').map
        (P.frameConstantPullback g).hom =
      (P.functorialCupExchange true i i' h g sq).hom := by
  let A := ModuleCat.{u + 1} P.Coefficient
  let U := upperStar A g
  let V := upperStar A h
  let R := lowerStar A i
  let R' := lowerStar A i'
  let m := (mateEquiv (upperStarLowerStarAdjunction A i)
    (upperStarLowerStarAdjunction A i') (upperStarCompIso A sq.toCommSq.w.symm).hom).natTrans
  have hm : NatTrans.IsMonoidal m := ordinary_mate_monoidal P.Coefficient sq.toCommSq
  have hnorm := (P.functorialCupExchange_existsUnique true i i' h g sq).choose_spec.1
  have hepi : Epi (cupCoefficientRestriction P i) := cupRestriction_epi P i
  have hepi' : Epi (V.map (cupCoefficientRestriction P i)) := V.map_epi _
  exact normalized_exchange_unique U V R R' m
    (frameUnitIso P Z) (frameUnitIso P X)
    (frameUnitIso P Z') (frameUnitIso P X')
    (P.frameConstantPullback g) (P.frameConstantPullback h)
    (frame_pullback_unit P g) (frame_pullback_unit P h)
    (cupCoefficientRestriction P i) (cupCoefficientRestriction P i')
    (P.functorialCupExchange true i i' h g sq).hom
    (frame_restriction_unit P i) (frame_restriction_unit P i') hnorm

end

private theorem unitPullback_single (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) :
    (unitPullback P n g).hom =
      (Functor.singleFunctorCompLeftDerivedFunctorIso
        (upperStar (ModuleCat.{u + 1} (setting P n).Coefficient) g)).hom.app
          ((setting P n).constant B) ≫
      (DerivedCategory.singleFunctor _ 0).map ((setting P n).frameConstantPullback g).hom := by
  change (inverseImage (setting P n).Coefficient g).map (𝟙 _) ≫
    (pullbackSingle (setting P n).Coefficient g ((setting P n).constant B)
      ((setting P n).constant B') ((setting P n).frameConstantPullback g)).hom ≫ 𝟙 _ = _
  rw [(inverseImage (setting P n).Coefficient g).map_id]
  simp only [pullbackSingle, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Category.id_comp, Category.comp_id,
    Functor.singleFunctorCompLeftDerivedFunctorIso, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app,
    leftDerivedUpperStarIsoMapDerivedCategory, Category.assoc]

private theorem coordinateSourcePullback_single (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (c : ℕ) :
    (coordinateSourcePullback P n g c).hom =
      (upperStar (ModuleCat.{u + 1} (setting P n).Coefficient)
        (spaceMap g c)).singleFunctorCompLeftDerivedFunctorIso.hom.app
          ((lowerStar (ModuleCat.{u + 1} (setting P n).Coefficient) (zero B c)).obj
            ((setting P n).constant B)) ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((setting P n).functorialCupExchange true (zero B c) (zero B' c)
            (spaceMap g c) g (zeroSquare g c)).hom := by
  simp only [coordinateSourcePullback, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.singleFunctorCompLeftDerivedFunctorIso, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, leftDerivedUpperStarIsoMapDerivedCategory,
    Category.assoc]

private theorem closed_exchange_hom (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z' Z X' X : Scheme.{u}} (g : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (h : X' ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion i']
    [HasCompactification i] [HasCompactification i'] (cart : IsPullback g i' i h)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A)))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) Z K) :
    (closedExchange A g i' i h cart K hK).hom =
      (inverseImage A h).map
        ((rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
          (ModuleCat.{u + 1} A) i).hom.app K) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) cart.toCommSq).app K ≫
      (rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar
        (ModuleCat.{u + 1} A) i').inv.app ((inverseImage A g).obj K) := by
  unfold closedExchange
  rfl


-- Transport the square witness before specializing to the coordinate morphisms.
private theorem ordinary_exchange_cartesian (P : PurityFiniteSetting.{u})
    {Z' Z X' X : Scheme.{u}} (g : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (h : X' ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion i']
    (cart : IsPullback g i' i h) (sq : ChosenCartesianSquare g i' i h) :
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) i)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) i')
      (upperStarCompIso (ModuleCat.{u + 1} P.Coefficient) cart.toCommSq.w.symm).hom).app
        (P.constant Z) ≫
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) i').map
        (P.frameConstantPullback g).hom =
      (P.functorialCupExchange true i i' h g sq).hom := by
  exact Eq.ndrec (motive := fun q : CommSq g i' i h =>
    (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) i)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} P.Coefficient) i')
      (upperStarCompIso (ModuleCat.{u + 1} P.Coefficient) q.w.symm).hom).app
        (P.constant Z) ≫
      (lowerStar (ModuleCat.{u + 1} P.Coefficient) i').map
        (P.frameConstantPullback g).hom =
      (P.functorialCupExchange true i i' h g sq).hom)
    (ordinary_exchange P g i' i h sq) (Subsingleton.elim sq.toCommSq cart.toCommSq)

set_option maxHeartbeats 400000 in
-- Canonical derived comparison instances need a larger kernel heartbeat budget.
private theorem closed_exact_source_exchange (A₀ : Type (u + 1)) [CommRing A₀] [Finite A₀]
    {Z' Z X' X : Scheme.{u}} (g : Z' ⟶ Z) (i' : Z' ⟶ X') (i : Z ⟶ X) (h : X' ⟶ X)
    [IsClosedImmersion i] [IsClosedImmersion i']
    [PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A₀) i)]
    [PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A₀) i')]
    (cart : IsPullback g i' i h)
    (M : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} A₀))
    (M' : Sheaf (Scheme.ProEt.topology Z') (ModuleCat.{u + 1} A₀))
    (hK : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A₀) Z
      ((DerivedCategory.singleFunctor _ 0).obj M))
    (p₀ : (upperStar (ModuleCat.{u + 1} A₀) g).obj M ≅ M')
    (e₀ : (upperStar (ModuleCat.{u + 1} A₀) h).obj
      ((lowerStar (ModuleCat.{u + 1} A₀) i).obj M) ≅
        (lowerStar (ModuleCat.{u + 1} A₀) i').obj M')
    (hnorm :
      (mateEquiv (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A₀) i)
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A₀) i')
        (upperStarCompIso (ModuleCat.{u + 1} A₀) cart.toCommSq.w.symm).hom).app M ≫
        (lowerStar (ModuleCat.{u + 1} A₀) i').map p₀.hom = e₀.hom)
    (p : (inverseImage A₀ g).obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj M')
    (d : (inverseImage A₀ h).obj ((DerivedCategory.singleFunctor _ 0).obj
      ((lowerStar (ModuleCat.{u + 1} A₀) i).obj M)) ≅
        (DerivedCategory.singleFunctor _ 0).obj
          ((lowerStar (ModuleCat.{u + 1} A₀) i').obj M'))
    (hp : p.hom =
      (Functor.singleFunctorCompLeftDerivedFunctorIso
        (upperStar (ModuleCat.{u + 1} A₀) g)).hom.app M ≫
      (DerivedCategory.singleFunctor _ 0).map p₀.hom)
    (hd : d.hom =
      (Functor.singleFunctorCompLeftDerivedFunctorIso
        (upperStar (ModuleCat.{u + 1} A₀) h)).hom.app
          ((lowerStar (ModuleCat.{u + 1} A₀) i).obj M) ≫
      (DerivedCategory.singleFunctor _ 0).map e₀.hom) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A₀) i').map p.inv ≫
      (closedExchange A₀ g i' i h cart _ hK).inv ≫
      (inverseImage A₀ h).map (closedSingleIso A₀ i M).hom =
        (closedSingleIso A₀ i' M').hom ≫ d.inv := by
  let A := ModuleCat.{u + 1} A₀
  let R := lowerStar A i
  let R' := lowerStar A i'
  let V := inverseImage A₀ h
  let K := (DerivedCategory.singleFunctor _ 0).obj M
  let K' := (DerivedCategory.singleFunctor _ 0).obj M'
  let e := closedSingleIso A₀ i M
  let e' := closedSingleIso A₀ i' M'
  let q := closedExchange A₀ g i' i h cart _ hK
  let pb := p.hom
  have hm := derived_mate_single A₀ cart.toCommSq M
  have hc : V.map (R.singleFunctorCompRightDerivedFunctorIso.inv.app M) ≫
      (derivedBaseChangeMap A cart.toCommSq).app K ≫
      R'.rightDerivedFunctor.map pb ≫
      R'.singleFunctorCompRightDerivedFunctorIso.hom.app M' =
    (upperStar A h).singleFunctorCompLeftDerivedFunctorIso.hom.app (R.obj M) ≫
      (DerivedCategory.singleFunctor _ 0).map e₀.hom := by
    exact normalize_single_exchange
      (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
      R' R'.rightDerivedFunctor R'.singleFunctorCompRightDerivedFunctorIso
      (V.map (R.singleFunctorCompRightDerivedFunctorIso.inv.app M))
      ((derivedBaseChangeMap A cart.toCommSq).app K)
      ((upperStar A g).singleFunctorCompLeftDerivedFunctorIso.hom.app M) pb
      p₀.hom _ _ _ hp hm hnorm
  have hc' : (derivedBaseChangeMap A cart.toCommSq).app K ≫
      R'.rightDerivedFunctor.map pb ≫
      R'.singleFunctorCompRightDerivedFunctorIso.hom.app M' =
    V.map (R.singleFunctorCompRightDerivedFunctorIso.hom.app M) ≫ d.hom := by
    exact cancel_inv_comparison V (R.singleFunctorCompRightDerivedFunctorIso.app M)
      _ _ d.hom (hc.trans hd.symm)
  let t := rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar A i
  let t' := rightDerivedLowerShriekIsoRightDerivedFunctorLowerStar A i'
  have he : e.hom = t.hom.app K ≫
      R.singleFunctorCompRightDerivedFunctorIso.hom.app M := by
    exact closed_single_hom R _ t M
  have he' : e'.hom = t'.hom.app K' ≫
      R'.singleFunctorCompRightDerivedFunctorIso.hom.app M' := by
    exact closed_single_hom R' _ t' M'
  have hq : q.hom = V.map (t.hom.app K) ≫
      (derivedBaseChangeMap A cart.toCommSq).app K ≫
      t'.inv.app ((inverseImage A₀ g).obj K) := by
    exact closed_exchange_hom A₀ g i' i h cart K hK
  exact transport_proper_comparison V (rightDerivedLowerShriek A i')
    R'.rightDerivedFunctor t' (t.app K)
    (R.singleFunctorCompRightDerivedFunctorIso.hom.app M) p
    (R'.singleFunctorCompRightDerivedFunctorIso.hom.app M') q e e' d
    ((derivedBaseChangeMap A cart.toCommSq).app K) he he' hq hc'


set_option maxHeartbeats 400000 in
-- Checking the specialized coordinate comparison needs a larger kernel budget.
/-- The proper derived closed exchange and the degree-zero coefficient exchange
have identical source identifications.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, final rank-one base-change
sentence; parent proof Step 4 (blueprint: lem-pur-coordinate-closed-source-exchange).

Proof: the two zero sections are closed in Noetherian schemes, so their direct
images are exact. Cancel the compact-support-to-proper comparisons from the
definition of closedExchange and the two definitions of closedSingleIso.
For exact closed direct image, the derived base-change mate on the coefficient
single object is the single image of the underived base-change mate, with the
canonical exact pullback and single comparisons. Verify this by transposing:
apply derivedSingleUnit_comp_comparison to the exact closed adjunctions to
identify their single-object units, and use the canonical composition square
of pullbacks to identify the square in the mate. Restricting constants
through this mate commutes with the constant-unit restriction by the adjunction
triangle identities. Since that restriction is epic and exact inverse image
preserves epimorphisms, the underived mate followed by the constant pullback is
the uniquely normalized functorialCupExchange. Apply the single functor and
restore the cancelled proper comparisons. Its inverse form is precisely the
displayed equation, including unitPullback and coordinateSourcePullback.
No purity or exceptional base-change isomorphism is used; empty schemes and
zero coefficients satisfy the same unit and inverse identities. -/
theorem coordinate_closed_source_exchange (P : PurityFiniteSetting.{u}) (n : ℕ)
    {B' B : Scheme.{u}} (g : B' ⟶ B) (aB : B ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aB] [QuasiCompact aB] [IsSeparated aB]
    [LocallyOfFiniteType (g ≫ aB)] [QuasiCompact (g ≫ aB)] [IsSeparated (g ≫ aB)] (c : ℕ) :
    letI := zero_exact P n B aB c
    letI := zero_exact P n B' (g ≫ aB) c
    (rightDerivedLowerShriek (ModuleCat.{u + 1} (setting P n).Coefficient)
          (zero B' c)).map (unitPullback P n g).inv ≫
        (closedExchange (setting P n).Coefficient g (zero B' c) (zero B c)
          (spaceMap g c) (zero_square g c) _ (unit_origin P n B)).inv ≫
        (inverseImage (setting P n).Coefficient (spaceMap g c)).map
          (closedSingleIso (setting P n).Coefficient (zero B c)
            ((setting P n).constant B)).hom =
      (closedSingleIso (setting P n).Coefficient (zero B' c)
        ((setting P n).constant B')).hom ≫ (coordinateSourcePullback P n g c).inv := by
  let := zero_exact P n B aB c
  let := zero_exact P n B' (g ≫ aB) c
  exact closed_exact_source_exchange (setting P n).Coefficient g (zero B' c) (zero B c)
    (spaceMap g c) (zero_square g c) ((setting P n).constant B) ((setting P n).constant B')
    (unit_origin P n B) ((setting P n).frameConstantPullback g)
    ((setting P n).functorialCupExchange true (zero B c) (zero B' c)
      (spaceMap g c) g (zeroSquare g c))
    (ordinary_exchange_cartesian (setting P n) g (zero B' c) (zero B c)
      (spaceMap g c) (zero_square g c) (zeroSquare g c))
    (unitPullback P n g) (coordinateSourcePullback P n g c)
    (unitPullback_single P n g) (coordinateSourcePullback_single P n g c)

end AlgebraicGeometry.ProEtale.AffineZeroPurity
