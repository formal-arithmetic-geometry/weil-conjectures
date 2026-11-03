/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import all WeilConjectures.AlgebraicGeometry.Normalized.NormalizedOriginComparisonCoherence
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothLevelOfOrientation
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteProCoefficientCounitTransport
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.QuotientIntrinsicCtf

/-! # FiniteSmoothProQuotientTransport

A step of finite smooth quotient coherence. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

attribute [local irreducible] ProEtale.pbcComparisonReduction
  scalarPullbackIso ExceptionalCoefficients.tensorIso originReductionMap
  compactSiteMap compactSiteInverse

private def proAssociatorOf {A B C : Type (u + 1)}
    [CommRing A] [CommRing B] [CommRing C]
    (T : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C)
    (h : χ = ψ.comp φ) : proScalar φ T ⋙ proScalar ψ T ≅ proScalar χ T :=
  @ProEtale.pbcFixedScalarExtensionComp.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} T.ProEt) (Scheme.ProEt.topology T)
    A B C inferInstance inferInstance inferInstance φ ψ χ h

private theorem siteScalarComp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (T : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C)
    (h : χ = ψ.comp φ) (K : DerivedCategoryModule A T) :
    (proScalar ψ T).map ((ProEtale.pbcComparisonReduction T φ).hom.app K) ≫
      (ProEtale.pbcComparisonReduction T ψ).hom.app ((ordinaryScalar φ T).obj K) ≫
      (comparison C T).map
        ((ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ h).hom.app K) =
    (proAssociatorOf T φ ψ χ h).hom.app ((comparison A T).obj K) ≫
      (ProEtale.pbcComparisonReduction T χ).hom.app K := by
  with_unfolding_all
    dsimp only [comparison, proScalar, ordinaryScalar, scalarExtension, proAssociatorOf]
    apply (cancel_mono ((ProEtale.pbcComparisonReduction T χ).inv.app K)).1
    simp only [Category.assoc]
    erw [ProEtale.comparisonScalarComp T φ ψ χ h K]
    simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    dsimp only [Functor.comp_obj]
    erw [(proScalar ψ T).map_id]
    simp only [proScalar, Category.id_comp, Category.comp_id]

private theorem originReductionCounit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) (K : proCategory A T) :
    (comparison B T).map (originReductionMap φ T K) ≫
        (ProEtale.derivedComparisonAdjunction (ModuleCat B) T).counit.app
          ((proScalar φ T).obj K) =
      (ProEtale.pbcComparisonReduction T φ).inv.app ((origin A T).obj K) ≫
        (proScalar φ T).map
          ((ProEtale.derivedComparisonAdjunction (ModuleCat A) T).counit.app K) := by
  with_unfolding_all
    unfold originReductionMap
    exact ((ProEtale.derivedComparisonAdjunction (ModuleCat B) T).homEquiv _ _).symm_apply_apply _

private theorem originReductionComp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (T : Scheme.{u}) (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C)
    (h : χ = ψ.comp φ) (K : proCategory A T) :
    (ordinaryScalar ψ T).map (originReductionMap φ T K) ≫
      originReductionMap ψ T ((proScalar φ T).obj K) ≫
      (origin C T).map ((proAssociatorOf T φ ψ χ h).hom.app K) =
    (ProEtale.pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ h).hom.app
        ((origin A T).obj K) ≫ originReductionMap χ T K := by
  with_unfolding_all
    let adj := ProEtale.derivedComparisonAdjunction (ModuleCat C) T
    apply (adj.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    have hn := adj.counit.naturality ((proAssociatorOf T φ ψ χ h).hom.app K)
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    erw [hn, reassoc_of% (originReductionCounit ψ T _)]
    have hs := (ProEtale.pbcComparisonReduction T ψ).inv.naturality
      (originReductionMap φ T K)
    dsimp only [Functor.comp_map] at hs
    erw [reassoc_of% hs, ← (proScalar ψ T).map_comp_assoc,
      originReductionCounit φ T K, Functor.map_comp_assoc]
    have ha := (proAssociatorOf T φ ψ χ h).hom.naturality
      ((ProEtale.derivedComparisonAdjunction (ModuleCat A) T).counit.app K)
    dsimp only [Functor.comp_map] at ha
    erw [ha]
    erw [originReductionCounit χ T K]
    simpa only [Category.assoc, comparison, proScalar, ordinaryScalar, scalarExtension,
      proAssociatorOf, origin, Functor.comp_obj, Functor.id_obj] using
      (congrArg (fun t ↦ t ≫ (proScalar χ T).map
        ((ProEtale.derivedComparisonAdjunction (ModuleCat A) T).counit.app K))
          (ProEtale.comparisonScalarComp T φ ψ χ h ((origin A T).obj K))).symm

section CategoricalTransport
universe v w
variable {C₁ C₂ C₃ D₁ D₂ D₃ P₁ P₂ P₃ Q₁ Q₂ Q₃ : Type v}
  [Category.{w} C₁] [Category.{w} C₂] [Category.{w} C₃]
  [Category.{w} D₁] [Category.{w} D₂] [Category.{w} D₃]
  [Category.{w} P₁] [Category.{w} P₂] [Category.{w} P₃]
  [Category.{w} Q₁] [Category.{w} Q₂] [Category.{w} Q₃]

private def originTransport
    {C D P Q C' D' P' Q' : Type v}
    [Category.{w} C] [Category.{w} D] [Category.{w} P] [Category.{w} Q]
    [Category.{w} C'] [Category.{w} D'] [Category.{w} P'] [Category.{w} Q']
    (O : P ⥤ C) (O' : P' ⥤ C') (V : D ⥤ Q) (V' : D' ⥤ Q')
    (s : C ⥤ C') (t : D ⥤ D') (p : P ⥤ P') (q : Q ⥤ Q')
    (F : C ⥤ D) (F' : C' ⥤ D') (τ : V ⋙ q ≅ t ⋙ V')
    (θ : ∀ K, s.obj (O.obj K) ⟶ O'.obj (p.obj K))
    (c : ∀ J, t.obj (F.obj J) ⟶ F'.obj (s.obj J)) (K : P) :
    q.obj ((O ⋙ F ⋙ V).obj K) ⟶ (O' ⋙ F' ⋙ V').obj (p.obj K) :=
  τ.hom.app (F.obj (O.obj K)) ≫ V'.map (c (O.obj K) ≫ F'.map (θ K))

private theorem originTransport_cocycle
    (O₁ : P₁ ⥤ C₁) (O₂ : P₂ ⥤ C₂) (O₃ : P₃ ⥤ C₃)
    (V₁ : D₁ ⥤ Q₁) (V₂ : D₂ ⥤ Q₂) (V₃ : D₃ ⥤ Q₃)
    (s₁₂ : C₁ ⥤ C₂) (s₂₃ : C₂ ⥤ C₃) (s₁₃ : C₁ ⥤ C₃)
    (t₁₂ : D₁ ⥤ D₂) (t₂₃ : D₂ ⥤ D₃) (t₁₃ : D₁ ⥤ D₃)
    (p₁₂ : P₁ ⥤ P₂) (p₂₃ : P₂ ⥤ P₃) (p₁₃ : P₁ ⥤ P₃)
    (q₁₂ : Q₁ ⥤ Q₂) (q₂₃ : Q₂ ⥤ Q₃) (q₁₃ : Q₁ ⥤ Q₃)
    (a : s₁₂ ⋙ s₂₃ ≅ s₁₃) (b : t₁₂ ⋙ t₂₃ ≅ t₁₃)
    (ap : p₁₂ ⋙ p₂₃ ≅ p₁₃) (bp : q₁₂ ⋙ q₂₃ ≅ q₁₃)
    (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃)
    (τ₁₂ : V₁ ⋙ q₁₂ ≅ t₁₂ ⋙ V₂) (τ₂₃ : V₂ ⋙ q₂₃ ≅ t₂₃ ⋙ V₃)
    (τ₁₃ : V₁ ⋙ q₁₃ ≅ t₁₃ ⋙ V₃)
    (θ₁₂ : ∀ K, s₁₂.obj (O₁.obj K) ⟶ O₂.obj (p₁₂.obj K))
    (θ₂₃ : ∀ K, s₂₃.obj (O₂.obj K) ⟶ O₃.obj (p₂₃.obj K))
    (θ₁₃ : ∀ K, s₁₃.obj (O₁.obj K) ⟶ O₃.obj (p₁₃.obj K))
    (c₁₂ : ∀ J, t₁₂.obj (F₁.obj J) ⟶ F₂.obj (s₁₂.obj J))
    (c₂₃ : ∀ J, t₂₃.obj (F₂.obj J) ⟶ F₃.obj (s₂₃.obj J))
    (c₁₃ : ∀ J, t₁₃.obj (F₁.obj J) ⟶ F₃.obj (s₁₃.obj J))
    (hc : ∀ {J L} (v : J ⟶ L),
      t₂₃.map (F₂.map v) ≫ c₂₃ L = c₂₃ J ≫ F₃.map (s₂₃.map v))
    (ht : ∀ J, q₂₃.map (τ₁₂.hom.app J) ≫ τ₂₃.hom.app (t₁₂.obj J) ≫
      V₃.map (b.hom.app J) = bp.hom.app (V₁.obj J) ≫ τ₁₃.hom.app J)
    (K : P₁)
    (hθ : s₂₃.map (θ₁₂ K) ≫ θ₂₃ (p₁₂.obj K) ≫ O₃.map (ap.hom.app K) =
      a.hom.app (O₁.obj K) ≫ θ₁₃ K)
    (hordinary : QuotientCocycle s₁₂ s₂₃ s₁₃ t₁₂ t₂₃ t₁₃ a b
      F₁ F₂ F₃ c₁₂ c₂₃ c₁₃ (O₁.obj K)) :
    QuotientCocycle p₁₂ p₂₃ p₁₃ q₁₂ q₂₃ q₁₃ ap bp
      (O₁ ⋙ F₁ ⋙ V₁) (O₂ ⋙ F₂ ⋙ V₂) (O₃ ⋙ F₃ ⋙ V₃)
      (originTransport O₁ O₂ V₁ V₂ s₁₂ t₁₂ p₁₂ q₁₂ F₁ F₂ τ₁₂ θ₁₂ c₁₂)
      (originTransport O₂ O₃ V₂ V₃ s₂₃ t₂₃ p₂₃ q₂₃ F₂ F₃ τ₂₃ θ₂₃ c₂₃)
      (originTransport O₁ O₃ V₁ V₃ s₁₃ t₁₃ p₁₃ q₁₃ F₁ F₃ τ₁₃ θ₁₃ c₁₃) K := by
  have hi :
      t₂₃.map (c₁₂ (O₁.obj K)) ≫ t₂₃.map (F₂.map (θ₁₂ K)) ≫
        c₂₃ (O₂.obj (p₁₂.obj K)) ≫ F₃.map (θ₂₃ (p₁₂.obj K)) ≫
        F₃.map (O₃.map (ap.hom.app K)) =
      b.hom.app (F₁.obj (O₁.obj K)) ≫ c₁₃ (O₁.obj K) ≫ F₃.map (θ₁₃ K) := by
    rw [reassoc_of% (hc (θ₁₂ K))]
    calc
      _ = (t₂₃.map (c₁₂ (O₁.obj K)) ≫ c₂₃ (s₁₂.obj (O₁.obj K)) ≫
          F₃.map (a.hom.app (O₁.obj K))) ≫ F₃.map (θ₁₃ K) := by
        simpa only [Functor.map_comp, Category.assoc] using
          congrArg (fun v ↦ t₂₃.map (c₁₂ (O₁.obj K)) ≫
            c₂₃ (s₁₂.obj (O₁.obj K)) ≫ F₃.map v) hθ
      _ = _ := by rw [hordinary]; simp only [Category.assoc]
  have hi' := congrArg V₃.map hi
  simp only [Functor.map_comp] at hi'
  dsimp only [QuotientCocycle, originTransport, Functor.comp_map, Functor.comp_obj]
  rw [q₂₃.map_comp]
  simp only [Category.assoc]
  have hn := τ₂₃.hom.naturality (c₁₂ (O₁.obj K) ≫ F₂.map (θ₁₂ K))
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]
  simp only [Functor.map_comp, Category.assoc]
  rw [hi', reassoc_of% (ht (F₁.obj (O₁.obj K)))]

private theorem conjugateCocycle
    (p₁₂ : P₁ ⥤ P₂) (p₂₃ : P₂ ⥤ P₃) (p₁₃ : P₁ ⥤ P₃)
    (q₁₂ : Q₁ ⥤ Q₂) (q₂₃ : Q₂ ⥤ Q₃) (q₁₃ : Q₁ ⥤ Q₃)
    (a : p₁₂ ⋙ p₂₃ ≅ p₁₃) (b : q₁₂ ⋙ q₂₃ ≅ q₁₃)
    (F₁ G₁ : P₁ ⥤ Q₁) (F₂ G₂ : P₂ ⥤ Q₂) (F₃ G₃ : P₃ ⥤ Q₃)
    (c₁₂ : ∀ K, q₁₂.obj (F₁.obj K) ⟶ F₂.obj (p₁₂.obj K))
    (c₂₃ : ∀ K, q₂₃.obj (F₂.obj K) ⟶ F₃.obj (p₂₃.obj K))
    (c₁₃ : ∀ K, q₁₃.obj (F₁.obj K) ⟶ F₃.obj (p₁₃.obj K))
    (K : P₁)
    (i₁ : G₁.obj K ⟶ F₁.obj K)
    (e₂ : F₂.obj (p₁₂.obj K) ⟶ G₂.obj (p₁₂.obj K))
    (i₂ : G₂.obj (p₁₂.obj K) ⟶ F₂.obj (p₁₂.obj K))
    (e₃ : F₃.obj (p₂₃.obj (p₁₂.obj K)) ⟶ G₃.obj (p₂₃.obj (p₁₂.obj K)))
    (e₁₃ : F₃.obj (p₁₃.obj K) ⟶ G₃.obj (p₁₃.obj K))
    (hei : e₂ ≫ i₂ = 𝟙 _)
    (he : e₃ ≫ G₃.map (a.hom.app K) = F₃.map (a.hom.app K) ≫ e₁₃)
    (hc : QuotientCocycle p₁₂ p₂₃ p₁₃ q₁₂ q₂₃ q₁₃ a b
      F₁ F₂ F₃ c₁₂ c₂₃ c₁₃ K) :
    q₂₃.map (q₁₂.map i₁ ≫ c₁₂ K ≫ e₂) ≫
      (q₂₃.map i₂ ≫ c₂₃ (p₁₂.obj K) ≫ e₃) ≫ G₃.map (a.hom.app K) =
    b.hom.app (G₁.obj K) ≫ (q₁₃.map i₁ ≫ c₁₃ K ≫ e₁₃) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← q₂₃.map_comp_assoc e₂ i₂, hei, CategoryTheory.Functor.map_id, Category.id_comp, he]
  rw [reassoc_of% hc]
  have hn := b.hom.naturality i₁
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]

private theorem pullbackFromOrigin_cancel
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : proCategory A Y)
    [hc : IsIso ((ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).counit.app K)] :
    pullbackFromOrigin f K ≫ pullbackToOrigin f K = 𝟙 _ := by
  with_unfolding_all
    simp only [pullbackFromOrigin, pullbackToOrigin, originInverse, dif_pos hc, Category.assoc]
    erw [← (proPullback A f).map_comp_assoc, IsIso.hom_inv_id]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
    all_goals rfl

private theorem pullbackFromOrigin_natural
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : proCategory A Y} (v : K ⟶ L) :
    pullbackFromOrigin f K ≫ (proPullback A f).map v =
      (comparison A X).map ((ordinaryFinitePullback A f).map ((origin A Y).map v)) ≫
        pullbackFromOrigin f L := by
  with_unfolding_all
    have hn := (sitePullbackIso A f).inv.naturality ((origin A Y).map v)
    have he := (ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).counit.naturality v
    dsimp only [Functor.comp_map, Functor.id_map] at hn he
    simp only [pullbackFromOrigin, Category.assoc]
    erw [← (proPullback A f).map_comp, ← he, (proPullback A f).map_comp]
    exact ((reassoc_of% hn) _).symm

private theorem sourceFromOrigin_cancel
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (L : DerivedCategoryModule A X)
    (K : proCategory A Y)
    [hc : IsIso ((ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).counit.app K)] :
    sourceFromOrigin A f L K ≫ sourceToOrigin A f L K = 𝟙 _ := by
  with_unfolding_all
    simp only [sourceFromOrigin, sourceToOrigin, originInverse, dif_pos hc, Category.assoc]
    erw [← (proSource A f L).map_comp_assoc, IsIso.hom_inv_id]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id]

private theorem sourceFromOrigin_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : DerivedCategoryModule A X)
    {K L : proCategory A Y} (v : K ⟶ L) :
    sourceFromOrigin A f M K ≫ (proSource A f M).map v =
      (comparison A X).map ((puritySource A f M).map ((origin A Y).map v)) ≫
        sourceFromOrigin A f M L := by
  with_unfolding_all
    have hn := (sourceNatIso A f M).hom.naturality ((origin A Y).map v)
    have he := (ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).counit.naturality v
    have hq (J : DerivedCategoryModule A Y) :
        (sourceNatIso A f M).hom.app J = (sourceAtOriginIso A f M J).hom :=
      congrArg Iso.hom (sourceNatIso_app A f M J)
    erw [hq, hq] at hn
    dsimp only [Functor.comp_map, Functor.id_map] at hn he
    simp only [sourceFromOrigin, Category.assoc]
    erw [← (proSource A f M).map_comp, ← he, (proSource A f M).map_comp]
    exact ((reassoc_of% hn) _).symm

private theorem ordinaryLambda_natural
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N M : ℕ} {hA : (N : A) = 0} {hB : (M : B) = 0}
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (e : CoefficientLineComparison φ N M hA hB X)
    {K L : DerivedCategoryModule A Y} (v : K ⟶ L) :
    (ordinaryScalar φ X).map ((puritySource A f (line A N hA X d)).map v) ≫
      (pullbackTwistComparison f d e L).hom =
    (pullbackTwistComparison f d e K).hom ≫
      (puritySource B f (line B M hB X d)).map ((ordinaryScalar φ Y).map v) := by
  with_unfolding_all
    have ht := (ExceptionalCoefficients.tensorIso φ X).hom.naturality
      (show ((ordinaryFinitePullback A f).obj K, line A N hA X d) ⟶
        ((ordinaryFinitePullback A f).obj L, line A N hA X d) from
          ((ordinaryFinitePullback A f).map v, 𝟙 _))
    have hp := (scalarPullbackIso φ f).inv.naturality v
    have he := ((derivedTensor (ModuleCat B) X).map
      ((ordinaryFinitePullback B f).map ((ordinaryScalar φ Y).map v))).naturality
        (e.tensorPower d).hom
    dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj] at ht hp
    simp only [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id,
      Category.comp_id] at ht
    simp only [pullbackTwistComparison, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Iso.app_inv, Iso.symm_hom, Category.assoc]
    change _ ≫ _ ≫ _ ≫ _ = _
    erw [reassoc_of% ht]
    have hp' := congrArg (fun t ↦ ((derivedTensor (ModuleCat B) X).map t).app
      ((ordinaryScalar φ X).obj (line A N hA X d))) hp
    simp only [Functor.map_comp, NatTrans.comp_app] at hp'
    erw [reassoc_of% hp', ← he]
    all_goals rfl

end CategoricalTransport

private theorem quotient_comp (ell : ℕ) {r m n : ℕ} (hmr : m ≤ r) (hnm : n ≤ m) :
    FiniteReduction.quotient.{u} ell (hnm.trans hmr) =
      (FiniteReduction.quotient ell hnm).comp (FiniteReduction.quotient ell hmr) :=
  RingHom.ext (fun x ↦
    congrArg (fun y : ZMod (ell ^ n) ↦ (⟨⟨y⟩⟩ : coefficient.{u} ell n))
      (DFunLike.congr_fun
        (Subsingleton.elim
          (ZMod.castHom (pow_dvd_pow ell (hnm.trans hmr)) (ZMod (ell ^ n)))
          ((ZMod.castHom (pow_dvd_pow ell hnm) (ZMod (ell ^ n))).comp
            (ZMod.castHom (pow_dvd_pow ell hmr) (ZMod (ell ^ m))))) x.down.down))

private def transportedCoefficient
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T U : Scheme.{u})
    (F : DerivedCategoryModule A T ⥤ DerivedCategoryModule A U)
    (G : DerivedCategoryModule B T ⥤ DerivedCategoryModule B U)
    (c : ∀ J, (ordinaryScalar φ U).obj (F.obj J) ⟶
      G.obj ((ordinaryScalar φ T).obj J)) (K : proCategory A T) :
    (proScalar φ U).obj ((origin A T ⋙ F ⋙ comparison A U).obj K) ⟶
      (origin B T ⋙ G ⋙ comparison B U).obj ((proScalar φ T).obj K) :=
  (ProEtale.pbcComparisonReduction U φ).hom.app (F.obj ((origin A T).obj K)) ≫
    (comparison B U).map (c ((origin A T).obj K) ≫
      G.map (originReductionMap φ T K))

private theorem liftedQuotientCocycle
    (ell : ℕ) {r m n : ℕ} (hmr : m ≤ r) (hnm : n ≤ m) (T U : Scheme.{u})
    (F₁ : DerivedCategoryModule (coefficient ell r) T ⥤
      DerivedCategoryModule (coefficient ell r) U)
    (F₂ : DerivedCategoryModule (coefficient ell m) T ⥤
      DerivedCategoryModule (coefficient ell m) U)
    (F₃ : DerivedCategoryModule (coefficient ell n) T ⥤
      DerivedCategoryModule (coefficient ell n) U)
    (c₁₂ : ∀ J, (ordinaryScalar (FiniteReduction.quotient ell hmr) U).obj (F₁.obj J) ⟶
      F₂.obj ((ordinaryScalar (FiniteReduction.quotient ell hmr) T).obj J))
    (c₂₃ : ∀ J, (ordinaryScalar (FiniteReduction.quotient ell hnm) U).obj (F₂.obj J) ⟶
      F₃.obj ((ordinaryScalar (FiniteReduction.quotient ell hnm) T).obj J))
    (c₁₃ : ∀ J, (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) U).obj
      (F₁.obj J) ⟶
      F₃.obj ((ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) T).obj J))
    (hc : ∀ {J L} (v : J ⟶ L),
      (ordinaryScalar (FiniteReduction.quotient ell hnm) U).map (F₂.map v) ≫ c₂₃ L =
      c₂₃ J ≫ F₃.map ((ordinaryScalar (FiniteReduction.quotient ell hnm) T).map v))
    (K : proCategory (coefficient ell r) T)
    (hordinary : QuotientCocycle
      (ordinaryScalar (FiniteReduction.quotient ell hmr) T)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) T)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) T)
      (ordinaryScalar (FiniteReduction.quotient ell hmr) U)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) U)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) U)
      (ordinaryAssociator T ell hmr hnm) (ordinaryAssociator U ell hmr hnm)
      F₁ F₂ F₃ c₁₂ c₂₃ c₁₃ ((origin (coefficient ell r) T).obj K)) :
    QuotientCocycle
      (proScalar (FiniteReduction.quotient ell hmr) T)
      (proScalar (FiniteReduction.quotient ell hnm) T)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) T)
      (proScalar (FiniteReduction.quotient ell hmr) U)
      (proScalar (FiniteReduction.quotient ell hnm) U)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) U)
      (proAssociatorOf T _ _ _ (quotient_comp ell hmr hnm))
      (proAssociatorOf U _ _ _ (quotient_comp ell hmr hnm))
      (origin (coefficient ell r) T ⋙ F₁ ⋙ comparison (coefficient ell r) U)
      (origin (coefficient ell m) T ⋙ F₂ ⋙ comparison (coefficient ell m) U)
      (origin (coefficient ell n) T ⋙ F₃ ⋙ comparison (coefficient ell n) U)
      (transportedCoefficient (FiniteReduction.quotient ell hmr) T U F₁ F₂ c₁₂)
      (transportedCoefficient (FiniteReduction.quotient ell hnm) T U F₂ F₃ c₂₃)
      (transportedCoefficient (FiniteReduction.quotient ell (hnm.trans hmr))
        T U F₁ F₃ c₁₃) K := by
  with_unfolding_all
    exact originTransport_cocycle
      (origin (coefficient ell r) T) (origin (coefficient ell m) T)
      (origin (coefficient ell n) T)
      (comparison (coefficient ell r) U) (comparison (coefficient ell m) U)
      (comparison (coefficient ell n) U)
      _ _ _ _ _ _ _ _ _ _ _ _
      (ordinaryAssociator T ell hmr hnm) (ordinaryAssociator U ell hmr hnm)
      _ _ F₁ F₂ F₃
      (ProEtale.pbcComparisonReduction U _) (ProEtale.pbcComparisonReduction U _)
      (ProEtale.pbcComparisonReduction U _)
      (originReductionMap _ T) (originReductionMap _ T) (originReductionMap _ T)
      c₁₂ c₂₃ c₁₃ hc
      (siteScalarComp U _ _ _ (quotient_comp ell hmr hnm)) K
      (originReductionComp T _ _ _ (quotient_comp ell hmr hnm) K) hordinary

private theorem exceptionalMap_natural
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f]
    {K L : DerivedCategoryModule A Y} (v : K ⟶ L) :
    (ordinaryScalar φ X).map ((rightDerivedUpperShriek A f).map v) ≫
      ExceptionalCoefficients.mateMap φ f L =
    ExceptionalCoefficients.mateMap φ f K ≫
      (rightDerivedUpperShriek B f).map ((ordinaryScalar φ Y).map v) := by
  with_unfolding_all
    have h := (mateEquiv
      (rightDerivedUpperShriekAdjunction A f)
      (rightDerivedUpperShriekAdjunction B f)
      (TwoSquare.mk _ _ _ _ (ExceptionalCoefficients.compactSupportIso φ
        (HasCompactification.compactification f)).inv)).naturality v
    simp only [← ExceptionalCoefficients.mateMap_eq, Functor.comp_map] at h
    exact h

private def compactFromOrigin
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (K : proCategory A X) :
    (origin A X ⋙ rightDerivedLowerShriek (ModuleCat A) f ⋙ comparison A Y).obj K ⟶
      (proCompact A f).obj K :=
  compactSiteInverse A f ((origin A X).obj K) ≫
    (proCompact A f).map
      ((ProEtale.derivedComparisonAdjunction (ModuleCat A) X).counit.app K)

private def compactToOrigin
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (K : proCategory A X) :
    (proCompact A f).obj K ⟶
      (origin A X ⋙ rightDerivedLowerShriek (ModuleCat A) f ⋙ comparison A Y).obj K :=
  (proCompact A f).map (originInverse A X K) ≫
    compactSiteMap A f ((origin A X).obj K)

private theorem compactFromOrigin_cancel
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Y) [HasCompactification f] (K : proCategory A X) (hK : IsCtf A X K) :
    compactFromOrigin A f K ≫ compactToOrigin A f K = 𝟙 _ := by
  with_unfolding_all
    have hc := intrinsicOriginCounit A X K hK
    have hp := (actualOriginCtf A X K hK).1.1.1
    simp only [compactFromOrigin, compactToOrigin, originInverse, dif_pos hc,
      Category.assoc]
    erw [← (proCompact A f).map_comp_assoc, IsIso.hom_inv_id]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [compactSiteMap, compactSiteInverse, dif_pos hp, Iso.inv_hom_id_app]
    all_goals rfl

private theorem compactFromOrigin_natural
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Y) [HasCompactification f]
    {K L : proCategory A X} (hK : IsCtf A X K) (hL : IsCtf A X L) (v : K ⟶ L) :
    compactFromOrigin A f K ≫ (proCompact A f).map v =
      (comparison A Y).map ((rightDerivedLowerShriek (ModuleCat A) f).map
        ((origin A X).map v)) ≫ compactFromOrigin A f L := by
  with_unfolding_all
    have hn := inverseSiteNaturality A f (actualOriginCtf A X K hK).1.1.1
      (actualOriginCtf A X L hL).1.1.1 ((origin A X).map v)
    have he := (ProEtale.derivedComparisonAdjunction (ModuleCat A) X).counit.naturality v
    dsimp only [Functor.comp_map, Functor.id_map] at he
    simp only [compactFromOrigin, Category.assoc]
    erw [← (proCompact A f).map_comp, ← he, (proCompact A f).map_comp]
    exact ((reassoc_of% hn) _).symm

private theorem compactCoefficient_transport
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Y) [HasCompactification f] (K : proCategory A X) (hK : IsCtf A X K)
    (hBK : IsCtf B X ((proScalar φ X).obj K)) :
    proCompactCoefficientMap φ f K =
      (proScalar φ Y).map (compactToOrigin A f K) ≫
        transportedCoefficient φ X Y
          (rightDerivedLowerShriek (ModuleCat A) f) (rightDerivedLowerShriek (ModuleCat B) f)
          (ExceptionalCoefficients.compactSupportMap φ (HasCompactification.compactification f))
          K ≫ compactFromOrigin B f ((proScalar φ X).obj K) := by
  with_unfolding_all
    have hO := actualOriginCtf A X K hK
    have hn := inverseSiteNaturality B f
      (ExceptionalCoefficients.scalar_extension_plus_of_finiteTor φ X _ hO.2)
      (actualOriginCtf B X _ hBK).1.1.1 (originReductionMap φ X K)
    have hn' := congrArg (fun t ↦ t ≫ (proCompact B f).map
      ((ProEtale.derivedComparisonAdjunction (ModuleCat B) X).counit.app
        ((proScalar φ X).obj K))) hn
    simp only [Category.assoc, ← Functor.map_comp] at hn'
    erw [originReductionCounit φ X K] at hn'
    simp only [proCompactCoefficientMap, compactToOrigin, compactFromOrigin,
      transportedCoefficient, Functor.map_comp, Category.assoc]
    simp only [Functor.map_comp] at hn'
    erw [hn']
    all_goals rfl

-- Preserve the fixed statement's unused hY and exceptional-hypothesis hn binders.

/-- Ordinary cocycles transport through the canonical site and origin comparisons.
Source: blueprint sk-lem-sp-reduction-compatibilities.proof.md, part (2), together
with the site-comparison transport in sk-thm-purity-transport, Step 1.
(blueprint: lem-pur-finite-smooth-pro-quotient-transport).

Proof: first take scalar-adjunction transposes of the canonical site/scalar
comparison for direct and successive quotients. The restriction/comparison
square composes on underlying sections, so mate pasting proves its scalar
associativity square with the displayed proAssociator and ordinaryAssociator.
Taking the site-comparison adjunction transpose of originReductionMap gives
its associative square: substitute its definition, use naturality of the origin
counit, and use the site/scalar square just proved. For the twist, expand
proTwistMap, move its first ordinary twist map through the second site/scalar
comparison by naturality, and apply htwist and that square.
For pullback, expand proPullbackMap. Intrinsic Ctf objects have ordinary bounded
constructible finite-Tor origins and invertible actual comparison counits by
finite-coefficient site comparison and Tor-amplitude comparison. Scalar
extension preserves this domain. Thus pullbackFromOrigin followed by
pullbackToOrigin cancels at the intermediate level. Naturality of the two site
pullback comparisons, the origin square, and hpull identify the remaining paths.
The same calculation for proLambda uses the source comparison instead and
hsource. For proCoefficientMap no inverse origin counit is needed: expand the
two maps, use naturality of the exceptional mate, the origin square and
hexception at the ordinary origin. The latter has its required domain by the
same intrinsic comparison theorem. Finally expand proCompactCoefficientMap.
Naturality moves the middle ordinary coefficient map past the site comparisons;
comparison counits cancel on Ctf. The ordinary and scalar-extended origins have
bounded-below compact support, so the actual open/proper site comparisons are
invertible there. Cancel compactSiteInverse against compactSiteMap, apply
hcompact, then use the site/scalar associativity square. Reassociate to obtain
the displayed compact-support equation. These are equalities for the fixed
maps, including equal quotient indices, not choices of new comparisons. -/
theorem finiteSmoothProQuotientTransport
    (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (hY : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y))
    (twists : ∀ (r m : ℕ) (_hm : 1 ≤ m) (hmr : m ≤ r),
      CoefficientLineComparison (FiniteReduction.quotient ell hmr) (ell ^ r) (ell ^ m)
        (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) X)
    (hcompact : ExceptionalCoefficients.CompactSupportCocycle ell f)
    (htwist : (∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r),
    (ordinaryScalar (FiniteReduction.quotient ell hnm) X).map
        ((twists r m (hn.trans hnm) hmr).tensorPower d).hom ≫
      ((twists m n hn hnm).tensorPower d).hom =
    (ordinaryAssociator X ell hmr hnm).hom.app
        (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) X d) ≫
      ((twists r n hn (hnm.trans hmr)).tensorPower d).hom))
    (hpull : (∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : DerivedCategoryModule (coefficient ell r) Y),
    QuotientCocycle
      (ordinaryScalar (FiniteReduction.quotient ell hmr) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) Y)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hmr) X)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) X)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (ordinaryAssociator Y ell hmr hnm)
      (ordinaryAssociator X ell hmr hnm)
      ((ordinaryFinitePullback (coefficient ell r) f))
      ((ordinaryFinitePullback (coefficient ell m) f))
      ((ordinaryFinitePullback (coefficient ell n) f))
      (ordinaryPullbackMap (FiniteReduction.quotient ell hmr) f)
      (ordinaryPullbackMap (FiniteReduction.quotient ell hnm) f)
      (ordinaryPullbackMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K))
    (hsource : (∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : DerivedCategoryModule (coefficient ell r) Y),
    DerivedCategory.boundedConstructibleFiniteTor (coefficient ell r) Y K →
    QuotientCocycle
      (ordinaryScalar (FiniteReduction.quotient ell hmr) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) Y)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hmr) X)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) X)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (ordinaryAssociator Y ell hmr hnm)
      (ordinaryAssociator X ell hmr hnm)
      (finiteSource ell r f d)
      (finiteSource ell m f d)
      (finiteSource ell n f d)
      (finiteLambda ell hmr f d (twists r m (hn.trans hnm) hmr))
      (finiteLambda ell hnm f d (twists m n hn hnm))
      (finiteLambda ell (hnm.trans hmr) f d (twists r n hn (hnm.trans hmr))) K))
    (hexception : (∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : DerivedCategoryModule (coefficient ell r) Y),
    DerivedCategory.boundedConstructibleFiniteTor (coefficient ell r) Y K →
    QuotientCocycle
      (ordinaryScalar (FiniteReduction.quotient ell hmr) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) Y)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (ordinaryScalar (FiniteReduction.quotient ell hmr) X)
      (ordinaryScalar (FiniteReduction.quotient ell hnm) X)
      (ordinaryScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (ordinaryAssociator Y ell hmr hnm)
      (ordinaryAssociator X ell hmr hnm)
      (rightDerivedUpperShriek (coefficient ell r) f)
      (rightDerivedUpperShriek (coefficient ell m) f)
      (rightDerivedUpperShriek (coefficient ell n) f)
      (ExceptionalCoefficients.mateMap (FiniteReduction.quotient ell hmr) f)
      (ExceptionalCoefficients.mateMap (FiniteReduction.quotient ell hnm) f)
      (ExceptionalCoefficients.mateMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K)) :
  let proAssociator (T : Scheme.{u}) (ell : ℕ) {r m n : ℕ}
      (hmr : m ≤ r) (hnm : n ≤ m) :
      proScalar (FiniteReduction.quotient ell hmr) T ⋙
        proScalar (FiniteReduction.quotient ell hnm) T ≅
          proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) T :=
    @ProEtale.pbcFixedScalarExtensionComp.{u} T.ProEt inferInstance
      (essentiallySmallSelf.{0, u, u + 1} T.ProEt) (Scheme.ProEt.topology T)
      (coefficient ell r) (coefficient ell m) (coefficient ell n)
      inferInstance inferInstance inferInstance
      (FiniteReduction.quotient.{u} ell hmr) (FiniteReduction.quotient ell hnm)
      (FiniteReduction.quotient ell (hnm.trans hmr))
      (RingHom.ext (fun x ↦
        congrArg (fun y : ZMod (ell ^ n) ↦ (⟨⟨y⟩⟩ : coefficient.{u} ell n))
          (DFunLike.congr_fun
            (Subsingleton.elim
              (ZMod.castHom (pow_dvd_pow ell (hnm.trans hmr)) (ZMod (ell ^ n)))
              ((ZMod.castHom (pow_dvd_pow ell hnm) (ZMod (ell ^ n))).comp
                (ZMod.castHom (pow_dvd_pow ell hmr) (ZMod (ell ^ m))))) x.down.down)));
  (∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r),
    (proScalar (FiniteReduction.quotient ell hnm) X).map
        (proTwistMap d (twists r m (hn.trans hnm) hmr)) ≫
      proTwistMap d (twists m n hn hnm) =
    (proAssociator X ell hmr hnm).hom.app
        ((comparison (coefficient ell r) X).obj
          (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) X d)) ≫
      proTwistMap d (twists r n hn (hnm.trans hmr))) ∧
  (∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : proCategory (coefficient ell r) Y),
    IsCtf (coefficient ell r) Y K →
    QuotientCocycle
      (proScalar (FiniteReduction.quotient ell hmr) Y)
      (proScalar (FiniteReduction.quotient ell hnm) Y)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (proScalar (FiniteReduction.quotient ell hmr) X)
      (proScalar (FiniteReduction.quotient ell hnm) X)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (proAssociator Y ell hmr hnm)
      (proAssociator X ell hmr hnm)
      ((proPullback (coefficient ell r) f))
      ((proPullback (coefficient ell m) f))
      ((proPullback (coefficient ell n) f))
      (proPullbackMap (FiniteReduction.quotient ell hmr) f)
      (proPullbackMap (FiniteReduction.quotient ell hnm) f)
      (proPullbackMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K) ∧
  (∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : proCategory (coefficient ell r) X),
    IsCtf (coefficient ell r) X K →
    QuotientCocycle
      (proScalar (FiniteReduction.quotient ell hmr) X)
      (proScalar (FiniteReduction.quotient ell hnm) X)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (proScalar (FiniteReduction.quotient ell hmr) Y)
      (proScalar (FiniteReduction.quotient ell hnm) Y)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (proAssociator X ell hmr hnm)
      (proAssociator Y ell hmr hnm)
      (proCompact (coefficient ell r) f)
      (proCompact (coefficient ell m) f)
      (proCompact (coefficient ell n) f)
      (proCompactCoefficientMap (FiniteReduction.quotient ell hmr) f)
      (proCompactCoefficientMap (FiniteReduction.quotient ell hnm) f)
      (proCompactCoefficientMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K) ∧
  (∀ (r m n : ℕ) (_hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : proCategory (coefficient ell r) Y),
    IsCtf (coefficient ell r) Y K →
    QuotientCocycle
      (proScalar (FiniteReduction.quotient ell hmr) Y)
      (proScalar (FiniteReduction.quotient ell hnm) Y)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (proScalar (FiniteReduction.quotient ell hmr) X)
      (proScalar (FiniteReduction.quotient ell hnm) X)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (proAssociator Y ell hmr hnm)
      (proAssociator X ell hmr hnm)
      (exceptional (coefficient ell r) f)
      (exceptional (coefficient ell m) f)
      (exceptional (coefficient ell n) f)
      (proCoefficientMap (FiniteReduction.quotient ell hmr) f)
      (proCoefficientMap (FiniteReduction.quotient ell hnm) f)
      (proCoefficientMap (FiniteReduction.quotient ell (hnm.trans hmr)) f) K) ∧
  (∀ (r m n : ℕ) (hn : 1 ≤ n) (hnm : n ≤ m) (hmr : m ≤ r)
    (K : proCategory (coefficient ell r) Y),
    IsCtf (coefficient ell r) Y K →
    QuotientCocycle
      (proScalar (FiniteReduction.quotient ell hmr) Y)
      (proScalar (FiniteReduction.quotient ell hnm) Y)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) Y)
      (proScalar (FiniteReduction.quotient ell hmr) X)
      (proScalar (FiniteReduction.quotient ell hnm) X)
      (proScalar (FiniteReduction.quotient ell (hnm.trans hmr)) X)
      (proAssociator Y ell hmr hnm)
      (proAssociator X ell hmr hnm)
      (finiteProSource ell r f d)
      (finiteProSource ell m f d)
      (finiteProSource ell n f d)
      (finiteProLambda ell hmr f d (twists r m (hn.trans hnm) hmr))
      (finiteProLambda ell hnm f d (twists m n hn hnm))
      (finiteProLambda ell (hnm.trans hmr) f d (twists r n hn (hnm.trans hmr))) K) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r m n hn hnm hmr
    with_unfolding_all
      have ht := htwist r m n hn hnm hmr
      have hs := siteScalarComp X _ _ _ (quotient_comp ell hmr hnm)
        (line (coefficient ell r) (ell ^ r) (CharP.cast_eq_zero _ _) X d)
      have hn' := (ProEtale.pbcComparisonReduction X
        (FiniteReduction.quotient ell hnm)).hom.naturality
          ((twists r m (hn.trans hnm) hmr).tensorPower d).hom
      dsimp only [Functor.comp_map] at hn'
      dsimp only [proScalar, ordinaryScalar, scalarExtension, comparison,
        Functor.comp_obj] at hn' hs ht ⊢
      simp only [proTwistMap, Functor.map_comp, Category.assoc]
      erw [reassoc_of% hn', ← (comparison (coefficient ell n) X).map_comp, ht]
      erw [(comparison (coefficient ell n) X).map_comp]
      exact (reassoc_of% hs) _
  · intro r m n hn hnm hmr K hK
    with_unfolding_all
      let φ := FiniteReduction.quotient.{u} ell hmr
      let ψ := FiniteReduction.quotient.{u} ell hnm
      let χ := FiniteReduction.quotient.{u} ell (hnm.trans hmr)
      let A := coefficient.{u} ell r
      let B := coefficient.{u} ell m
      let C := coefficient.{u} ell n
      have hc {J L : DerivedCategoryModule B Y} (v : J ⟶ L) :
          (ordinaryScalar ψ X).map ((ordinaryFinitePullback B f).map v) ≫
            ordinaryPullbackMap ψ f L =
          ordinaryPullbackMap ψ f J ≫
            (ordinaryFinitePullback C f).map ((ordinaryScalar ψ Y).map v) :=
        (scalarPullbackIso ψ f).inv.naturality v
      have hl := liftedQuotientCocycle ell hmr hnm Y X
        (ordinaryFinitePullback A f) (ordinaryFinitePullback B f)
        (ordinaryFinitePullback C f)
        (ordinaryPullbackMap φ f) (ordinaryPullbackMap ψ f) (ordinaryPullbackMap χ f)
        hc K (hpull r m n hn hnm hmr ((origin A Y).obj K))
      have := intrinsicOriginCounit B Y ((proScalar φ Y).obj K)
        (quotientIntrinsicCtf ell r m (hn.trans hnm) hmr Y K hK)
      have he := pullbackFromOrigin_cancel B f ((proScalar φ Y).obj K)
      have hh := pullbackFromOrigin_natural C f
        ((proAssociatorOf Y φ ψ χ (quotient_comp ell hmr hnm)).hom.app K)
      have h := conjugateCocycle
        (proScalar φ Y) (proScalar ψ Y) (proScalar χ Y)
        (proScalar φ X) (proScalar ψ X) (proScalar χ X)
        (proAssociatorOf Y φ ψ χ (quotient_comp ell hmr hnm))
        (proAssociatorOf X φ ψ χ (quotient_comp ell hmr hnm))
        _ (proPullback A f) _ (proPullback B f) _ (proPullback C f)
        _ _ _ K (pullbackToOrigin f K) (pullbackFromOrigin f ((proScalar φ Y).obj K))
        (pullbackToOrigin f ((proScalar φ Y).obj K)) _ _ he hh hl
      simpa only [QuotientCocycle, proPullbackMap, transportedCoefficient,
        ordinaryPullbackMap, proAssociatorOf, Functor.comp_obj, Category.assoc] using h
  · intro r m n hn hnm hmr K hK
    with_unfolding_all
      let φ := FiniteReduction.quotient.{u} ell hmr
      let ψ := FiniteReduction.quotient.{u} ell hnm
      let χ := FiniteReduction.quotient.{u} ell (hnm.trans hmr)
      let A := coefficient.{u} ell r
      let B := coefficient.{u} ell m
      let C := coefficient.{u} ell n
      have hc {J L : DerivedCategoryModule B X} (v : J ⟶ L) :
          (ordinaryScalar ψ Y).map ((rightDerivedLowerShriek (ModuleCat B) f).map v) ≫
            ExceptionalCoefficients.compactSupportMap ψ
              (HasCompactification.compactification f) L =
          ExceptionalCoefficients.compactSupportMap ψ
              (HasCompactification.compactification f) J ≫
            (rightDerivedLowerShriek (ModuleCat C) f).map ((ordinaryScalar ψ X).map v) :=
        compactScalarMap_naturality ψ (HasCompactification.compactification f) v
      have hl := liftedQuotientCocycle ell hmr hnm X Y
        (rightDerivedLowerShriek (ModuleCat A) f) (rightDerivedLowerShriek (ModuleCat B) f)
        (rightDerivedLowerShriek (ModuleCat C) f)
        (ExceptionalCoefficients.compactSupportMap φ (HasCompactification.compactification f))
        (ExceptionalCoefficients.compactSupportMap ψ (HasCompactification.compactification f))
        (ExceptionalCoefficients.compactSupportMap χ (HasCompactification.compactification f))
        hc K (hcompact r m n hmr hnm hn ((origin A X).obj K)
          (actualOriginCtf A X K hK)).symm
      have hmid := quotientIntrinsicCtf ell r m (hn.trans hnm) hmr X K hK
      have hlast := quotientIntrinsicCtf ell m n hn hnm X _ hmid
      have hdir := quotientIntrinsicCtf ell r n hn (hnm.trans hmr) X K hK
      have hh := compactFromOrigin_natural C f hlast hdir
        ((proAssociatorOf X φ ψ χ (quotient_comp ell hmr hnm)).hom.app K)
      have h := conjugateCocycle
        (proScalar φ X) (proScalar ψ X) (proScalar χ X)
        (proScalar φ Y) (proScalar ψ Y) (proScalar χ Y)
        (proAssociatorOf X φ ψ χ (quotient_comp ell hmr hnm))
        (proAssociatorOf Y φ ψ χ (quotient_comp ell hmr hnm))
        _ (proCompact A f) _ (proCompact B f) _ (proCompact C f)
        _ _ _ K (compactToOrigin A f K) _ (compactToOrigin B f ((proScalar φ X).obj K))
        _ _ (compactFromOrigin_cancel B f _ hmid) hh hl
      erw [← compactCoefficient_transport φ f K hK hmid,
        ← compactCoefficient_transport ψ f _ hmid hlast,
        ← compactCoefficient_transport χ f K hK hdir] at h
      exact h
  · intro r m n hn hnm hmr K hK
    with_unfolding_all
      exact liftedQuotientCocycle ell hmr hnm Y X
        (rightDerivedUpperShriek (coefficient ell r) f)
        (rightDerivedUpperShriek (coefficient ell m) f)
        (rightDerivedUpperShriek (coefficient ell n) f)
        (ExceptionalCoefficients.mateMap (FiniteReduction.quotient ell hmr) f)
        (ExceptionalCoefficients.mateMap (FiniteReduction.quotient ell hnm) f)
        (ExceptionalCoefficients.mateMap (FiniteReduction.quotient ell (hnm.trans hmr)) f)
        (fun v ↦ exceptionalMap_natural _ f v) K
        (hexception r m n hn hnm hmr _ (actualOriginCtf _ Y K hK))
  · intro r m n hn hnm hmr K hK
    with_unfolding_all
      let φ := FiniteReduction.quotient.{u} ell hmr
      let ψ := FiniteReduction.quotient.{u} ell hnm
      let χ := FiniteReduction.quotient.{u} ell (hnm.trans hmr)
      let A := coefficient.{u} ell r
      let B := coefficient.{u} ell m
      let C := coefficient.{u} ell n
      let LA := line A (ell ^ r) (CharP.cast_eq_zero _ _) X d
      let LB := line B (ell ^ m) (CharP.cast_eq_zero _ _) X d
      let LC := line C (ell ^ n) (CharP.cast_eq_zero _ _) X d
      have hl := liftedQuotientCocycle ell hmr hnm Y X
        (finiteSource ell r f d) (finiteSource ell m f d) (finiteSource ell n f d)
        (finiteLambda ell hmr f d (twists r m (hn.trans hnm) hmr))
        (finiteLambda ell hnm f d (twists m n hn hnm))
        (finiteLambda ell (hnm.trans hmr) f d (twists r n hn (hnm.trans hmr)))
        (fun v ↦ ordinaryLambda_natural f d (twists m n hn hnm) v) K
        (hsource r m n hn hnm hmr _ (actualOriginCtf A Y K hK))
      have := intrinsicOriginCounit B Y ((proScalar φ Y).obj K)
        (quotientIntrinsicCtf ell r m (hn.trans hnm) hmr Y K hK)
      have he := sourceFromOrigin_cancel B f LB ((proScalar φ Y).obj K)
      have hh := sourceFromOrigin_natural C f LC
        ((proAssociatorOf Y φ ψ χ (quotient_comp ell hmr hnm)).hom.app K)
      have h := conjugateCocycle
        (proScalar φ Y) (proScalar ψ Y) (proScalar χ Y)
        (proScalar φ X) (proScalar ψ X) (proScalar χ X)
        (proAssociatorOf Y φ ψ χ (quotient_comp ell hmr hnm))
        (proAssociatorOf X φ ψ χ (quotient_comp ell hmr hnm))
        (origin A Y ⋙ finiteSource ell r f d ⋙ comparison A X) (finiteProSource ell r f d)
        (origin B Y ⋙ finiteSource ell m f d ⋙ comparison B X) (finiteProSource ell m f d)
        (origin C Y ⋙ finiteSource ell n f d ⋙ comparison C X) (finiteProSource ell n f d)
        _ _ _ K
        (sourceToOrigin A f LA K) (sourceFromOrigin B f LB ((proScalar φ Y).obj K))
        (sourceToOrigin B f LB ((proScalar φ Y).obj K)) _ _ he hh hl
      simpa only [QuotientCocycle, finiteProLambda, proLambda, transportedCoefficient,
        finiteLambda, finiteSource, proAssociatorOf, Functor.comp_obj, Category.assoc] using h

set_option linter.unusedVariables false in
end AlgebraicGeometry.Etale.FiniteSmoothPurity
