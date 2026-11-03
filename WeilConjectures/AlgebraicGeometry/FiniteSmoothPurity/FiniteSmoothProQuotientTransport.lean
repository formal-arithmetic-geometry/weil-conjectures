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

/-! # FiniteSmoothProQuotientTransport

A step of finite smooth quotient coherence. -/

@[expose] public noncomputable section
-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

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

end AlgebraicGeometry.Etale.FiniteSmoothPurity
