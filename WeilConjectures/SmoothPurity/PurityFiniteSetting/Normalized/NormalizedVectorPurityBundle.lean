/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Vector.VectorPurityNormalization
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationMate
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # Normalized vector-bundle purity family. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry.Etale

/-- Braiding conjugates the coefficient-first mate to the twist-first mate. -/
private theorem swap_mate_isIso
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    (L : C ⥤ D) (R P : D ⥤ C) (adj : L ⊣ R)
    (W : C) (t : L.obj W ⟶ 𝟙_ D) (K : D)
    (π : L.obj W ⊗ K ⟶ L.obj (W ⊗ P.obj K)) [IsIso π]
    (h : IsIso (adj.homEquiv _ K
      (inv ((β_ K (L.obj W)).hom ≫ π ≫ L.map (β_ W (P.obj K)).hom) ≫
        (K ◁ t) ≫ (ρ_ K).hom))) :
    IsIso (adj.homEquiv _ K (inv π ≫ (t ▷ K) ≫ (λ_ K).hom)) := by
  have he : adj.homEquiv _ K (inv π ≫ (t ▷ K) ≫ (λ_ K).hom) =
      (β_ W (P.obj K)).hom ≫ adj.homEquiv _ K
        (inv ((β_ K (L.obj W)).hom ≫ π ≫ L.map (β_ W (P.obj K)).hom) ≫
          (K ◁ t) ≫ (ρ_ K).hom) := by
    rw [← adj.homEquiv_naturality_left]
    apply congrArg (adj.homEquiv _ K)
    simp only [IsIso.inv_comp, Category.assoc, IsIso.hom_inv_id_assoc]
    simp only [IsIso.Iso.inv_hom]
    rw [← BraidedCategory.braiding_inv_naturality_left_assoc]
    simp
  rw [he]
  exact IsIso.comp_isIso' inferInstance h

/-- Invertible trace mates determine the normalized family and its unit orientation. -/
private theorem normalized_of_iso_mates
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D]
    (L : C ⥤ D) (R P : D ⥤ C) (adj : L ⊣ R)
    (W : C) (t : L.obj W ⟶ 𝟙_ D)
    (π : tensorLeft (L.obj W) ⟶ (P ⋙ tensorLeft W) ⋙ L)
    [IsIso π]
    (hiso : ∀ K, IsIso (adj.homEquiv _ K
      (inv (π.app K) ≫ (t ▷ K) ≫ (λ_ K).hom)))
    (e : (P ⋙ tensorLeft W).obj (𝟙_ D) ≅ W)
    (hu : π.app (𝟙_ D) ≫ L.map e.hom = (ρ_ (L.obj W)).hom)
    (Q : ObjectProperty D) :
    IntegrationPurity L R P adj W t π Q ∧
      ∃ γ : P ⋙ tensorLeft W ⟶ R,
        IntegrationGammaNormalized L R P adj W t π γ ∧ ∀ K, IsIso (γ.app K) := by
  let c : (P ⋙ tensorLeft W) ⋙ L ⟶ 𝟭 D :=
    inv π ≫ (curriedTensor D).map t ≫ (leftUnitorNatIso D).hom
  let γ : P ⋙ tensorLeft W ⟶ R :=
    { app := fun K ↦ adj.homEquiv _ K (c.app K)
      naturality := by
        intro K K' f
        apply adj.homEquiv_naturality_left_square
        exact c.naturality f }
  have hc (K : D) : L.map (γ.app K) ≫ adj.counit.app K = c.app K :=
    (adj.homEquiv _ K).symm_apply_apply (c.app K)
  have hi (K : D) : IsIso (γ.app K) := by
    simpa only [γ, c, NatTrans.comp_app, NatIso.isIso_inv_app,
      curriedTensor_map_app, leftUnitorNatIso_hom_app] using hiso K
  let : ∀ K, IsIso (γ.app K) := hi
  let : IsIso γ := NatIso.isIso_of_isIso_app γ
  have hn : IntegrationGammaNormalized L R P adj W t π γ := by
    intro K
    refine ⟨c.app K, heq_of_eq (hc K), heq_of_eq ?_⟩
    simp [c]
  have hu' : L.map e.inv ≫ inv (π.app (𝟙_ D)) = (ρ_ (L.obj W)).inv := by
    apply (cancel_mono (ρ_ (L.obj W)).hom).1
    rw [Category.assoc, ← hu, ← Category.assoc (inv (π.app (𝟙_ D))),
      IsIso.inv_hom_id, Category.id_comp, ← L.map_comp, Iso.inv_hom_id,
      L.map_id, hu, Iso.inv_hom_id]
  have ht : L.map e.inv ≫ c.app (𝟙_ D) = t := by
    change L.map e.inv ≫ ((inv π).app (𝟙_ D) ≫
      (t ▷ 𝟙_ D) ≫ (λ_ (𝟙_ D)).hom) = t
    rw [NatIso.isIso_inv_app, ← Category.assoc, ← Category.assoc, hu']
    simp [unitors_equal]
  let β : R.obj (𝟙_ D) ≅ W := (asIso (γ.app (𝟙_ D))).symm ≪≫ e
  have hβ : L.map β.inv ≫ adj.counit.app (𝟙_ D) = t := by
    dsimp only [β, Iso.trans_inv, Iso.symm_inv, asIso_hom]
    rw [L.map_comp, Category.assoc, hc]
    exact ht
  refine ⟨⟨fun K ↦ inferInstance, ?_, ?_⟩, γ, hn, hi⟩
  · let α : Q.ι ⋙ R ≅ Q.ι ⋙ (P ⋙ tensorLeft W) :=
      (Functor.isoWhiskerLeft Q.ι (asIso γ)).symm
    refine ⟨α, ?_, ?_⟩
    · intro K
      exact hn K.obj
    · intro α' hα'
      have hinv : α'.inv = α.inv := by
        ext K
        apply (adj.homEquiv _ K.obj).symm.injective
        rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
        change L.map (α'.inv.app K) ≫ adj.counit.app K.obj =
          L.map (γ.app K.obj) ≫ adj.counit.app K.obj
        obtain ⟨m, hm, hp⟩ := hα' K
        obtain ⟨n, hn, hq⟩ := hn K.obj
        rw [eq_of_heq hm, eq_of_heq hn]
        apply (cancel_epi (π.app K.obj)).1
        exact (eq_of_heq hp).trans (eq_of_heq hq).symm
      exact Iso.ext_inv hinv
  · refine ⟨β, hβ, ?_⟩
    intro β' hβ'
    have h : β'.inv = β.inv := by
      apply (adj.homEquiv _ (𝟙_ D)).symm.injective
      simpa only [Adjunction.homEquiv_counit] using hβ'.trans hβ.symm
    exact Iso.ext_inv h

/-- Perform the projection and unit calculations before specializing the coefficient category;
the right adjoint of `Rf_!` is abstracted, so no general-coefficient `Rf^!` is used. -/
private theorem normalized_etale_general
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A]
    {FC : A → A → Type (u + 1)} {CC : A → Type (u + 1)}
    [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
    [(CategoryTheory.forget A).ReflectsIsomorphisms]
    [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
    [∀ T : Scheme.{u}, T.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    [(Etale.rightDerivedLowerShriek A f).IsLeftAdjoint]
    [IsIso (Etale.projectionMap A f)]
    (R : DerivedCategory (Sheaf Y.smallEtaleTopology A) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology A))
    (adj : Etale.rightDerivedLowerShriek A f ⊣ R)
    (W : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (t : (Etale.rightDerivedLowerShriek A f).obj W ⟶
      (DerivedCategory.singleFunctor (Sheaf Y.smallEtaleTopology A) 0).obj
        (𝟙_ (Sheaf Y.smallEtaleTopology A)))
    (Q : ObjectProperty (DerivedCategory (Sheaf Y.smallEtaleTopology A)))
    (h : ∀ K, ∀ [IsIso (
        ((Etale.derivedTensorSymmetry A Y).hom.app K).app
          ((Etale.rightDerivedLowerShriek A f).obj W) ≫
        ((Etale.projectionMap A f).app W).app K ≫
        (Etale.rightDerivedLowerShriek A f).map
          (((Etale.derivedTensorSymmetry A X).hom.app W).app
            (((Etale.upperStar A f).leftDerivedFunctor).obj K)))],
      IsIso (adj.homEquiv _ K
      (inv (((Etale.derivedTensorSymmetry A Y).hom.app K).app
          ((Etale.rightDerivedLowerShriek A f).obj W) ≫
        ((Etale.projectionMap A f).app W).app K ≫
        (Etale.rightDerivedLowerShriek A f).map
          (((Etale.derivedTensorSymmetry A X).hom.app W).app
            (((Etale.upperStar A f).leftDerivedFunctor).obj K))) ≫
        ((Etale.derivedTensor A Y).obj K).map t ≫
        (Etale.derivedTensorRightUnitor A Y K).hom))) :
    IntegrationPurity (Etale.rightDerivedLowerShriek A f)
      R ((Etale.upperStar A f).leftDerivedFunctor)
      adj W
        (t ≫ (Etale.singleFunctorObjUnitIso A Y).hom)
      ((Etale.projectionMap A f).app W) Q ∧
    ∃ γ : (Etale.upperStar A f).leftDerivedFunctor ⋙ tensorLeft W ⟶
        R,
      IntegrationGammaNormalized (Etale.rightDerivedLowerShriek A f)
        R ((Etale.upperStar A f).leftDerivedFunctor)
        adj W
        (t ≫ (Etale.singleFunctorObjUnitIso A Y).hom)
        ((Etale.projectionMap A f).app W) γ ∧ ∀ K, IsIso (γ.app K) := by
  have hu : (Etale.singleFunctorObjUnitIso A Y).hom = 𝟙 _ := by
    have h := (Etale.singleFunctorObjUnitIso A Y).hom_inv_id
    rwa [Etale.singleFunctorObjUnitIso_inv, Category.comp_id] at h
  have ht : t ≫ (Etale.singleFunctorObjUnitIso A Y).hom = t := by
    rw [hu]
    exact Category.comp_id t
  rw [ht]
  let π : tensorLeft ((Etale.rightDerivedLowerShriek A f).obj W) ⟶
      ((Etale.upperStar A f).leftDerivedFunctor ⋙ tensorLeft W) ⋙
        Etale.rightDerivedLowerShriek A f := (Etale.projectionMap A f).app W
  let e : ((Etale.upperStar A f).leftDerivedFunctor ⋙ tensorLeft W).obj (𝟙_ _) ≅ W :=
    (tensorLeft W).mapIso (Etale.leftDerivedUpperStarUnitIso A f) ≪≫ ρ_ W
  apply normalized_of_iso_mates (Etale.rightDerivedLowerShriek A f)
    R ((Etale.upperStar A f).leftDerivedFunctor)
    adj W t π ?_ e
    (Etale.projectionMap_rightUnitality A f W) Q
  intro K
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology A)
  let := _root_.DerivedCategory.braidedCategory' (Sheaf Y.smallEtaleTopology A)
  exact swap_mate_isIso _ _ _ adj
    W t K (π.app K) (h K)

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] Etale.sheafBraidedCategory
attribute [local irreducible] Etale.rightDerivedUpperShriek
  Etale.rightDerivedUpperShriekAdjunction
attribute [local irreducible] VectorBundleZeroSection.scheme VectorBundleZeroSection.π
  VectorBundleZeroSection.over VectorBundleZeroSection.antiEquivalence

/-- Retain the native finite-unit presentation when specializing to module coefficients. -/
private theorem normalized_finite_general
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (W : Etale.DerivedCategoryModule A X)
    (t : (RfShriek A f).obj W ⟶ Etale.ordinaryFiniteUnit A Y)
    (Q : ObjectProperty (Etale.DerivedCategoryModule A Y))
    (h : ∀ K, ∀ [IsIso (Etale.compactProjectionMapCoeffFirst A f K W)],
      IsIso ((Etale.rightDerivedUpperShriekAdjunction A f).homEquiv _ K
        (inv (Etale.compactProjectionMapCoeffFirst A f K W) ≫
          ((Etale.derivedTensor (ModuleCat A) Y).obj K).map t ≫
          (Etale.derivedTensorRightUnitor (ModuleCat A) Y K).hom))) :
    VectorPurityFunctorConclusion A f Q W
      (t ≫ (Etale.singleFunctorObjUnitIso (ModuleCat A) Y).hom) ∧
    ∃ γ : RfPullback A f ⋙ tensorLeft W ⟶ RfUpper A f,
      IntegrationGammaNormalized (RfShriek A f) (RfUpper A f) (RfPullback A f)
        (Etale.rightDerivedUpperShriekAdjunction A f) W
        (t ≫ (Etale.singleFunctorObjUnitIso (ModuleCat A) Y).hom)
        ((Etale.projectionMap (ModuleCat A) f).app W) γ ∧ ∀ K, IsIso (γ.app K) := by
  apply normalized_etale_general (ModuleCat A) f (RfUpper A f)
    (Etale.rightDerivedUpperShriekAdjunction A f) W t Q
  intro K hp
  let : IsIso (Etale.compactProjectionMapCoeffFirst A f K W) := hp
  exact h K

/-- The integration-normalized vector purity family on every ordinary unbounded input.
Source: current blueprint sec-smooth-purity/sk-prop-an, integration and Steps 4--6.
Proof: apply the generic normalized integration construction to the canonical vector-bundle
projection. The projection is invertible for finite coefficients. Conjugate the coefficient-first
projection with the derived tensor symmetry and invoke the established vector integration mate
isomorphism. The counit normalization and unit orientation follow from the adjunction triangle
and right-unitality of the projection map. The remaining base-change, direct-sum and scalar
identities are separate compatibility statements used by the parent.
(blueprint: lem-pur-normalized-vector-purity-bundle). -/
theorem vectorBundleNormalized
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (B : Scheme.{u}) [IsNoetherian B] (hB : IsUnit (N : Γ(B, ⊤)))
    (d : ℕ) (F : B.Modules) [F.IsFiniteLocallyFreeOfRank d] :
    let := (Etale.vectorIntegration_geometry B d F).1
    let := (Etale.vectorIntegration_geometry B d F).2.1
    VectorPurityFunctorConclusion A (VectorBundleZeroSection.π B d F)
      (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) B)
      (Etale.vectorIntegrationCoefficient A N hA B d F)
      (Etale.vectorBundleIntegration N hN A hA B hB d F ≫
        (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) B).hom) ∧
    ∃ γ : VectorPurityGamma A N hA B d F,
      VectorPurityGammaNormalized A N hN hA B hB d F γ ∧
      ∀ K : Etale.DerivedCategoryModule A B, IsIso (γ.app K) := by
  let := (Etale.vectorIntegration_geometry B d F).1
  let := (Etale.vectorIntegration_geometry B d F).2.1
  let f := VectorBundleZeroSection.π B d F
  let W := Etale.vectorIntegrationCoefficient A N hA B d F
  let t : (RfShriek A f).obj W ⟶ Etale.ordinaryFiniteUnit A B :=
    Etale.vectorBundleIntegration N hN A hA B hB d F
  apply normalized_finite_general A f W t
    (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) B)
  intro K hp
  exact Etale.vectorIntegrationMate_isIso N hN A hA B hB d F K

end WeilConjectures.PurityFiniteSetting
