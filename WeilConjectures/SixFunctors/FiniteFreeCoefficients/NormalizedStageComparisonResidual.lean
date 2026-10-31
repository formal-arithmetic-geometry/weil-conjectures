/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations
import all WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageHomNaturality
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageSiteEvaluation
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarTensorIdentity
import all WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageFiniteRingFoundations
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientComparison
import WeilConjectures.AlgebraicGeometry.CoefDualizingSiteMates.CoefDualizingSiteMates
import all WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCompactQuotientCocycle
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarUnitComposition
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageSiteBridgeFoundations
import WeilConjectures.SixFunctors.NormalizedSiteScalarTensor.NormalizedSiteScalarTensorComposition

/-! # Unit and composition part of normalized stage comparison coherence

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraph 3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtensionComp
  AlgebraicGeometry.ProEtale.pbcComparisonReduction
  _root_.DerivedCategory.monoidalClosed
  _root_.DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.Etale.derivedTensor AlgebraicGeometry.Etale.derivedHom
  AlgebraicGeometry.ProEtale.derivedHom

namespace ResidualHomProof

open StageHomProof
local notation "uncurry₀" => Functor.uncurry.obj

variable {A B C : Type*} [Category A] [Category B] [Category C]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem uncurry_pre
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (c : ∀ K : C, T.obj K ⊣ H.obj (op K))
    {N N' K M : C} (f : N ⟶ N') (g : N' ⟶ (H.obj (op K)).obj M) :
    ((c K).homEquiv N M).symm (f ≫ g) =
      (uncurry₀ T).map (Prod.mkHom (𝟙 K) f) ≫ ((c K).homEquiv N' M).symm g := by
  rw [uncurry, uncurry, tensor_right_comp, Category.assoc]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem uncurry_post
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (c : ∀ K : C, T.obj K ⊣ H.obj (op K))
    (hc : ∀ (K K' M : C) (f : K' ⟶ K),
      (uncurry₀ T).map (Prod.mkHom (𝟙 K')
          ((uncurry₀ H).map (Prod.mkHom f.op (𝟙 M)))) ≫ (c K').counit.app M =
        (uncurry₀ T).map (Prod.mkHom f (𝟙 _)) ≫ (c K).counit.app M)
    {N K M K' M' : C} (g : N ⟶ (H.obj (op K)).obj M)
    (f : K' ⟶ K) (h : M ⟶ M') :
    ((c K').homEquiv N M').symm
        (g ≫ (uncurry₀ H).map (Prod.mkHom f.op h)) =
      (uncurry₀ T).map (Prod.mkHom f (𝟙 N)) ≫
        ((c K).homEquiv N M).symm g ≫ h := by
  rw [uncurry_pre, uncurry, evaluation_transport T H c hc, uncurry]
  simp only [← Category.assoc, ← (uncurry₀ T).map_comp]
  congr 2
  congr 1
  ext <;> simp

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem hom_beta
    {TA : A ⥤ A ⥤ A} {HA : Aᵒᵖ ⥤ A ⥤ A}
    {TB : B ⥤ B ⥤ B} {HB : Bᵒᵖ ⥤ B ⥤ B}
    (a : ∀ K : A, TA.obj K ⊣ HA.obj (op K))
    (b : ∀ K : B, TB.obj K ⊣ HB.obj (op K))
    (F : A ⥤ B) (μ : uncurry₀ TA ⋙ F ≅ F.prod F ⋙ uncurry₀ TB) (K M : A) :
    ((b (F.obj K)).homEquiv _ _).symm (StageHomProof.homMap a b F μ K M) =
      μ.inv.app (K, (HA.obj (op K)).obj M) ≫ F.map ((a K).counit.app M) :=
  Equiv.symm_apply_apply _ _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem hom_tower
    {TA : A ⥤ A ⥤ A} {HA : Aᵒᵖ ⥤ A ⥤ A}
    {TB : B ⥤ B ⥤ B} {HB : Bᵒᵖ ⥤ B ⥤ B}
    {TC : C ⥤ C ⥤ C} {HC : Cᵒᵖ ⥤ C ⥤ C}
    (a : ∀ K : A, TA.obj K ⊣ HA.obj (op K))
    (b : ∀ K : B, TB.obj K ⊣ HB.obj (op K))
    (c : ∀ K : C, TC.obj K ⊣ HC.obj (op K))
    (hc : ∀ (K K' M : C) (f : K' ⟶ K),
      (uncurry₀ TC).map (Prod.mkHom (𝟙 K')
          ((uncurry₀ HC).map (Prod.mkHom f.op (𝟙 M)))) ≫ (c K').counit.app M =
        (uncurry₀ TC).map (Prod.mkHom f (𝟙 _)) ≫ (c K).counit.app M)
    (F : A ⥤ B) (G : B ⥤ C) (L : A ⥤ C)
    (μ : uncurry₀ TA ⋙ F ≅ F.prod F ⋙ uncurry₀ TB)
    (ν : uncurry₀ TB ⋙ G ≅ G.prod G ⋙ uncurry₀ TC)
    (ξ : uncurry₀ TA ⋙ L ≅ L.prod L ⋙ uncurry₀ TC) (α : F ⋙ G ≅ L)
    (ht : ∀ X Y : A,
      G.map (μ.hom.app (X, Y)) ≫ ν.hom.app (F.obj X, F.obj Y) ≫
          (uncurry₀ TC).map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) =
        α.hom.app ((uncurry₀ TA).obj (X, Y)) ≫ ξ.hom.app (X, Y)) (K M : A) :
    G.map (StageHomProof.homMap a b F μ K M) ≫ StageHomProof.homMap b c G ν (F.obj K) (F.obj M) ≫
        (uncurry₀ HC).map (Prod.mkHom (α.inv.app K).op (α.hom.app M)) =
      α.hom.app ((HA.obj (op K)).obj M) ≫ StageHomProof.homMap a c L ξ K M := by
  have hi (X Y : A) :
      ν.inv.app (F.obj X, F.obj Y) ≫ G.map (μ.inv.app (X, Y)) ≫
          α.hom.app ((uncurry₀ TA).obj (X, Y)) =
        (uncurry₀ TC).map (Prod.mkHom (α.hom.app X) (α.hom.app Y)) ≫
          ξ.inv.app (X, Y) := by
    apply (cancel_mono (ξ.hom.app (X, Y))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← ht]
    simp [← G.map_comp, ← Category.assoc]
  have he : ((c (G.obj (F.obj K))).homEquiv _ (G.obj (F.obj M))).symm
      (G.map (StageHomProof.homMap a b F μ K M) ≫ StageHomProof.homMap b c G ν (F.obj K) (F.obj M))
          =
      ν.inv.app (F.obj K, F.obj ((HA.obj (op K)).obj M)) ≫
        G.map (μ.inv.app (K, (HA.obj (op K)).obj M)) ≫
          G.map (F.map ((a K).counit.app M)) := by
    rw [uncurry_pre]
    rw [hom_beta]
    have hn := ν.inv.naturality
      (Prod.mkHom (𝟙 (F.obj K)) (StageHomProof.homMap a b F μ K M))
    dsimp only [Functor.comp_map, Functor.prod_map] at hn
    erw [G.map_id] at hn
    rw [← Category.assoc, hn, Category.assoc, ← G.map_comp]
    rw [← uncurry, hom_beta, G.map_comp]
  apply ((c (L.obj K)).homEquiv _ (L.obj M)).symm.injective
  rw [← Category.assoc, uncurry_post TC HC c hc, he, uncurry_pre]
  rw [hom_beta]
  have hn := α.hom.naturality ((a K).counit.app M)
  dsimp only [Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hn
  simp only [Category.assoc]
  rw [hn]
  erw [reassoc_of% hi K ((HA.obj (op K)).obj M)]
  rw [← Category.assoc, ← (uncurry₀ TC).map_comp]
  congr 2
  ext <;> simp

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem hom_id
    {T : A ⥤ A ⥤ A} {H : Aᵒᵖ ⥤ A ⥤ A}
    (a : ∀ K : A, T.obj K ⊣ H.obj (op K)) (K M : A) :
    StageHomProof.homMap a a (𝟭 A) (Iso.refl _) K M = 𝟙 _ := by
  apply ((a K).homEquiv _ _).symm.injective
  dsimp only [StageHomProof.homMap, Functor.id_obj]
  rw [Equiv.symm_apply_apply]
  simp [uncurry, ← prod_id]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem hom_unit
    {T : A ⥤ A ⥤ A} {H : Aᵒᵖ ⥤ A ⥤ A}
    (a : ∀ K : A, T.obj K ⊣ H.obj (op K))
    (ha : ∀ (K K' M : A) (f : K' ⟶ K),
      (uncurry₀ T).map (Prod.mkHom (𝟙 K')
          ((uncurry₀ H).map (Prod.mkHom f.op (𝟙 M)))) ≫ (a K').counit.app M =
        (uncurry₀ T).map (Prod.mkHom f (𝟙 _)) ≫ (a K).counit.app M)
    (F : A ⥤ A) (μ : uncurry₀ T ⋙ F ≅ F.prod F ⋙ uncurry₀ T)
    (z : F ≅ 𝟭 A)
    (ht : ∀ K M : A, μ.hom.app (K, M) ≫
      (uncurry₀ T).map (Prod.mkHom (z.hom.app K) (z.hom.app M)) =
        z.hom.app ((uncurry₀ T).obj (K, M))) (K M : A) :
    StageHomProof.homMap a a F μ K M ≫
        (uncurry₀ H).map (Prod.mkHom (z.inv.app K).op (z.hom.app M)) =
      z.hom.app ((H.obj (op K)).obj M) := by
  have h := hom_tower a a a ha F (𝟭 A) (𝟭 A) μ (Iso.refl _) (Iso.refl _)
    (F.rightUnitor ≪≫ z) (by
      intro U V
      simpa [Functor.id_map, Iso.refl_hom, NatTrans.id_app, Category.id_comp, Category.comp_id,
        Iso.trans_hom, NatTrans.comp_app, Functor.rightUnitor_hom_app] using ht U V) K M
  simpa [Functor.id_map, hom_id, Category.comp_id, Iso.trans_hom,
    Iso.trans_inv, NatTrans.comp_app, Functor.rightUnitor_hom_app,
    Functor.rightUnitor_inv_app, Category.id_comp] using h

end ResidualHomProof

namespace ResidualMateProof

variable {C₁ D₁ C₂ D₂ C₃ D₃ : Type*}
  [Category C₁] [Category D₁] [Category C₂] [Category D₂]
  [Category C₃] [Category D₃]
  {P₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {P₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
  {P₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
  {S : C₁ ⥤ C₂} {T : D₁ ⥤ D₂} {U : C₂ ⥤ C₃} {V : D₂ ⥤ D₃}
  {W : C₁ ⥤ C₃} {Z : D₁ ⥤ D₃}

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem inverse_natural
    (d : P₁ ⋙ T ⟶ S ⋙ P₂) {K L : C₁} (g : K ⟶ L)
    [IsIso (d.app K)] [IsIso (d.app L)] :
    P₂.map (S.map g) ≫ inv (d.app L) = inv (d.app K) ≫ T.map (P₁.map g) := by
  apply (cancel_epi (d.app K)).1
  simp only [IsIso.hom_inv_id_assoc]
  have hn := d.naturality g
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, ← hn]
  simp

attribute [-instance] CategoryTheory.catToReflQuiver in
private def mateAt (a : P₁ ⊣ R₁) (b : P₂ ⊣ R₂)
    (d : P₁ ⋙ T ⟶ S ⋙ P₂) (K : D₁) [IsIso (d.app (R₁.obj K))] :
    S.obj (R₁.obj K) ⟶ R₂.obj (T.obj K) :=
  b.homEquiv _ _ (inv (d.app (R₁.obj K)) ≫ T.map (a.counit.app K))

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem mateAt_beta (a : P₁ ⊣ R₁) (b : P₂ ⊣ R₂)
    (d : P₁ ⋙ T ⟶ S ⋙ P₂) (K : D₁) [IsIso (d.app (R₁.obj K))] :
    P₂.map (mateAt a b d K) ≫ b.counit.app (T.obj K) =
      inv (d.app (R₁.obj K)) ≫ T.map (a.counit.app K) := by
  exact (b.homEquiv _ _).symm_apply_apply _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem mateAt_natural (a : P₁ ⊣ R₁) (b : P₂ ⊣ R₂)
    (d : P₁ ⋙ T ⟶ S ⋙ P₂) {K L : D₁} (g : K ⟶ L)
    [IsIso (d.app (R₁.obj K))] [IsIso (d.app (R₁.obj L))] :
    S.map (R₁.map g) ≫ mateAt a b d L =
      mateAt a b d K ≫ R₂.map (T.map g) := by
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hn := b.counit.naturality (T.map g)
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [mateAt_beta, hn]
  rw [reassoc_of% mateAt_beta a b d K]
  rw [reassoc_of% inverse_natural d (R₁.map g), ← T.map_comp]
  erw [a.counit.naturality]
  simp only [Functor.id_map, T.map_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem mateAt_comp (a : P₁ ⊣ R₁) (b : P₂ ⊣ R₂) (c : P₃ ⊣ R₃)
    (d : P₁ ⋙ T ⟶ S ⋙ P₂) (e : P₂ ⋙ V ⟶ U ⋙ P₃)
    (k : P₁ ⋙ Z ⟶ W ⋙ P₃) (eX : S ⋙ U ≅ W) (eY : T ⋙ V ≅ Z)
    (K : D₁)
    [IsIso (d.app (R₁.obj K))] [IsIso (k.app (R₁.obj K))]
    [IsIso (e.app (S.obj (R₁.obj K)))] [IsIso (e.app (R₂.obj (T.obj K)))]
    (hc : V.map (d.app (R₁.obj K)) ≫ e.app (S.obj (R₁.obj K)) ≫
        P₃.map (eX.hom.app (R₁.obj K)) =
      eY.hom.app (P₁.obj (R₁.obj K)) ≫ k.app (R₁.obj K)) :
    U.map (mateAt a b d K) ≫ mateAt b c e (T.obj K) ≫ R₃.map (eY.hom.app K) =
      eX.hom.app (R₁.obj K) ≫ mateAt a c k K := by
  have hi : P₃.map (eX.hom.app (R₁.obj K)) ≫ inv (k.app (R₁.obj K)) =
      inv (e.app (S.obj (R₁.obj K))) ≫ V.map (inv (d.app (R₁.obj K))) ≫
        eY.hom.app (P₁.obj (R₁.obj K)) := by
    apply (cancel_epi (V.map (d.app (R₁.obj K)) ≫ e.app (S.obj (R₁.obj K)))).1
    calc
      _ = (eY.hom.app _ ≫ k.app _) ≫ inv (k.app _) := by
        rw [← hc]; simp only [Category.assoc]
      _ = _ := by simp [Category.assoc]
  apply (c.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hn := c.counit.naturality (eY.hom.app K)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at hn
  rw [hn]
  rw [reassoc_of% mateAt_beta b c e (T.obj K)]
  rw [reassoc_of% inverse_natural e (mateAt a b d K)]
  rw [← V.map_comp_assoc, mateAt_beta, V.map_comp]
  have hy := eY.hom.naturality (a.counit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hy
  simp only [Category.assoc]
  rw [hy]
  rw [← reassoc_of% hi, mateAt_beta]

end ResidualMateProof

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_direct_comp
    (pro : Bool) {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ)
    {T X : Scheme.{u}} (f : T ⟶ X) (K : Sites.D pro A T) :
    (Sites.scalar pro ψ X).map (Sites.direct pro φ f K) ≫
        Sites.direct pro ψ f ((Sites.scalar pro φ T).obj K) ≫
          (Sites.push pro C f).map ((Sites.comp pro φ ψ χ h T).hom.app K) =
      (Sites.comp pro φ ψ χ h X).hom.app ((Sites.push pro A f).obj K) ≫
        Sites.direct pro χ f K := by
  subst χ
  cases pro <;> dsimp only [Sites.scalar, Sites.direct, Sites.push, Sites.comp, id_eq]
  · have he := Etale.finiteCoefficientDirectImageMap_coefficientChain φ ψ f K
    have hcomp := congrArg (fun g ↦
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ (ψ.comp φ) rfl).hom.app
        ((R(Etale.lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫ g) he
    simpa only [CategoryTheory.Category.assoc, Iso.hom_inv_id_app_assoc] using hcomp.symm
  · have he := ProEtale.finiteCoefficientDirectImageMap_coefficientChain φ ψ f K
    have hcomp := congrArg (fun g ↦
      (ProEtale.pbcFixedScalarExtensionComp (Scheme.ProEt.topology X)
        φ ψ (ψ.comp φ) rfl).hom.app
          ((R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f)).obj K) ≫ g) he
    simpa only [CategoryTheory.Category.assoc, Iso.hom_inv_id_app_assoc] using hcomp.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_unit_of_cocycle
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (S : C ⥤ C) (T : D ⥤ D)
    (uS : S ≅ 𝟭 C) (uT : T ≅ 𝟭 D)
    (b : F ⋙ T ⟶ S ⋙ F) (K : C) [IsIso (b.app K)]
    (hc : uT.hom.app (T.obj (F.obj K)) ≫ b.app K =
      T.map (b.app K) ≫ b.app (S.obj K) ≫ F.map (uS.hom.app (S.obj K))) :
    b.app K ≫ F.map (uS.hom.app K) = uT.hom.app (F.obj K) := by
  have hs : uS.hom.app (S.obj K) = S.map (uS.hom.app K) := by
    apply (cancel_mono (uS.hom.app K)).mp
    exact (uS.hom.naturality (uS.hom.app K)).symm
  rw [hs, ← Functor.comp_map, ← b.naturality] at hc
  simp only [Functor.comp_map, ← T.map_comp, ← Category.assoc] at hc
  have hh := (cancel_mono (b.app K)).mp hc
  have hn := uT.hom.naturality (b.app K ≫ F.map (uS.hom.app K))
  dsimp only [Functor.id_map, Functor.comp_obj, Functor.id_obj] at hn
  apply (cancel_epi (uT.hom.app (T.obj (F.obj K)))).mp
  simpa only [Category.assoc, hh] using hn.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_unit_at
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (S : C ⥤ C) (T : D ⥤ D)
    (uS : S ≅ 𝟭 C) (uT : T ≅ 𝟭 D) (K : C)
    (b : T.obj (F.obj K) ⟶ F.obj (S.obj K))
    (b' : T.obj (F.obj (S.obj K)) ⟶ F.obj (S.obj (S.obj K))) [IsIso b]
    (hn : T.map (F.map (uS.hom.app K)) ≫ b =
      b' ≫ F.map (S.map (uS.hom.app K)))
    (hc : uT.hom.app (T.obj (F.obj K)) ≫ b =
      T.map b ≫ b' ≫ F.map (uS.hom.app (S.obj K))) :
    b ≫ F.map (uS.hom.app K) = uT.hom.app (F.obj K) := by
  have hs : uS.hom.app (S.obj K) = S.map (uS.hom.app K) := by
    apply (cancel_mono (uS.hom.app K)).mp
    exact (uS.hom.naturality (uS.hom.app K)).symm
  rw [hs, ← hn, ← T.map_comp_assoc] at hc
  have hh := (cancel_mono b).mp hc
  have hu := uT.hom.naturality (b ≫ F.map (uS.hom.app K))
  dsimp only [Functor.id_map, Functor.comp_obj, Functor.id_obj] at hu
  apply (cancel_epi (uT.hom.app (T.obj (F.obj K)))).mp
  simpa only [Category.assoc, hh] using hu.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_scalar_self_comp
    (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Sites.comp pro (RingHom.id A) (RingHom.id A) (RingHom.id A) (by ext; rfl) X =
      Functor.isoWhiskerLeft (Sites.scalar pro (RingHom.id A) X)
        (Sites.unit pro (RingHom.id A) rfl X) ≪≫
          (Sites.scalar pro (RingHom.id A) X).rightUnitor := by
  cases pro <;> dsimp only [Sites.comp, Sites.scalar, Sites.unit]
  · exact Etale.ExceptionalCoefficients.scalar_comp_unit X.smallEtaleTopology A
  · exact Etale.ExceptionalCoefficients.scalar_comp_unit (Scheme.ProEt.topology X) A

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_scalar_id_comp
    (pro : Bool) {A : Type (u + 1)} [CommRing A]
    (φ : A →+* A) (hφ : φ = RingHom.id A) (h : φ = φ.comp φ) (X : Scheme.{u}) :
    Sites.comp pro φ φ φ h X =
      Functor.isoWhiskerLeft (Sites.scalar pro φ X) (Sites.unit pro φ hφ X) ≪≫
        (Sites.scalar pro φ X).rightUnitor := by
  subst φ
  exact residual_scalar_self_comp pro A X

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_scalar_id_comp_app
    (pro : Bool) {A : Type (u + 1)} [CommRing A]
    (φ : A →+* A) (hφ : φ = RingHom.id A) (h : φ = φ.comp φ) (X : Scheme.{u})
    (K : Sites.D pro A X) :
    (Sites.comp pro φ φ φ h X).hom.app K =
      (Sites.unit pro φ hφ X).hom.app ((Sites.scalar pro φ X).obj K) := by
  rw [residual_scalar_id_comp pro φ hφ]
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.comp_obj]
  exact Category.comp_id _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_direct_unit
    (pro : Bool) {A : Type (u + 1)} [CommRing A]
    (φ : A →+* A) (hφ : φ = RingHom.id A) {T X : Scheme.{u}} (f : T ⟶ X)
    (K : Sites.D pro A T) [IsIso (Sites.direct pro φ f K)] :
    Sites.direct pro φ f K ≫
        (Sites.push pro A f).map ((Sites.unit pro φ hφ T).hom.app K) =
      (Sites.unit pro φ hφ X).hom.app ((Sites.push pro A f).obj K) := by
  subst φ
  let b : Sites.push pro A f ⋙ Sites.scalar pro (RingHom.id A) X ⟶
      Sites.scalar pro (RingHom.id A) T ⋙ Sites.push pro A f := {
    app := Sites.direct pro (RingHom.id A) f
    naturality := fun _ _ g ↦ by
      cases pro <;> dsimp only [Sites.scalar, Sites.direct, Sites.push, id_eq]
      · exact Etale.finiteCoefficientDirectImageMap_naturality (RingHom.id A) f g
      · exact ProEtale.finiteCoefficientDirectImageMap_naturality (RingHom.id A) f g }
  apply residual_unit_of_cocycle (Sites.push pro A f)
    (Sites.scalar pro (RingHom.id A) T) (Sites.scalar pro (RingHom.id A) X)
    (Sites.unit pro (RingHom.id A) rfl T) (Sites.unit pro (RingHom.id A) rfl X) b K
  have h := residual_direct_comp pro (RingHom.id A) (RingHom.id A) (RingHom.id A)
    (by ext; rfl) f K
  rw [residual_scalar_self_comp, residual_scalar_self_comp] at h
  simpa [b, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Functor.comp_obj,
    Category.comp_id] using h.symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private abbrev residual_etale_direct_trans
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) :
    R(Etale.lowerStar (ModuleCat.{u + 1} A) i) ⋙ Etale.scalarExtension φ X ⟶
      Etale.scalarExtension φ Z ⋙ R(Etale.lowerStar (ModuleCat.{u + 1} B) i) where
  app := Etale.finiteCoefficientDirectImageMap φ i
  naturality := fun _ _ g ↦ Etale.finiteCoefficientDirectImageMap_naturality φ i g

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_closed_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Cat A X) [IsIso (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj M))] :
    closedMap φ i M = ResidualMateProof.mateAt
      (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)))
      (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)))
      (residual_etale_direct_trans φ i) M := by
  dsimp only [closedMap, ResidualMateProof.mateAt, residual_etale_direct_trans, Sites.push,
    Sites.scalar, Sites.direct, id_eq] at *
  rw [dif_pos (inferInstance : IsIso (Etale.finiteCoefficientDirectImageMap φ i
    ((closedUpper A i).obj M)))]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_closed_natural_etale
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {K L : Cat A X} (g : K ⟶ L)
    [IsIso (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj K))]
    [IsIso (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj L))] :
    (Etale.scalarExtension φ Z).map ((closedUpper A i).map g) ≫ closedMap φ i L =
      closedMap φ i K ≫ (closedUpper B i).map ((Etale.scalarExtension φ X).map g) := by
  rw [residual_closed_eq, residual_closed_eq]
  exact ResidualMateProof.mateAt_natural
    (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)))
    (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)))
    (residual_etale_direct_trans φ i) g

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_closed_comp_etale
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (M : Cat A X)
    [IsIso (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj M))]
    [IsIso (Etale.finiteCoefficientDirectImageMap χ i ((closedUpper A i).obj M))]
    [IsIso (Etale.finiteCoefficientDirectImageMap ψ i
      ((closedUpper B i).obj ((Etale.scalarExtension φ X).obj M)))] :
    (Etale.scalarExtension ψ Z).map (closedMap φ i M) ≫
        closedMap ψ i ((Etale.scalarExtension φ X).obj M) ≫
          (closedUpper C i).map ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ
              h).hom.app M) =
      (ProEtale.pbcFixedScalarExtensionComp Z.smallEtaleTopology φ ψ χ h).hom.app ((closedUpper A
          i).obj M) ≫
        closedMap χ i M := by
  have hc := residual_direct_comp false φ ψ χ h i ((closedUpper A i).obj M)
  dsimp only [Sites.scalar, Sites.direct, Sites.push, Sites.comp, id_eq] at hc
  have hall : IsIso (((Etale.scalarExtension ψ X).map
        (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj M)) ≫
      Etale.finiteCoefficientDirectImageMap ψ i ((Etale.scalarExtension φ Z).obj ((closedUpper A
          i).obj M))) ≫
        (R(Etale.lowerStar (ModuleCat.{u + 1} C) i)).map
          ((ProEtale.pbcFixedScalarExtensionComp Z.smallEtaleTopology φ ψ χ h).hom.app ((closedUpper
              A i).obj M))) := by
    rw [Category.assoc, hc]
    infer_instance
  have htwo : IsIso ((Etale.scalarExtension ψ X).map
        (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj M)) ≫
      Etale.finiteCoefficientDirectImageMap ψ i ((Etale.scalarExtension φ Z).obj ((closedUpper A
          i).obj M))) :=
    IsIso.of_isIso_comp_right _
      ((R(Etale.lowerStar (ModuleCat.{u + 1} C) i)).map
        ((ProEtale.pbcFixedScalarExtensionComp Z.smallEtaleTopology φ ψ χ h).hom.app ((closedUpper A
            i).obj M)))
  have : IsIso (Etale.finiteCoefficientDirectImageMap ψ i
      ((Etale.scalarExtension φ Z).obj ((closedUpper A i).obj M))) :=
    IsIso.of_isIso_comp_left
      ((Etale.scalarExtension ψ X).map (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A
          i).obj M))) _
  rw [residual_closed_eq, residual_closed_eq, residual_closed_eq]
  exact ResidualMateProof.mateAt_comp _ _ _
    (residual_etale_direct_trans φ i) (residual_etale_direct_trans ψ i)
    (residual_etale_direct_trans χ i) (ProEtale.pbcFixedScalarExtensionComp Z.smallEtaleTopology φ ψ
        χ h)
    (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ h) M hc

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_rnu_ctf
    {A : Type (u + 1)} [CommRing A] [Finite A] (X : Scheme.{u})
    (K : Sites.D true A X) (hK : Sites.Ctf true A X K) :
    Ctf A X ((Sites.rnu A X).obj K) := by
  obtain ⟨⟨K', hbc, ⟨e⟩⟩, a, b, ht⟩ := hK
  have ht' := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K').1
    ((ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X a b).prop_of_iso
      e.symm ht)
  have hu := ProEtale.isIso_derivedComparisonAdjunction_unit_app
    (ModuleCat.{u + 1} A) X K' hbc.1.1
  let e' : K' ≅ (Sites.rnu A X).obj K :=
    (@asIso _ _ _ _
      ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X).unit.app K') hu) ≪≫
        (Sites.rnu A X).mapIso e
  apply (ctf_iff_source A X _).2
  exact (Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X).prop_of_iso
    e' ⟨hbc, a, b, ht'⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
private def residual_rnu_trans
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    Sites.rnu A X ⋙ Etale.scalarExtension φ X ⟶
      Sites.scalar true φ X ⋙ Sites.rnu B X :=
  (mateEquiv (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X)
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} B) X)
    (TwoSquare.mk _ _ _ _ (Sites.scalarSite φ X).inv)).natTrans

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_rnu_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (M : Sites.D true A X) :
    Sites.rnuScalar φ X M = (residual_rnu_trans φ X).app M := by
  apply ((ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} B) X).homEquiv _ _).symm.injective
  rw [Sites.rnuScalar, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  exact (mateEquiv_counit
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X)
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} B) X)
    (TwoSquare.mk _ _ _ _ (Sites.scalarSite φ X).inv) M).symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_closed_natural_pro
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {K L : Sites.D true A X} (g : K ⟶ L)
    [IsIso (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj ((Sites.rnu A X).obj
        K)))]
    [IsIso (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj ((Sites.rnu A X).obj
        L)))] :
    (Sites.scalar true φ Z).map ((Sites.exceptional true A i).map g) ≫
        Sites.proClosedMap φ i L =
      Sites.proClosedMap φ i K ≫
        (Sites.exceptional true B i).map ((Sites.scalar true φ X).map g) := by
  have h₁ := (Sites.scalarSite φ Z).hom.naturality
    ((closedUpper A i).map ((Sites.rnu A X).map g))
  have h₂ := residual_closed_natural_etale φ i ((Sites.rnu A X).map g)
  have h₃ := (residual_rnu_trans φ X).naturality g
  dsimp only [Functor.comp_map, Sites.scalar, id_eq] at h₁ h₃
  dsimp only [Sites.proClosedMap, Sites.exceptional, Sites.scalar, id_eq, Functor.comp_map]
  simp only [residual_rnu_eq, Category.assoc]
  rw [reassoc_of% h₁, ← (Sites.nu B Z).map_comp_assoc, h₂]
  simp only [Functor.map_comp, Category.assoc]
  rw [← (Sites.nu B Z).map_comp, ← (closedUpper B i).map_comp, h₃]
  simp only [Functor.map_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_inverse_square
    {C : Type*} [Category C] {A B D E F : C}
    (f : A ≅ B) (g : B ≅ D) (h : E ≅ F) (x : D ⟶ F) (y : A ⟶ E)
    (hc : f.hom ≫ g.hom ≫ x = y ≫ h.hom) :
    x ≫ h.inv = g.inv ≫ f.inv ≫ y := by
  apply (cancel_epi (f.hom ≫ g.hom)).1
  calc
    _ = (y ≫ h.hom) ≫ h.inv := by rw [← hc]; simp only [Category.assoc]
    _ = _ := by simp [Category.assoc]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_site_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ)
    (X : Scheme.{u}) (K : Cat A X) :
    (Sites.scalar true ψ X).map ((Sites.scalarSite φ X).hom.app K) ≫
        (Sites.scalarSite ψ X).hom.app ((Etale.scalarExtension φ X).obj K) ≫
        (Sites.nu C X).map ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ
            h).hom.app K) =
      (Sites.comp true φ ψ χ h X).hom.app ((Sites.nu A X).obj K) ≫
        (Sites.scalarSite χ X).hom.app K := by
  subst χ
  exact ProEtale.CoefDualizingSiteMates.tensorCoherence φ ψ X K

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_rnu_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ)
    (X : Scheme.{u}) (M : Sites.D true A X) :
    (Etale.scalarExtension ψ X).map (Sites.rnuScalar φ X M) ≫
        Sites.rnuScalar ψ X ((Sites.scalar true φ X).obj M) ≫
          (Sites.rnu C X).map ((Sites.comp true φ ψ χ h X).hom.app M) =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ h).hom.app ((Sites.rnu A
          X).obj M) ≫
        Sites.rnuScalar χ X M := by
  have hc := residual_site_comp φ ψ χ h X ((Sites.rnu A X).obj M)
  have hi : (Sites.nu C X).map
        ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ h).hom.app ((Sites.rnu A
            X).obj M)) ≫
        (Sites.scalarSite χ X).inv.app ((Sites.rnu A X).obj M) =
      (Sites.scalarSite ψ X).inv.app
          ((Etale.scalarExtension φ X).obj ((Sites.rnu A X).obj M)) ≫
        (Sites.scalar true ψ X).map
          ((Sites.scalarSite φ X).inv.app ((Sites.rnu A X).obj M)) ≫
        (Sites.comp true φ ψ χ h X).hom.app
          ((Sites.nu A X).obj ((Sites.rnu A X).obj M)) := by
    exact residual_inverse_square
      ((Sites.scalar true ψ X).mapIso ((Sites.scalarSite φ X).app ((Sites.rnu A X).obj M)))
      ((Sites.scalarSite ψ X).app ((Etale.scalarExtension φ X).obj ((Sites.rnu A X).obj M)))
      ((Sites.scalarSite χ X).app ((Sites.rnu A X).obj M)) _ _ hc
  have hm := Etale.ExceptionalCoefficients.mate_cocycle_at
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} A) X)
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} B) X)
    (ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} C) X)
    (TwoSquare.mk _ _ _ _ (Sites.scalarSite φ X).inv)
    (TwoSquare.mk _ _ _ _ (Sites.scalarSite ψ X).inv)
    (TwoSquare.mk _ _ _ _ (Sites.scalarSite χ X).inv)
    (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ h) (Sites.comp true φ ψ χ h X)
        M hi
  simpa only [residual_rnu_eq, residual_rnu_trans, Sites.scalar, Sites.rnu,
    id_eq, Functor.comp_obj] using hm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_pro_closed_def
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (M : Sites.D true A X) :
    Sites.proClosedMap φ i M =
      (Sites.scalarSite φ Z).hom.app ((closedUpper A i).obj ((Sites.rnu A X).obj M)) ≫
        (Sites.nu B Z).map (closedMap φ i ((Sites.rnu A X).obj M) ≫
          (closedUpper B i).map (Sites.rnuScalar φ X M)) := by
  simp only [Sites.proClosedMap, Functor.map_comp]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_closed_comp_pro
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ)
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (M : Sites.D true A X)
    [IsIso (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj ((Sites.rnu A X).obj
        M)))]
    [IsIso (Etale.finiteCoefficientDirectImageMap χ i ((closedUpper A i).obj ((Sites.rnu A X).obj
        M)))]
    [IsIso (Etale.finiteCoefficientDirectImageMap ψ i ((closedUpper B i).obj
      ((Etale.scalarExtension φ X).obj ((Sites.rnu A X).obj M))))]
    [IsIso (Etale.finiteCoefficientDirectImageMap ψ i ((closedUpper B i).obj
      ((Sites.rnu B X).obj ((Sites.scalar true φ X).obj M))))] :
    (Sites.scalar true ψ Z).map (Sites.proClosedMap φ i M) ≫
        Sites.proClosedMap ψ i ((Sites.scalar true φ X).obj M) ≫
          (Sites.exceptional true C i).map ((Sites.comp true φ ψ χ h X).hom.app M) =
      (Sites.comp true φ ψ χ h Z).hom.app ((Sites.exceptional true A i).obj M) ≫
        Sites.proClosedMap χ i M := by
  let w := closedMap φ i ((Sites.rnu A X).obj M) ≫
    (closedUpper B i).map (Sites.rnuScalar φ X M)
  have hn := (Sites.scalarSite ψ Z).hom.naturality w
  dsimp only [Functor.comp_map, Sites.scalar, id_eq] at hn
  have hm := residual_closed_natural_etale ψ i
    (K := (Etale.scalarExtension φ X).obj ((Sites.rnu A X).obj M))
    (L := (Sites.rnu B X).obj ((Sites.scalar true φ X).obj M))
    (Sites.rnuScalar φ X M)
  have hc := residual_closed_comp_etale φ ψ χ h i ((Sites.rnu A X).obj M)
  have hr := residual_rnu_comp φ ψ χ h X M
  have hw :
      (Etale.scalarExtension ψ Z).map w ≫
        (closedMap ψ i ((Sites.rnu B X).obj ((Sites.scalar true φ X).obj M)) ≫
          (closedUpper C i).map (Sites.rnuScalar ψ X ((Sites.scalar true φ X).obj M))) ≫
        (closedUpper C i).map
          ((Sites.rnu C X).map ((Sites.comp true φ ψ χ h X).hom.app M)) =
      (ProEtale.pbcFixedScalarExtensionComp Z.smallEtaleTopology φ ψ χ h).hom.app ((closedUpper A
          i).obj ((Sites.rnu A X).obj M)) ≫
        (closedMap χ i ((Sites.rnu A X).obj M) ≫
          (closedUpper C i).map (Sites.rnuScalar χ X M)) := by
    dsimp only [w]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hm]
    rw [← (closedUpper C i).map_comp, ← (closedUpper C i).map_comp, hr]
    rw [Functor.map_comp]
    erw [reassoc_of% hc]
  simp only [Category.assoc] at hw
  rw [residual_pro_closed_def, residual_pro_closed_def, residual_pro_closed_def]
  change (Sites.scalar true ψ Z).map (_ ≫ (Sites.nu B Z).map w) ≫
    _ ≫ (Sites.nu C Z).map ((closedUpper C i).map
      ((Sites.rnu C X).map ((Sites.comp true φ ψ χ h X).hom.app M))) = _
  dsimp only [Sites.scalar, Sites.exceptional, id_eq, Functor.comp_map, Functor.comp_obj] at *
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  simp only [← (Sites.nu C Z).map_comp]
  rw [hw]
  simp only [CategoryTheory.Functor.map_comp]
  have ht := residual_site_comp φ ψ χ h Z ((closedUpper A i).obj ((Sites.rnu A X).obj M))
  dsimp only [Sites.scalar, id_eq] at ht
  rw [reassoc_of% ht]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_exceptional_comp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ)
    {X S : Scheme.{u}} [IsNoetherian S] {f : X ⟶ S} [HasCompactification f]
    (K : Cat A S) :
    (Etale.scalarExtension ψ X).map (Etale.ExceptionalCoefficients.mateMap φ f K) ≫
        Etale.ExceptionalCoefficients.mateMap ψ f ((Etale.scalarExtension φ S).obj K) ≫
          (Etale.rightDerivedUpperShriek C f).map
            ((ProEtale.pbcFixedScalarExtensionComp S.smallEtaleTopology φ ψ χ h).hom.app K) =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ h).hom.app
          ((Etale.rightDerivedUpperShriek A f).obj K) ≫
        Etale.ExceptionalCoefficients.mateMap χ f K := by
  let c := HasCompactification.compactification f
  let d := Etale.ExceptionalCoefficients.compactSupportIso φ c
  let e := Etale.ExceptionalCoefficients.compactSupportIso ψ c
  let k := Etale.ExceptionalCoefficients.compactSupportIso χ c
  have hc := Etale.FiniteSmoothPurity.compact_chain φ ψ χ h c
    ((Etale.rightDerivedUpperShriek A f).obj K)
  simp only [← Etale.ExceptionalCoefficients.compactSupportIso_hom_app] at hc
  change (ProEtale.pbcFixedScalarExtensionComp S.smallEtaleTopology φ ψ χ h).hom.app
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
        ((Etale.rightDerivedUpperShriek A f).obj K)) ≫
      k.hom.app ((Etale.rightDerivedUpperShriek A f).obj K) =
    (Etale.scalarExtension ψ S).map (d.hom.app ((Etale.rightDerivedUpperShriek A f).obj K)) ≫
      e.hom.app ((Etale.scalarExtension φ X).obj ((Etale.rightDerivedUpperShriek A f).obj K)) ≫
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} C) f).map
        ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ h).hom.app
          ((Etale.rightDerivedUpperShriek A f).obj K)) at hc
  have hi : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} C) f).map
        ((ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ h).hom.app
          ((Etale.rightDerivedUpperShriek A f).obj K)) ≫
        k.inv.app ((Etale.rightDerivedUpperShriek A f).obj K) =
      e.inv.app ((Etale.scalarExtension φ X).obj ((Etale.rightDerivedUpperShriek A f).obj K)) ≫
        (Etale.scalarExtension ψ S).map
          (d.inv.app ((Etale.rightDerivedUpperShriek A f).obj K)) ≫
        (ProEtale.pbcFixedScalarExtensionComp S.smallEtaleTopology φ ψ χ h).hom.app
          ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj
            ((Etale.rightDerivedUpperShriek A f).obj K)) := by
    exact residual_inverse_square
      ((Etale.scalarExtension ψ S).mapIso (d.app ((Etale.rightDerivedUpperShriek A f).obj K)))
      (e.app ((Etale.scalarExtension φ X).obj ((Etale.rightDerivedUpperShriek A f).obj K)))
      (k.app ((Etale.rightDerivedUpperShriek A f).obj K)) _ _ hc.symm
  have hm := Etale.ExceptionalCoefficients.mate_cocycle_at
    (Etale.rightDerivedUpperShriekAdjunction A f)
    (Etale.rightDerivedUpperShriekAdjunction B f)
    (Etale.rightDerivedUpperShriekAdjunction C f)
    (TwoSquare.mk _ _ _ _ d.inv) (TwoSquare.mk _ _ _ _ e.inv)
    (TwoSquare.mk _ _ _ _ k.inv) (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ h)
    (ProEtale.pbcFixedScalarExtensionComp S.smallEtaleTopology φ ψ χ h) K hi
  simpa only [Etale.ExceptionalCoefficients.mateMap_eq, d, e, k, c] using hm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_omega_comp_etale
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ)
    {X S : Scheme.{u}} [IsNoetherian S] {f : X ⟶ S} (c : Compactification f) :
    (Etale.scalarExtension ψ X).map (omegaMap φ c) ≫ omegaMap ψ c =
      (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ χ h).hom.app (omega A c) ≫
          omegaMap χ c := by
  let := c.hasCompactification
  have hn := (mateEquiv (Etale.rightDerivedUpperShriekAdjunction B f)
    (Etale.rightDerivedUpperShriekAdjunction C f)
    (TwoSquare.mk _ _ _ _ (Etale.ExceptionalCoefficients.compactSupportIso ψ
      (HasCompactification.compactification f)).inv)).natTrans.naturality
        (Etale.ExceptionalCoefficients.unitIso φ S).hom
  dsimp only [Functor.comp_map] at hn
  simp only [← Etale.ExceptionalCoefficients.mateMap_eq] at hn
  dsimp only [omegaMap, upper, Sites.scalar, id_eq]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← (Etale.rightDerivedUpperShriek C f).map_comp,
    Etale.normalizedScalarUnit_comp φ ψ χ h S]
  rw [Functor.map_comp]
  have hm := residual_exceptional_comp φ ψ χ h (f := f)
    (𝟙_ (Etale.DerivedCategoryModule A S))
  dsimp only [omega, upper] at *
  exact (reassoc_of% hm) ((Etale.rightDerivedUpperShriek C f).map
    (Etale.ExceptionalCoefficients.unitIso χ S).hom)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_omega_comp_pro
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    [Finite A] [Finite B] [Finite C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ)
    {X S : Scheme.{u}} [IsNoetherian S] {f : X ⟶ S} (c : Compactification f) :
    (Sites.scalar true ψ X).map (Sites.proOmegaMap φ c) ≫ Sites.proOmegaMap ψ c =
      (Sites.comp true φ ψ χ h X).hom.app (Sites.omega true A c) ≫
        Sites.proOmegaMap χ c := by
  subst χ
  have ha := (finite_ring_site_bridge_foundations A (𝟙 X) c).2
  have hb := (finite_ring_site_bridge_foundations B (𝟙 X) c).2
  have hc := (finite_ring_site_bridge_foundations C (𝟙 X) c).2
  have ht := CategoryTheory.CoefDualizingSiteMates.transport_cocycle
    (Sites.nu A X) (Sites.nu B X) (Sites.nu C X)
    (Etale.scalarExtension φ X) (Etale.scalarExtension ψ X) (Etale.scalarExtension (ψ.comp φ) X)
    (Sites.scalar true φ X) (Sites.scalar true ψ X) (Sites.scalar true (ψ.comp φ) X)
    (Sites.scalarSite φ X) (Sites.scalarSite ψ X) (Sites.scalarSite (ψ.comp φ) X)
    (ProEtale.pbcFixedScalarExtensionComp X.smallEtaleTopology φ ψ (ψ.comp φ) rfl) (Sites.comp true
        φ ψ (ψ.comp φ) rfl X)
    (ProEtale.CoefDualizingSiteMates.tensorCoherence φ ψ X)
    (asIso (Sites.omegaBridge A c)) (asIso (Sites.omegaBridge B c))
    (asIso (Sites.omegaBridge C c))
    (omegaMap φ c) (omegaMap ψ c) (omegaMap (ψ.comp φ) c)
    (residual_omega_comp_etale φ ψ (ψ.comp φ) rfl c)
  simpa only [CategoryTheory.CoefDualizingSiteMates.transport, Sites.proOmegaMap,
    Sites.inverseOnDomain, dif_pos ha, dif_pos hb, dif_pos hc,
    asIso_hom, asIso_inv] using ht

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_object_unit
    {C : Type*} [Category C] (F : C ⥤ C) (z : F ≅ 𝟭 C)
    (K : C) (v : F.obj K ⟶ K) [IsIso v]
    (h : F.map v ≫ v = z.hom.app (F.obj K) ≫ v) : v = z.hom.app K := by
  let : F.Faithful := Functor.Faithful.of_iso z.symm
  have hz : z.hom.app (F.obj K) = F.map (z.hom.app K) := by
    apply (cancel_mono (z.hom.app K)).1
    exact (z.hom.naturality (z.hom.app K)).symm
  exact F.map_injective (by simpa only [hz] using (cancel_mono v).1 h)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_tensor_comp
    (pro : Bool) {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ)
    (X : Scheme.{u}) (μφ : Sites.TensorComparison pro φ X)
    (μψ : Sites.TensorComparison pro ψ X) (μχ : Sites.TensorComparison pro χ X)
    (hφ : Sites.NormalizedTensor pro φ X μφ)
    (hψ : Sites.NormalizedTensor pro ψ X μψ)
    (hχ : Sites.NormalizedTensor pro χ X μχ) (K M : Sites.D pro A X) :
    (Sites.comp pro φ ψ χ h X).hom.app
        ((Functor.uncurry.obj (Sites.tensor pro A X)).obj (K, M)) ≫ μχ.hom.app (K, M) =
      (Sites.scalar pro ψ X).map (μφ.hom.app (K, M)) ≫
        μψ.hom.app ((Sites.scalar pro φ X).obj K, (Sites.scalar pro φ X).obj M) ≫
        (Functor.uncurry.obj (Sites.tensor pro C X)).map
          (Prod.mkHom ((Sites.comp pro φ ψ χ h X).hom.app K)
            ((Sites.comp pro φ ψ χ h X).hom.app M)) := by
  cases pro
  · have eφ := eq_of_heq hφ
    have eψ := eq_of_heq hψ
    have eχ := eq_of_heq hχ
    subst μφ; subst μψ; subst μχ
    simpa only [Sites.comp, Sites.scalar, Sites.tensor, id_eq, Functor.uncurry_obj_obj] using
      Etale.ExceptionalCoefficients.scalarTensor_comp φ ψ χ h X K M
  · obtain ⟨δφ, hnφ, heφ⟩ := hφ
    obtain ⟨δψ, hnψ, heψ⟩ := hψ
    obtain ⟨δχ, hnχ, heχ⟩ := hχ
    dsimp only [Sites.TensorComparison, Sites.tensor, Sites.scalar,
      ProEtale.derivedTensor, id_eq] at μφ μψ μχ
    have eφ : μφ = δφ := eq_of_heq heφ
    have eψ : μψ = δψ := eq_of_heq heψ
    have eχ : μχ = δχ := eq_of_heq heχ
    subst μφ; subst μψ; subst μχ
    simpa only [Sites.comp, Sites.scalar, Sites.tensor, ProEtale.derivedTensor,
      id_eq, Functor.uncurry_obj_obj, curriedTensor_obj_obj] using
      NormalizedSiteScalarTensor.scalar_tensor_comp (Scheme.ProEt.topology X)
        φ ψ χ h δφ δψ δχ hnφ hnψ hnχ K M

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_tensor_unit
    (pro : Bool) {A : Type (u + 1)} [CommRing A]
    (φ : A →+* A) (hφ : φ = RingHom.id A) (X : Scheme.{u})
    (μ : Sites.TensorComparison pro φ X) (hμ : Sites.NormalizedTensor pro φ X μ)
    (K M : Sites.D pro A X) :
    μ.hom.app (K, M) ≫ (Functor.uncurry.obj (Sites.tensor pro A X)).map
        (Prod.mkHom ((Sites.unit pro φ hφ X).hom.app K)
          ((Sites.unit pro φ hφ X).hom.app M)) =
      (Sites.unit pro φ hφ X).hom.app
        ((Functor.uncurry.obj (Sites.tensor pro A X)).obj (K, M)) := by
  subst φ
  apply Etale.ExceptionalCoefficients.tensor_identity_from_comp
    (Functor.uncurry.obj (Sites.tensor pro A X))
    (Sites.scalar pro (RingHom.id A) X) μ (Sites.unit pro (RingHom.id A) rfl X)
  intro U V
  have ht := residual_tensor_comp pro (RingHom.id A) (RingHom.id A) (RingHom.id A)
    (by ext; rfl) X μ μ μ hμ hμ hμ U V
  simpa only [residual_scalar_id_comp_app pro (RingHom.id A) rfl] using ht

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_hom_comp
    (pro : Bool) {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : χ = ψ.comp φ)
    (X : Scheme.{u}) (μφ : Sites.TensorComparison pro φ X)
    (μψ : Sites.TensorComparison pro ψ X) (μχ : Sites.TensorComparison pro χ X)
    (hφ : Sites.NormalizedTensor pro φ X μφ)
    (hψ : Sites.NormalizedTensor pro ψ X μψ)
    (hχ : Sites.NormalizedTensor pro χ X μχ) (K M : Sites.D pro A X) :
    (Sites.comp pro φ ψ χ h X).hom.app (((Sites.hom pro A X).obj (op K)).obj M) ≫
        Sites.homMap pro χ X μχ K M =
      (Sites.scalar pro ψ X).map (Sites.homMap pro φ X μφ K M) ≫
        Sites.homMap pro ψ X μψ ((Sites.scalar pro φ X).obj K)
          ((Sites.scalar pro φ X).obj M) ≫
        (Functor.uncurry.obj (Sites.hom pro C X)).map
          (Prod.mkHom ((Sites.comp pro φ ψ χ h X).inv.app K).op
            ((Sites.comp pro φ ψ χ h X).hom.app M)) := by
  simpa only [Sites.homMap, StageHomProof.homMap] using
    (ResidualHomProof.hom_tower (Sites.adj pro A X) (Sites.adj pro B X)
      (Sites.adj pro C X) (normalized_stage_site_evaluation_dinaturality pro C X)
      (Sites.scalar pro φ X) (Sites.scalar pro ψ X) (Sites.scalar pro χ X)
      μφ μψ μχ (Sites.comp pro φ ψ χ h X)
      (fun U V ↦ (residual_tensor_comp pro φ ψ χ h X μφ μψ μχ hφ hψ hχ U V).symm)
      K M).symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem residual_hom_unit
    (pro : Bool) {A : Type (u + 1)} [CommRing A]
    (φ : A →+* A) (hφ : φ = RingHom.id A) (X : Scheme.{u})
    (μ : Sites.TensorComparison pro φ X) (hμ : Sites.NormalizedTensor pro φ X μ)
    (K M : Sites.D pro A X) :
    Sites.homMap pro φ X μ K M ≫
        (Functor.uncurry.obj (Sites.hom pro A X)).map
          (Prod.mkHom ((Sites.unit pro φ hφ X).inv.app K).op
            ((Sites.unit pro φ hφ X).hom.app M)) =
      (Sites.unit pro φ hφ X).hom.app (((Sites.hom pro A X).obj (op K)).obj M) := by
  simpa only [Sites.homMap, StageHomProof.homMap] using
    ResidualHomProof.hom_unit (Sites.adj pro A X)
      (normalized_stage_site_evaluation_dinaturality pro A X) (Sites.scalar pro φ X) μ
      (Sites.unit pro φ hφ X) (residual_tensor_unit pro φ hφ X μ hμ) K M

/-- The naturality, unit, and composition equations, separated from pairing equations.
(blueprint: lem-sf-normalized-stage-comparison-residual). -/
structure StageComparisonResidual (pro : Bool)
    (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T X Z S : Scheme.{u}} (f : T ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    {aX : X ⟶ S} (c : Compactification aX)
    (μ : ∀ {s t : Stage l E} (a : Arrow s t), Sites.TensorComparison pro a.ringMap X) : Prop where
  closed_natural : pro = true → ∀ {s t : Stage l E} (a : Arrow s t)
      {K L : Sites.D pro s.ring X} (g : K ⟶ L),
    Sites.Ctf pro s.ring X K → Sites.Ctf pro s.ring X L →
      (Sites.scalar pro a.ringMap Z).map
          ((Sites.exceptional pro s.ring i).map g) ≫
        Sites.stageClosedMap pro a i L =
      Sites.stageClosedMap pro a i K ≫
        (Sites.exceptional pro t.ring i).map
          ((Sites.scalar pro a.ringMap X).map g)
  direct_unit : ∀ (s : Stage l E) (a : Arrow s s)
      (h : a.embedding = AlgHom.id (Padic l) s.field) (K : Sites.D pro s.ring T),
    Sites.Ctf pro s.ring T K → Sites.direct pro a.ringMap f K ≫
      (Sites.push pro s.ring f).map
        ((Sites.unit pro a.ringMap (Arrow.ringMap_id a h) T).hom.app K) =
      (Sites.unit pro a.ringMap (Arrow.ringMap_id a h) X).hom.app
        ((Sites.push pro s.ring f).obj K)
  closed_unit : ∀ (s : Stage l E) (a : Arrow s s)
      (h : a.embedding = AlgHom.id (Padic l) s.field) (M : Sites.D pro s.ring X),
    Sites.Ctf pro s.ring X M → Sites.stageClosedMap pro a i M ≫
      (Sites.exceptional pro s.ring i).map
        ((Sites.unit pro a.ringMap (Arrow.ringMap_id a h) X).hom.app M) =
      (Sites.unit pro a.ringMap (Arrow.ringMap_id a h) Z).hom.app
        ((Sites.exceptional pro s.ring i).obj M)
  omega_unit : ∀ (s : Stage l E) (a : Arrow s s)
      (h : a.embedding = AlgHom.id (Padic l) s.field),
    Sites.stageOmegaMap pro a c =
      (Sites.unit pro a.ringMap (Arrow.ringMap_id a h) X).hom.app
        (Sites.omega pro s.ring c)
  hom_unit : ∀ (s : Stage l E) (a : Arrow s s)
      (h : a.embedding = AlgHom.id (Padic l) s.field)
      (K M : Sites.D pro s.ring X), Sites.Ctf pro s.ring X K →
      Sites.Ctf pro s.ring X M →
      Sites.homMap pro a.ringMap X (μ a) K M ≫
        (Functor.uncurry.obj (Sites.hom pro s.ring X)).map
          (Prod.mkHom
            ((Sites.unit pro a.ringMap (Arrow.ringMap_id a h) X).inv.app K).op
            ((Sites.unit pro a.ringMap (Arrow.ringMap_id a h) X).hom.app M)) =
      (Sites.unit pro a.ringMap (Arrow.ringMap_id a h) X).hom.app
        (((Sites.hom pro s.ring X).obj (op K)).obj M)
  closed_comp : ∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v)
      (ab : Arrow s v) (h : ab.embedding = b.embedding.comp a.embedding)
      (M : Sites.D pro s.ring X), Sites.Ctf pro s.ring X M →
      (Sites.scalar pro b.ringMap Z).map (Sites.stageClosedMap pro a i M) ≫
        Sites.stageClosedMap pro b i ((Sites.scalar pro a.ringMap X).obj M) ≫
          (Sites.exceptional pro v.ring i).map
            ((Sites.comp pro a.ringMap b.ringMap ab.ringMap
              (Arrow.ringMap_comp a b ab h) X).hom.app M) =
      (Sites.comp pro a.ringMap b.ringMap ab.ringMap
        (Arrow.ringMap_comp a b ab h) Z).hom.app
          ((Sites.exceptional pro s.ring i).obj M) ≫ Sites.stageClosedMap pro ab i M
  omega_comp : ∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v)
      (ab : Arrow s v) (h : ab.embedding = b.embedding.comp a.embedding),
    (Sites.scalar pro b.ringMap X).map (Sites.stageOmegaMap pro a c) ≫
      Sites.stageOmegaMap pro b c =
      (Sites.comp pro a.ringMap b.ringMap ab.ringMap
        (Arrow.ringMap_comp a b ab h) X).hom.app (Sites.omega pro s.ring c) ≫
        Sites.stageOmegaMap pro ab c
  hom_comp : ∀ {s t v : Stage l E} (a : Arrow s t) (b : Arrow t v)
      (ab : Arrow s v) (h : ab.embedding = b.embedding.comp a.embedding)
      (K M : Sites.D pro s.ring X), Sites.Ctf pro s.ring X K →
      Sites.Ctf pro s.ring X M →
      (Sites.comp pro a.ringMap b.ringMap ab.ringMap
        (Arrow.ringMap_comp a b ab h) X).hom.app
          (((Sites.hom pro s.ring X).obj (op K)).obj M) ≫
        Sites.homMap pro ab.ringMap X (μ ab) K M =
      (Sites.scalar pro b.ringMap X).map
          (Sites.homMap pro a.ringMap X (μ a) K M) ≫
        Sites.homMap pro b.ringMap X (μ b)
          ((Sites.scalar pro a.ringMap X).obj K)
          ((Sites.scalar pro a.ringMap X).obj M) ≫
        (Functor.uncurry.obj (Sites.hom pro v.ring X)).map
          (Prod.mkHom
            ((Sites.comp pro a.ringMap b.ringMap ab.ringMap
              (Arrow.ringMap_comp a b ab h) X).inv.app K).op
            ((Sites.comp pro a.ringMap b.ringMap ab.ringMap
              (Arrow.ringMap_comp a b ab h) X).hom.app M))

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The fixed maps satisfy naturality, unit, and coefficient-composition coherence.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 2--3;
(blueprint: lem-sf-normalized-stage-comparison-residual).

Proof: the coefficient projection formula gives the direct-image cocycle. At the
constructible objects in question the direct comparison is invertible, so transpose
its inverse under the closed adjunction. Counit naturality and mate pasting give closed
naturality and composition. On the pro-etale site paste this with the right-mate
cocycle for the site comparison. The compact-support cocycle similarly gives the
exceptional cocycle; evaluation at the unit and normalizedScalarUnit_comp give the
dualizing equation, which transports across the invertible dualizing site bridges.
The normalized tensorator cocycle, on either site, gives Hom composition by
transposition against evaluation and its dinaturality. Finally specialize all
cocycles to identity arrows and cancel the comparison isomorphisms to obtain units. -/
theorem normalized_stage_comparison_residual
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T X Z : Scheme.{u})
    [T.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))] [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    (f : T ⟶ X) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of D.k))]
    (c : Compactification (X ↘ Spec (.of D.k)))
    (μ : ∀ pro : Bool, ∀ {s t : Stage l E} (a : Arrow s t),
      Sites.TensorComparison pro a.ringMap X)
    (hμ : ∀ (pro : Bool) {s t : Stage l E} (a : Arrow s t),
      Sites.NormalizedTensor pro a.ringMap X (μ pro a))
    (σ : ∀ (pro : Bool) (s : Stage l E),
      Sites.tensor pro s.ring X ≅ (Sites.tensor pro s.ring X).flip)
    (hσ : ∀ (pro : Bool) (s : Stage l E),
      Sites.NormalizedSymmetry pro s.ring X (σ pro s))
    (hi : ∀ pro : Bool, Sites.StageComparisonIsomorphisms pro l E f i c (μ pro))
    (hsi : letI := c.hasCompactification
      Sites.StageComparisonSiteIsomorphisms l E f i c) :
    ∀ pro : Bool, StageComparisonResidual pro l E f i c (μ pro) := by
  have _ := hl
  have _ := hσ
  let := c.hasCompactification
  have hs (pro : Bool) {s t : Stage l E} (a : Arrow s t)
      (M : Sites.D pro s.ring X) (hM : Sites.Ctf pro s.ring X M) :
      Sites.Ctf pro t.ring X ((Sites.scalar pro a.ringMap X).obj M) :=
    (finite_ring_scalar_direct_foundations D a.ringMap T X f).2.1 pro M hM
  have hn (pro : Bool) {s t : Stage l E} (a : Arrow s t)
      {K L : Sites.D pro s.ring X} (g : K ⟶ L)
      (hK : Sites.Ctf pro s.ring X K) (hL : Sites.Ctf pro s.ring X L) :
      (Sites.scalar pro a.ringMap Z).map ((Sites.exceptional pro s.ring i).map g) ≫
          Sites.stageClosedMap pro a i L =
        Sites.stageClosedMap pro a i K ≫
          (Sites.exceptional pro t.ring i).map ((Sites.scalar pro a.ringMap X).map g) := by
    cases pro
    · have := hsi.closed_direct_iso a K hK
      have := hsi.closed_direct_iso a L hL
      simpa only [Sites.scalar, Sites.exceptional, Sites.stageClosedMap, id_eq] using
        residual_closed_natural_etale a.ringMap i g
    · have := hsi.closed_direct_iso a ((Sites.rnu s.ring X).obj K) (residual_rnu_ctf X K hK)
      have := hsi.closed_direct_iso a ((Sites.rnu s.ring X).obj L) (residual_rnu_ctf X L hL)
      simpa only [Sites.stageClosedMap] using residual_closed_natural_pro a.ringMap i g
  have hc (pro : Bool) {s t r : Stage l E} (a : Arrow s t) (b : Arrow t r)
      (ab : Arrow s r) (h : ab.embedding = b.embedding.comp a.embedding)
      (M : Sites.D pro s.ring X) (hM : Sites.Ctf pro s.ring X M) :
      (Sites.scalar pro b.ringMap Z).map (Sites.stageClosedMap pro a i M) ≫
          Sites.stageClosedMap pro b i ((Sites.scalar pro a.ringMap X).obj M) ≫
          (Sites.exceptional pro r.ring i).map
            ((Sites.comp pro a.ringMap b.ringMap ab.ringMap
              (Arrow.ringMap_comp a b ab h) X).hom.app M) =
        (Sites.comp pro a.ringMap b.ringMap ab.ringMap
          (Arrow.ringMap_comp a b ab h) Z).hom.app ((Sites.exceptional pro s.ring i).obj M) ≫
          Sites.stageClosedMap pro ab i M := by
    cases pro
    · have := hsi.closed_direct_iso a M hM
      have := hsi.closed_direct_iso ab M hM
      have : IsIso (Etale.finiteCoefficientDirectImageMap b.ringMap i
          ((closedUpper t.ring i).obj ((Etale.scalarExtension a.ringMap X).obj M))) :=
        hsi.closed_direct_iso b ((Etale.scalarExtension a.ringMap X).obj M) (hs false a M hM)
      simpa only [Sites.scalar, Sites.comp, Sites.exceptional, Sites.stageClosedMap, id_eq] using
        residual_closed_comp_etale a.ringMap b.ringMap ab.ringMap
          (Arrow.ringMap_comp a b ab h) i M
    · have hR := residual_rnu_ctf X M hM
      have := hsi.closed_direct_iso a ((Sites.rnu s.ring X).obj M) hR
      have := hsi.closed_direct_iso ab ((Sites.rnu s.ring X).obj M) hR
      have : IsIso (Etale.finiteCoefficientDirectImageMap b.ringMap i
          ((closedUpper t.ring i).obj
            ((Etale.scalarExtension a.ringMap X).obj ((Sites.rnu s.ring X).obj M)))) :=
        hsi.closed_direct_iso b
          ((Etale.scalarExtension a.ringMap X).obj ((Sites.rnu s.ring X).obj M))
          (hs false a ((Sites.rnu s.ring X).obj M) hR)
      have := hsi.closed_direct_iso b
        ((Sites.rnu t.ring X).obj ((Sites.scalar true a.ringMap X).obj M))
        (residual_rnu_ctf X _ (hs true a M hM))
      simpa only [Sites.stageClosedMap, Sites.scalar, id_eq] using
        residual_closed_comp_pro a.ringMap b.ringMap ab.ringMap
          (Arrow.ringMap_comp a b ab h) i M
  have ho (pro : Bool) {s t r : Stage l E} (a : Arrow s t) (b : Arrow t r)
      (ab : Arrow s r) (h : ab.embedding = b.embedding.comp a.embedding) :
      (Sites.scalar pro b.ringMap X).map (Sites.stageOmegaMap pro a c) ≫
          Sites.stageOmegaMap pro b c =
        (Sites.comp pro a.ringMap b.ringMap ab.ringMap
          (Arrow.ringMap_comp a b ab h) X).hom.app (Sites.omega pro s.ring c) ≫
          Sites.stageOmegaMap pro ab c := by
    cases pro
    · simpa only [Sites.scalar, Sites.comp, Sites.omega, Sites.upper, Sites.one,
        Sites.stageOmegaMap, id_eq, omega] using
        residual_omega_comp_etale a.ringMap b.ringMap ab.ringMap
          (Arrow.ringMap_comp a b ab h) c
    · simpa only [Sites.stageOmegaMap] using
        residual_omega_comp_pro a.ringMap b.ringMap ab.ringMap
          (Arrow.ringMap_comp a b ab h) c
  intro pro
  refine {
    closed_natural := fun _ {_ _} a {_ _} g hK hL ↦ hn pro a g hK hL
    direct_unit := ?_
    closed_unit := ?_
    omega_unit := ?_
    hom_unit := ?_
    closed_comp := hc pro
    omega_comp := ho pro
    hom_comp := ?_ }
  · intro s a h K hK
    have := (finite_ring_scalar_direct_foundations D a.ringMap T X f).2.2 pro K hK
    exact residual_direct_unit pro a.ringMap (Arrow.ringMap_id a h) f K
  · intro s a h M hM
    have := (hi pro).closed_iso a M hM
    apply residual_unit_at (Sites.exceptional pro s.ring i)
      (Sites.scalar pro a.ringMap X) (Sites.scalar pro a.ringMap Z)
      (Sites.unit pro a.ringMap (Arrow.ringMap_id a h) X)
      (Sites.unit pro a.ringMap (Arrow.ringMap_id a h) Z) M
      (Sites.stageClosedMap pro a i M)
      (Sites.stageClosedMap pro a i ((Sites.scalar pro a.ringMap X).obj M))
    · exact hn pro a ((Sites.unit pro a.ringMap (Arrow.ringMap_id a h) X).hom.app M)
        (hs pro a M hM) hM
    · have hab : a.embedding = a.embedding.comp a.embedding := by simp [h]
      have hh := hc pro a a a hab M hM
      simpa only [residual_scalar_id_comp_app pro a.ringMap (Arrow.ringMap_id a h)]
        using hh.symm
  · intro s a h
    have := (hi pro).omega_iso a
    apply residual_object_unit (Sites.scalar pro a.ringMap X)
      (Sites.unit pro a.ringMap (Arrow.ringMap_id a h) X)
      (Sites.omega pro s.ring c) (Sites.stageOmegaMap pro a c)
    have hab : a.embedding = a.embedding.comp a.embedding := by simp [h]
    have hh := ho pro a a a hab
    simpa only [residual_scalar_id_comp_app pro a.ringMap (Arrow.ringMap_id a h)] using hh
  · intro s a h K M _ _
    exact residual_hom_unit pro a.ringMap (Arrow.ringMap_id a h) X (μ pro a) (hμ pro a) K M
  · intro s t r a b ab h K M _ _
    exact residual_hom_comp pro a.ringMap b.ringMap ab.ringMap
      (Arrow.ringMap_comp a b ab h) X (μ pro a) (μ pro b) (μ pro ab)
      (hμ pro a) (hμ pro b) (hμ pro ab) K M

end WeilConjectures.FiniteFreeCoefficients
