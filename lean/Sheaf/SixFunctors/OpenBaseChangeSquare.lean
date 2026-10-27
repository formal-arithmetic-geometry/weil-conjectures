/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.SixFunctors.OpenBaseChangeSquareData
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.PullbackTorAmplitude
import Sheaf.Paper.FiniteCoefficientTensorCtf
import all Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.ProEtaleConstantModuleConstructibility
import Sheaf.SixFunctors.FiniteOpenCartesianCalculus
import Sheaf.SixFunctors.CompletedOpenCartesianIdentity
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations

/-! # Open projection/base-change square

The canonical square comparisons are monoidal, and the finite and completed
open identities hold on their constructible domains.
(blueprint: lem-sf-pf-open-base-change-square)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped MonoidalCategory
namespace WeilConjectures.OpenProjectionBaseChange
variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
variable (E : Type u) [Field E] [Algebra ℚ_[c.l] E] [FiniteDimensional ℚ_[c.l] E]
variable (n : ℕ)

attribute [local irreducible] canonicalFinitePullbackTensor finiteIntrinsicClosed
  finiteIntrinsicTensorModels canonicalIntegralPullbackTensor

private theorem tensor_square_of_composition
    {C : Type*} {B : Type*} [Category C] [Category B]
    (TC : C × C ⥤ C) (TB : B × B ⥤ B)
    {U F G : C ⥤ B} (a : U ≅ F) (b : U ≅ G) (X Y : C)
    (mU : U.obj (TC.obj (X, Y)) ⟶ TB.obj (U.obj X, U.obj Y))
    (mF : F.obj (TC.obj (X, Y)) ⟶ TB.obj (F.obj X, F.obj Y))
    (mG : G.obj (TC.obj (X, Y)) ⟶ TB.obj (G.obj X, G.obj Y))
    (ha : mU ≫ TB.map (Prod.mkHom (a.hom.app X) (a.hom.app Y)) =
      a.hom.app (TC.obj (X, Y)) ≫ mF)
    (hb : mU ≫ TB.map (Prod.mkHom (b.hom.app X) (b.hom.app Y)) =
      b.hom.app (TC.obj (X, Y)) ≫ mG) :
    (a.symm ≪≫ b).hom.app (TC.obj (X, Y)) ≫ mG =
      mF ≫ TB.map (Prod.mkHom ((a.symm ≪≫ b).hom.app X)
        ((a.symm ≪≫ b).hom.app Y)) := by
  apply (cancel_epi (a.hom.app (TC.obj (X, Y)))).1
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, ← ha, Category.assoc, ← TB.map_comp]
  simpa only [prod_comp, Iso.hom_inv_id_app_assoc] using hb.symm

private theorem tensor_square_associated
    {C B : Type*} [Category C] [Category B]
    (TC : C × C ⥤ C) (TB : B × B ⥤ B)
    {U F G : C ⥤ B} (a : U ≅ F) (b : U ≅ G) (X Y : C)
    (mU : U.obj (TC.obj (X, Y)) ⟶ TB.obj (U.obj X, U.obj Y))
    {Z₁ Z₂ : B} (f₁ : F.obj (TC.obj (X, Y)) ⟶ Z₁)
    (f₂ : Z₁ ⟶ TB.obj (F.obj X, F.obj Y))
    (g₁ : G.obj (TC.obj (X, Y)) ⟶ Z₂)
    (g₂ : Z₂ ⟶ TB.obj (G.obj X, G.obj Y))
    (ha : mU ≫ TB.map (Prod.mkHom (a.hom.app X) (a.hom.app Y)) =
      a.hom.app (TC.obj (X, Y)) ≫ f₁ ≫ f₂)
    (hb : mU ≫ TB.map (Prod.mkHom (b.hom.app X) (b.hom.app Y)) =
      b.hom.app (TC.obj (X, Y)) ≫ g₁ ≫ g₂) :
    (a.symm ≪≫ b).hom.app (TC.obj (X, Y)) ≫ g₁ ≫ g₂ =
      f₁ ≫ f₂ ≫ TB.map (Prod.mkHom ((a.symm ≪≫ b).hom.app X)
        ((a.symm ≪≫ b).hom.app Y)) := by
  simpa only [Category.assoc] using
    tensor_square_of_composition TC TB a b X Y mU (f₁ ≫ f₂) (g₁ ≫ g₂) ha hb


set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Scheme.residueField

private theorem tensor_comparison_eq
    {C B I : Type*} [Category C] [Category B]
    (TC : C × C ⥤ C) (TB : B × B ⥤ B) (F : I → C ⥤ B)
    (m : ∀ i X Y, (F i).obj (TC.obj (X, Y)) ⟶ TB.obj ((F i).obj X, (F i).obj Y))
    {i j : I} (e : i = j) (X Y : C) :
    m i X Y ≫ TB.map (Prod.mkHom ((eqToIso (congrArg F e)).hom.app X)
      ((eqToIso (congrArg F e)).hom.app Y)) =
      (eqToIso (congrArg F e)).hom.app (TC.obj (X, Y)) ≫ m j X Y := by
  cases e
  simp

private theorem tensor_comparison_trans
    {C B : Type*} [Category C] [Category B]
    (TC : C × C ⥤ C) (TB : B × B ⥤ B)
    {U F G : C ⥤ B} (a : U ≅ F) (b : F ≅ G) (X Y : C)
    (mU : U.obj (TC.obj (X, Y)) ⟶ TB.obj (U.obj X, U.obj Y))
    (mF : F.obj (TC.obj (X, Y)) ⟶ TB.obj (F.obj X, F.obj Y))
    (mG : G.obj (TC.obj (X, Y)) ⟶ TB.obj (G.obj X, G.obj Y))
    (ha : mU ≫ TB.map (Prod.mkHom (a.hom.app X) (a.hom.app Y)) =
      a.hom.app (TC.obj (X, Y)) ≫ mF)
    (hb : mF ≫ TB.map (Prod.mkHom (b.hom.app X) (b.hom.app Y)) =
      b.hom.app (TC.obj (X, Y)) ≫ mG) :
    mU ≫ TB.map (Prod.mkHom ((a ≪≫ b).hom.app X) ((a ≪≫ b).hom.app Y)) =
      (a ≪≫ b).hom.app (TC.obj (X, Y)) ≫ mG := by
  simp only [Iso.trans_hom, NatTrans.comp_app]
  change mU ≫ TB.map ((Prod.mkHom (a.hom.app X) (a.hom.app Y)) ≫
    Prod.mkHom (b.hom.app X) (b.hom.app Y)) = _
  rw [TB.map_comp]
  rw [← Category.assoc, ha]
  simp only [Category.assoc]
  rw [hb]

private theorem monoidality_of_eq_composition
    {D₁ D₂ D₃ D₄ : Type*} [Category D₁] [Category D₂] [Category D₃] [Category D₄]
    (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
    (T₃ : D₃ × D₃ ⥤ D₃) (T₄ : D₄ × D₄ ⥤ D₄)
    (F : D₁ ⥤ D₂) (F' : D₃ ⥤ D₄) (G : D₁ ⥤ D₃) (H : D₂ ⥤ D₄)
    (muF : ∀ B C, F.obj (T₁.obj (B, C)) ≅ T₂.obj (F.obj B, F.obj C))
    (muF' : ∀ B C, F'.obj (T₃.obj (B, C)) ≅ T₄.obj (F'.obj B, F'.obj C))
    (muG : ∀ B C, G.obj (T₁.obj (B, C)) ≅ T₃.obj (G.obj B, G.obj C))
    (muH : ∀ B C, H.obj (T₂.obj (B, C)) ≅ T₄.obj (H.obj B, H.obj C))
    {I : Type*} (W : I → D₁ ⥤ D₄)
    (mW : ∀ i B C, (W i).obj (T₁.obj (B, C)) ⟶ T₄.obj ((W i).obj B, (W i).obj C))
    {i j : I} (w : i = j) (a : W i ≅ G ⋙ F') (b : W j ≅ F ⋙ H)
    (ha : ∀ B C, mW i B C ≫ T₄.map (Prod.mkHom (a.hom.app B) (a.hom.app C)) =
      a.hom.app (T₁.obj (B, C)) ≫ F'.map (muG B C).hom ≫
        (muF' (G.obj B) (G.obj C)).hom)
    (hb : ∀ B C, mW j B C ≫ T₄.map (Prod.mkHom (b.hom.app B) (b.hom.app C)) =
      b.hom.app (T₁.obj (B, C)) ≫ H.map (muF B C).hom ≫
        (muH (F.obj B) (F.obj C)).hom)
    : Monoidality T₁ T₂ T₃ T₄ F F' G H (a.symm ≪≫ eqToIso (congrArg W w) ≪≫ b)
      muF muF' muG muH := by
  intro B C
  exact tensor_square_associated T₁ T₄ a (eqToIso (congrArg W w) ≪≫ b) B C (mW i B C)
    (F'.map (muG B C).hom) (muF' (G.obj B) (G.obj C)).hom
    (H.map (muF B C).hom) (muH (F.obj B) (F.obj C)).hom (ha B C)
      (tensor_comparison_trans T₁ T₄ (eqToIso (congrArg W w)) b B C
        (mW i B C) (mW j B C) _ (tensor_comparison_eq T₁ T₄ W mW w B C) (hb B C))


private theorem map_derived_eq
    {C B I : Type*} [Category C] [Category B] [Abelian C] [Abelian B]
    [HasDerivedCategory C] [HasDerivedCategory B]
    (F : I → C ⥤ B) [∀ i, (F i).Additive]
    [∀ i, PreservesFiniteLimits (F i)] [∀ i, PreservesFiniteColimits (F i)]
    {i j : I} (e : i = j) :
    (Functor.mapDerivedCategoryNatIso (eqToIso (congrArg F e))).hom =
      (eqToIso (congrArg (fun i ↦ (F i).mapDerivedCategory) e)).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem finite_square_comparison
    (A : Type u) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (a : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (h : X' ⟶ X) (w : a ≫ j = j' ≫ h) :
    sfIntrinsicDerivedSquarePullback A a j' j h w =
      (sfIntrinsicDerivedPullbackComp A a j).symm ≪≫
        eqToIso (congrArg (sfIntrinsicDerivedPullback A) w) ≪≫
          sfIntrinsicDerivedPullbackComp A j' h := by
  apply Iso.ext
  simp only [sfIntrinsicDerivedSquarePullback, sfIntrinsicSquarePullback,
    sfIntrinsicDerivedPullbackComp, Iso.trans_hom, Iso.symm_hom,
    Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_symm, Iso.trans_assoc, Category.assoc]
  rw [map_derived_eq
    (C := proEtaleRingModules X (proEtaleConstantRing X A))
    (B := proEtaleRingModules U' (proEtaleConstantRing U' A))
    (fun f : U' ⟶ X ↦ sfIntrinsicPullback A f) w]

private theorem finite_monoidality (Q : SixFunctorCompactifiedSquare D) :
    Monoidality
      (finiteIntrinsicDerivedTensor c.l E Q.Y.obj.left n)
      (finiteIntrinsicDerivedTensor c.l E Q.Z.obj.left n)
      (finiteIntrinsicDerivedTensor c.l E Q.Y'.obj.left n)
      (finiteIntrinsicDerivedTensor c.l E Q.Z'.obj.left n)
      (finiteDerivedPullback c.l E n Q.p.hom.left)
      (finiteDerivedPullback c.l E n Q.p'.hom.left)
      (finiteDerivedPullback c.l E n Q.g.hom.left)
      (finiteDerivedPullback c.l E n Q.h.hom.left)
      (finiteTheta D c E n Q)
      (finiteMu D c E Q.p n) (finiteMu D c E Q.p' n)
      (finiteMu D c E Q.g n) (finiteMu D c E Q.h n) := by
  intro B C
  let a := eqToIso (congrArg (finiteDerivedPullback c.l E n) Q.properSquare.w) ≪≫
    sfIntrinsicDerivedPullbackComp (finiteCoefficientRing c.l E (n + 1))
      Q.p'.hom.left Q.g.hom.left
  let b := sfIntrinsicDerivedPullbackComp (finiteCoefficientRing c.l E (n + 1))
    Q.h.hom.left Q.p.hom.left
  have he : finiteTheta D c E n Q = a.symm ≪≫ b := by
    rw [finiteTheta, finite_square_comparison]
    simp only [a, b, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  change (finiteTheta D c E n Q).hom.app _ ≫ _ = _
  rw [he]
  simpa only [finiteMu, Category.assoc] using
    tensor_square_of_composition _ _ a b B C _ _ _
    (tensor_comparison_trans _ _ _ _ B C _ _ _
      (tensor_comparison_eq _ _ (finiteDerivedPullback c.l E n)
        (fun f B C ↦ (@canonicalFinitePullbackTensor c.l _ E _ _ _
          Q.Z'.obj.left Q.Y.obj.left f n (units D c Q.Z') (units D c Q.Y) B C).hom)
        Q.properSquare.w B C)
      (@canonicalFinitePullbackTensor_composition c.l _ E _ _ _ Q.Y'.obj.left
        Q.Y.obj.left Q.Z'.obj.left Q.g.hom.left Q.p'.hom.left n
          (units D c Q.Y') (units D c Q.Y) (units D c Q.Z') B C))
    (@canonicalFinitePullbackTensor_composition c.l _ E _ _ _ Q.Z.obj.left
      Q.Y.obj.left Q.Z'.obj.left Q.p.hom.left Q.h.hom.left n
        (units D c Q.Z) (units D c Q.Y) (units D c Q.Z') B C)


private theorem integral_composition
    {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (h : Z ⟶ X)
    (B C : sfIntegralConstructibleCategory c.l E Y.obj.left) :
    let := units D c X
    let := units D c Y
    let := units D c Z
    @canonicalIntegralPullbackTensor_composition c.l _ E _ _ _ X.obj.left Y.obj.left
      Z.obj.left f.hom.left h.hom.left (units D c X) (units D c Y) (units D c Z) B C :=
  (@derivedPullbackTensorIso c.l _ E _ _ _ X.obj.left Y.obj.left f.hom.left 0
    (units D c X) (units D c Y) c.Qbar (inferInstance) (inferInstance)
      (inferInstance)).2.2.2.2.2.2.2.2.2.1
      (hZ := units D c Z) h.hom.left B C

attribute [local irreducible] pullbackTensorIntegralComposition
  constructibleIntegralPullback constructibleIntegralTensor integralDerivedPullback
  integralCompletedTensor



private theorem integral_monoidality (Q : SixFunctorCompactifiedSquare D) :
    Monoidality
      (integralTensor D c E Q.Y) (integralTensor D c E Q.Z)
      (integralTensor D c E Q.Y') (integralTensor D c E Q.Z')
      (integralPull D c E Q.p) (integralPull D c E Q.p')
      (integralPull D c E Q.g) (integralPull D c E Q.h)
      (integralTheta D c E Q)
      (integralMu D c E Q.p) (integralMu D c E Q.p')
      (integralMu D c E Q.g) (integralMu D c E Q.h) := by
  exact monoidality_of_eq_composition
    (integralTensor D c E Q.Y) (integralTensor D c E Q.Z)
    (integralTensor D c E Q.Y') (integralTensor D c E Q.Z')
    (integralPull D c E Q.p) (integralPull D c E Q.p')
    (integralPull D c E Q.g) (integralPull D c E Q.h)
    (integralMu D c E Q.p) (integralMu D c E Q.p')
    (integralMu D c E Q.g) (integralMu D c E Q.h)
    (fun k ↦ @constructibleIntegralPullback c.l _ E _ _ _ Q.Z'.obj.left
      Q.Y.obj.left k (units D c Q.Z') (units D c Q.Y))
    (fun k B C ↦ (@canonicalIntegralPullbackTensor c.l _ E _ _ _ Q.Z'.obj.left
      Q.Y.obj.left k (units D c Q.Z') (units D c Q.Y) B C).hom)
    Q.properSquare.w.symm
    (@pullbackTensorIntegralComposition c.l _ E _ _ _ Q.Y'.obj.left Q.Y.obj.left
      Q.Z'.obj.left Q.g.hom.left Q.p'.hom.left (units D c Q.Y') (units D c Q.Y)
        (units D c Q.Z'))
    (@pullbackTensorIntegralComposition c.l _ E _ _ _ Q.Z.obj.left Q.Y.obj.left
      Q.Z'.obj.left Q.p.hom.left Q.h.hom.left (units D c Q.Z) (units D c Q.Y)
        (units D c Q.Z'))
    (integral_composition D c E Q.g Q.p') (integral_composition D c E Q.p Q.h)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


private theorem integral_domains
    (ops : SixFunctorDatum D c E (n + 1) (Nat.succ_pos n))
    (Q : SixFunctorCompactifiedSquare D) (d : IntegralMaps.{u} D c E Q)
    (K : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.X.obj.left))
    (L : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.Y.obj.left))
    (hK : sfIntegralConstructible c.l E Q.X.obj.left K)
    (hL : sfIntegralConstructible c.l E Q.Y.obj.left L) :
    IntegralDomains.{u} D c E Q K L := by
  let := Q.open_i
  let := Q.open_i'
  have hp {X Y : SixFunctorSpace D} (f : X ⟶ Y) (N)
      (hN : sfIntegralConstructible c.l E Y.obj.left N) :
      sfIntegralConstructible c.l E X.obj.left
        ((integralDerivedPullback.{u, u} c.l E f.hom.left).obj N) :=
    (@integralOperations_preserve_constructible c.l _ E _ _ _ X.obj.left Y.obj.left
      f.hom.left (units D c X) (units D c Y)).1 N hN |>.1
  have ht (X : SixFunctorSpace D) (M N)
      (hM : sfIntegralConstructible c.l E X.obj.left M)
      (hN : sfIntegralConstructible c.l E X.obj.left N) :
      sfIntegralConstructible c.l E X.obj.left
        ((integralCompletedTensor.{u, u} c.l E X.obj.left).obj (M, N)) :=
    (@integralOperations_preserve_constructible c.l _ E _ _ _ X.obj.left X.obj.left
      (𝟙 _) (units D c X) (units D c X)).2 X.obj.left (.inl rfl) M N hM hN |>.1
  have hs {X Y : SixFunctorSpace D} (f : X ⟶ Y) (N)
      (hN : sfIntegralConstructible c.l E X.obj.left N) :
      sfIntegralConstructible c.l E Y.obj.left
        ((sfCompletedDerivedDirectImage.{u} c.l E f.hom.left).obj N) :=
    (sfIntegralConstructible c.l E Y.obj.left).prop_of_iso
      ((ops.higher.integralDirectImage f).app ⟨N, hN⟩)
      ((ops.higher.integral.direct f).obj ⟨N, hN⟩).property
  have hM := d.1.openData.constructible K hK
  have hP := hp Q.p L hL
  have hQ := ht Q.Z _ _ hM hP
  have hJP := d.1.openData.restriction_constructible _ hP
  have hV := ht Q.X _ _ hK hJP
  have hAK := hp Q.g' K hK
  have hHP := hp Q.h _ hP
  have hHM := hp Q.h _ hM
  have hHQ := hp Q.h _ hQ
  have hAJP := hp Q.g' _ hJP
  have hAV := hp Q.g' _ hV
  have hJHP := d.1.openData'.restriction_constructible _ hHP
  have hW := ht Q.X' _ _ hAK hJHP
  have heV := d.1.openData.constructible _ hV
  have heAV := d.1.openData'.constructible _ hAV
  have heAK := d.1.openData'.constructible _ hAK
  have heW := d.1.openData'.constructible _ hW
  exact ⟨hM, hP, hQ, hJP, hV, hAK, hHP, hHM, hHQ, hAJP, hAV, hJHP, hW,
    heV, heAV, heAK, heW, hs Q.p _ hM, hs Q.p _ hQ, hs Q.p' _ hHM,
    hs Q.p' _ hHQ, hp Q.h _ heV, ht Q.Z' _ _ heAK hHP⟩


private theorem finite_constructible_iso (X : SixFunctorSpace D)
    {M N : proEtaleDerivedCategory X.obj.left (finiteCoefficientRing c.l E (n + 1))}
    (e : M ≅ N)
    (hM : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) X.obj.left M) :
    intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) X.obj.left N := by
  let : Finite (finiteCoefficientRing c.l E (n + 1)) := pullbackTensorCoefficientFinite c.l E n
  constructor
  · apply hM.1.subset
    intro i hi hz
    exact hi (hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e).symm)
  · intro i
    have h := hM.2 i
    rw [proEtaleModuleRestriction_constructible_iff] at h ⊢
    exact ProEtale.isConstructible_of_iso
      ((proEtaleModuleRestriction X.obj.left (finiteCoefficientRing c.l E (n + 1))).mapIso
        ((DerivedCategory.homologyFunctor _ i).mapIso e)) h


private theorem finite_tor_iso (X : SixFunctorSpace D)
    {M N : proEtaleDerivedCategory X.obj.left (finiteCoefficientRing c.l E (n + 1))}
    (e : M ≅ N) (hM : finiteTorConstructible c.l E (n + 1) (Nat.succ_pos n) X.obj.left M) :
    finiteTorConstructible c.l E (n + 1) (Nat.succ_pos n) X.obj.left N := by
  refine ⟨finite_constructible_iso D c E n X e hM.1, ?_⟩
  obtain ⟨a, b, hab, ht⟩ := hM.2
  refine ⟨a, b, hab, ?_⟩
  intro C P hC f hf hP T i hi
  obtain ⟨eC⟩ := hC
  exact ht C P ⟨eC ≪≫ e.symm⟩ f hf hP T i hi


private theorem finite_tensor (X : SixFunctorSpace D)
    (M N : proEtaleDerivedCategory X.obj.left (finiteCoefficientRing c.l E (n + 1)))
    (hM : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) X.obj.left M)
    (hN : finiteTorConstructible c.l E (n + 1) (Nat.succ_pos n) X.obj.left N) :
    intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) X.obj.left
      ((finiteIntrinsicDerivedTensor c.l E X.obj.left n).obj (M, N)) := by
  let R := integralCoefficientCommRingSheaf.{u, u} c.l E X.obj.left n
  let C := normalizedDVRModules c.l E X.obj.left n
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := SheafOfModules.monoidalClosed_kfi (R := R)
  let := SheafOfModules.monoidalPreadditive_kfi R
  let := HasDerivedCategory.standard C
  let M₀ := DerivedCategory.Q.objPreimage M
  let N₀ := DerivedCategory.Q.objPreimage N
  obtain ⟨P, f, hP, _, hf, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) N₀
  obtain ⟨Q, g, hQ, _, hg, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) M₀
  let eP : DerivedCategory.Q.obj P ≅ N :=
    asIso (DerivedCategory.Q.map f) ≪≫ DerivedCategory.Q.objObjPreimageIso N
  let eQ : DerivedCategory.Q.obj Q ≅ M :=
    asIso (DerivedCategory.Q.map g) ≪≫ DerivedCategory.Q.objObjPreimageIso M
  have hPc := finite_tor_iso D c E n X eP.symm hN
  have hQc := finite_constructible_iso D c E n X eQ.symm hM
  obtain ⟨a, b, ht⟩ := hPc.2
  have hPk : CochainComplex.IsAcyclicTensorKFlat (J := ProEt.topology X.obj.left)
      (R := R) P := hP
  have htotal := (finiteCoefficient_tensor_ctf D c.l c.different E (n + 1)
    (Nat.succ_pos n) X.obj.left P Q P (𝟙 P) (quasiIso_of_isIso _) hPk
      a b hPc ht hQc).1
  let e := DerivedCategory.Q.mapIso (β_ P Q) ≪≫
    (finiteIntrinsicTensorModels c.l E X.obj.left n).iso _ _ _ Q P hQ hP ≪≫
      (finiteIntrinsicDerivedTensor c.l E X.obj.left n).mapIso (Iso.prod eQ eP)
  exact finite_constructible_iso D c E n X e htotal

private theorem finite_pull_constructible
    (ops : SixFunctorDatum D c E (n + 1) (Nat.succ_pos n))
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (N : proEtaleDerivedCategory Y.obj.left (finiteCoefficientRing c.l E (n + 1)))
    (hN : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Y.obj.left N) :
    intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) X.obj.left
      ((finiteDerivedPullback c.l E n f.hom.left).obj N) :=
  finite_constructible_iso D c E n X ((ops.finitePullback f).app ⟨N, hN⟩)
    ((ops.finite.pull f).obj ⟨N, hN⟩).property

private theorem finite_open_constructible
    (ops : SixFunctorDatum D c E (n + 1) (Nat.succ_pos n))
    {X Y : SixFunctorSpace D} (j : X ⟶ Y) (hj : IsOpenImmersion j.hom.left)
    (N : proEtaleDerivedCategory X.obj.left (finiteCoefficientRing c.l E (n + 1)))
    (hN : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) X.obj.left N) :
    intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Y.obj.left
      ((@sfIntrinsicDerivedOpen (finiteCoefficientRing c.l E (n + 1)) _
        (pullbackTensorCoefficientFinite c.l E n) _ _ j.hom.left hj).obj N) :=
  finite_constructible_iso D c E n Y ((ops.finiteOpenExtension j hj).app ⟨N, hN⟩)
    ((ops.finite.openExtension j hj).obj ⟨N, hN⟩).property

private theorem finite_pull_tor
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (N : proEtaleDerivedCategory Y.obj.left (finiteCoefficientRing c.l E (n + 1)))
    (hN : finiteTorConstructible c.l E (n + 1) (Nat.succ_pos n) Y.obj.left N) :
    finiteTorConstructible c.l E (n + 1) (Nat.succ_pos n) X.obj.left
      ((finiteDerivedPullback c.l E n f.hom.left).obj N) := by
  let : LocallyOfFiniteType X.obj.hom := X.property.1
  let : QuasiCompact X.obj.hom := X.property.2
  let : LocallyOfFiniteType Y.obj.hom := Y.property.1
  let : QuasiCompact Y.obj.hom := Y.property.2
  have ht := sf_pullback_finiteTorConstructible D c.l c.different E (n + 1)
    (Nat.succ_pos n) X.obj Y.obj f.hom N hN
  let : Finite (finiteCoefficientRing c.l E (n + 1)) := pullbackTensorCoefficientFinite c.l E n
  let := sfIntrinsicPullback_additive (finiteCoefficientRing c.l E (n + 1)) f.hom.left
  let := sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing c.l E (n + 1)) f.hom.left
  let := sfIntrinsicPullback_preservesFiniteColimits
    (finiteCoefficientRing c.l E (n + 1)) f.hom.left
  exact finite_tor_iso D c E n X
    ((Functor.mapDerivedCategoryNatIso (pullbackTensorFiniteRealization c.l E
      f.hom.left n)).app N) ht

private theorem finite_domains
    (ops : SixFunctorDatum D c E (n + 1) (Nat.succ_pos n))
    (Q : SixFunctorCompactifiedSquare D) (d : FiniteMaps D c E n Q)
    (K : proEtaleDerivedCategory Q.X.obj.left (finiteCoefficientRing c.l E (n + 1)))
    (L : proEtaleDerivedCategory Q.Y.obj.left (finiteCoefficientRing c.l E (n + 1)))
    (hK : intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.X.obj.left K)
    (hL : finiteTorConstructible c.l E (n + 1) (Nat.succ_pos n) Q.Y.obj.left L) :
    FiniteDomains D c E n Q K L := by
  let := Q.open_i
  let := Q.open_i'
  let := Q.proper_p
  let := Q.proper_p'
  let : LocallyOfFiniteType Q.Z.obj.hom := Q.Z.property.1
  let : QuasiCompact Q.Z.obj.hom := Q.Z.property.2
  let : IsNoetherian Q.Z.obj.left := isNoetherian_of_locallyOfFiniteType Q.Z.obj.hom
  have hp := @finite_pull_constructible D c E _ _ _ n ops
  have ho := @finite_open_constructible D c E _ _ _ n ops
  have ht := finite_tensor D c E n
  have hi := finite_constructible_iso D c E n
  have hM := ho Q.i Q.open_i K hK
  have hPt := finite_pull_tor D c E n Q.p L hL
  have hP := hPt.1
  have hQ := ht Q.Z _ _ hM hPt
  have hJPt := finite_pull_tor D c E n Q.i _ hPt
  have hJP := hJPt.1
  have hV := ht Q.X _ _ hK hJPt
  have hAK := hp Q.g' K hK
  have hHP := hp Q.h _ hP
  have hHM := hp Q.h _ hM
  have hHQ := hp Q.h _ hQ
  have hAJP := hp Q.g' _ hJP
  have hAV := hp Q.g' _ hV
  have hJHP := hp Q.i' _ hHP
  let eW := finiteMu D c E Q.g' n K
      ((finiteDerivedPullback c.l E n Q.i.hom.left).obj (finiteP D c E n Q L)) ≪≫
    (finiteIntrinsicDerivedTensor c.l E Q.X'.obj.left n).mapIso
      (Iso.prod (Iso.refl _) ((sfIntrinsicDerivedSquarePullback
        (finiteCoefficientRing c.l E (n + 1)) Q.g'.hom.left Q.i'.hom.left
          Q.i.hom.left Q.h.hom.left Q.openSquare.w).app (finiteP D c E n Q L)))
  have hW := hi Q.X' eW hAV
  have heAK := ho Q.i' Q.open_i' _ hAK
  let eT := finiteMu D c E Q.h n (finiteM D c E n Q K) (finiteP D c E n Q L) ≪≫
    (finiteIntrinsicDerivedTensor c.l E Q.Z'.obj.left n).mapIso
      (Iso.prod (d.beta.app K) (Iso.refl _))
  exact ⟨hM, hP, hQ, hJP, hV, hAK, hHP, hHM, hHQ, hAJP, hAV, hJHP, hW,
    ho Q.i Q.open_i _ hV, ho Q.i' Q.open_i' _ hAV, heAK,
    ho Q.i' Q.open_i' _ hW, hp Q.h _ (ho Q.i Q.open_i _ hV), hi Q.Z' eT hHQ⟩


private def integral_maps (Q : SixFunctorCompactifiedSquare D) : IntegralMaps D c E Q := by
  let := Q.open_i
  let := Q.open_i'
  let : LocallyOfFiniteType Q.X'.obj.hom := Q.X'.property.1
  let : QuasiCompact Q.X'.obj.hom := Q.X'.property.2
  let : LocallyOfFiniteType Q.X.obj.hom := Q.X.property.1
  let : QuasiCompact Q.X.obj.hom := Q.X.property.2
  let : LocallyOfFiniteType Q.Z'.obj.hom := Q.Z'.property.1
  let : QuasiCompact Q.Z'.obj.hom := Q.Z'.property.2
  let : LocallyOfFiniteType Q.Z.obj.hom := Q.Z.property.1
  let : QuasiCompact Q.Z.obj.hom := Q.Z.property.2
  let d := Classical.choice (OpenFactorCoherence.openFactorCoherence c.l E D c.different
    Q.X'.obj Q.X.obj Q.Z'.obj Q.Z.obj Q.g'.hom Q.i'.hom Q.i.hom Q.h.hom
      (openSquare D Q))
  let sq := IsPullback.id_horiz Q.i'.hom.left
  let s : OpenImmersionSquare (𝟙 Q.X'.obj.left) Q.i'.hom.left Q.i'.hom.left
      (𝟙 Q.Z'.obj.left) :=
    { w := sq.w
      isoPullback := sq.isoPullback
      hom_fst := sq.isoPullback_hom_fst
      hom_snd := sq.isoPullback_hom_snd
      isOpenImmersion := Q.open_i'
      isOpenImmersion' := Q.open_i' }
  let d' := Classical.choice (OpenFactorCoherence.openFactorCoherence c.l E D c.different
    Q.X'.obj Q.X'.obj Q.Z'.obj Q.Z'.obj (𝟙 _) Q.i'.hom Q.i'.hom (𝟙 _) s)
  exact ⟨d, d'.tensorU, d'.tensorX⟩

/-- The two normalized base-change equations, with their finite and integral domains.
Source: current blueprint sec-six-functors/sk-prop-sf-pf-coherence, base-change paragraph
(blueprint: lem-sf-pf-open-base-change-square).

Proof plan (the node's six steps).
1. Finite pullback preserves bounded intrinsic constructibility by exactness, the pulled
back stratification, and finite local constancy. Open extension preserves the interval
and constructibility, with no Tor hypothesis on K.
2. Pull L along p and j; these maps are separated. Finite Tor amplitude of this second
factor gives the bounded constructibility of Q and V by lem-sf-tensor-ctf. Repeat after
base change; g itself requires no separatedness hypothesis.
3. Integral pullback and tensor preserve bounded constructibility. The open-factor
coherence theorem gives extension and restriction closure, and identifies completed open
pullback with ordinary restriction. Integral direct-image constructibility applied to
M,Q,HM,HQ gives the four proper images. The strict pushforward comparison and completed
adjunction transport identify the ordinary adjunctions on these full domains.
4. Write theta as c2 composed with inverse c1 for the two composition comparisons.
Their tensor compatibility gives monoidality after cancellation of c1. The same argument
for the open square gives monoidality of sigma, for the specified strict-system maps.
5. Both open routes have source isomorphic to j prime shriek A V and target j prime
shriek W. Restricting detects equality by full faithfulness and the open-unit identity.
Use finite open-tensor normalization or completed open-factor coherence, respectively.
6. In these coordinates both restrictions equal mu_A followed by 1 tensor sigma_P.
On the right use sigma monoidality to cancel its first factor against the inverse open
unit; tensor normalization identifies the remaining factor. This proves equality of
completed arrows before evaluation or rationalization. Every operation and normalization
is natural in K,L, hence so is the equality. -/
theorem openBaseChangeSquare
    (_operations : SixFunctorDatum D c E (n + 1) (Nat.succ_pos n))
    (Q : SixFunctorCompactifiedSquare D) :
    Monoidality
      (finiteIntrinsicDerivedTensor c.l E Q.Y.obj.left n)
      (finiteIntrinsicDerivedTensor c.l E Q.Z.obj.left n)
      (finiteIntrinsicDerivedTensor c.l E Q.Y'.obj.left n)
      (finiteIntrinsicDerivedTensor c.l E Q.Z'.obj.left n)
      (finiteDerivedPullback c.l E n Q.p.hom.left)
      (finiteDerivedPullback c.l E n Q.p'.hom.left)
      (finiteDerivedPullback c.l E n Q.g.hom.left)
      (finiteDerivedPullback c.l E n Q.h.hom.left)
      (finiteTheta D c E n Q)
      (finiteMu D c E Q.p n) (finiteMu D c E Q.p' n)
      (finiteMu D c E Q.g n) (finiteMu D c E Q.h n) ∧
    Monoidality
      (integralTensor D c E Q.Y) (integralTensor D c E Q.Z)
      (integralTensor D c E Q.Y') (integralTensor D c E Q.Z')
      (integralPull D c E Q.p) (integralPull D c E Q.p')
      (integralPull D c E Q.g) (integralPull D c E Q.h)
      (integralTheta D c E Q)
      (integralMu D c E Q.p) (integralMu D c E Q.p')
      (integralMu D c E Q.g) (integralMu D c E Q.h) ∧
    (∃ d : FiniteMaps D c E n Q,
      ∀ (K : proEtaleDerivedCategory Q.X.obj.left (finiteCoefficientRing c.l E (n + 1)))
        (L : proEtaleDerivedCategory Q.Y.obj.left (finiteCoefficientRing c.l E (n + 1))),
        intrinsicFiniteTorsionConstructible c.l E (n + 1) (Nat.succ_pos n) Q.X.obj.left K →
        finiteTorConstructible c.l E (n + 1) (Nat.succ_pos n) Q.Y.obj.left L →
        FiniteDomains D c E n Q K L ∧ FiniteEquation D c E n Q d K L) ∧
    (∃ d : IntegralMaps D c E Q,
      ∀ (K : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.X.obj.left))
        (L : DerivedCategory (scalarReductionSource.{u, u} c.l E Q.Y.obj.left))
        (hK : sfIntegralConstructible c.l E Q.X.obj.left K),
        finiteTorConstructibleIntegral c.l E Q.Y.obj.left L →
        ∃ dom : IntegralDomains D c E Q K L, IntegralEquation D c E Q d K L hK dom) := by
  refine ⟨finite_monoidality D c E n Q, integral_monoidality D c E Q, ?_, ?_⟩
  · obtain ⟨d, hd⟩ := finite_open_cartesian_calculus D c E n Q
    refine ⟨d, ?_⟩
    intro K L hK hL
    exact ⟨finite_domains D c E n _operations Q d K L hK hL,
      hd K (finiteP D c E n Q L)⟩
  · let d := integral_maps D c E Q
    refine ⟨d, ?_⟩
    intro K L hK hL
    let dom := integral_domains D c E n _operations Q d K L hK hL.1
    exact ⟨dom, completed_open_cartesian_identity D c E Q d K L hK dom⟩

end WeilConjectures.OpenProjectionBaseChange
