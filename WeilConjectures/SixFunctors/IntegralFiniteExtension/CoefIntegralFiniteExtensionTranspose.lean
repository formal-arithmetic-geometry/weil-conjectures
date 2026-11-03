/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import WeilConjectures.SixFunctors.PurCompactSupport.ScalarTensorAssociator
import WeilConjectures.SixFunctors.IntegralFiniteExtension.FiniteDualizingScalarComposition
import WeilConjectures.SixFunctors.IntegralFiniteExtension.IntegralScalarQuotientComposition

/-! Evaluation-transpose component of integral extension coherence.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, final paragraph.
(blueprint: lem-sf-integral-finite-extension-composition-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.derivedInternalHomOfUniverses
  CategoryTheory.homComplexFunctor
  WeilConjectures.IntegralHom.totalTensor WeilConjectures.IntegralHom.homModelMap
  WeilConjectures.IntegralHom.projection WeilConjectures.IntegralHom.evaluate

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace TransposeProof

variable {A B C : Type*} [Category A] [Category B] [Category C]

private theorem tensor_map_comp (T : A × A ⥤ A)
    {U V W X Y Z : A} (f : U ⟶ V) (g : V ⟶ W) (h : X ⟶ Y) (k : Y ⟶ Z) :
    T.map (Prod.mkHom (f ≫ g) (h ≫ k)) =
      T.map (Prod.mkHom f h) ≫ T.map (Prod.mkHom g k) :=
  T.map_comp (Prod.mkHom f h) (Prod.mkHom g k)

private theorem tensor_right_comp (T : A × A ⥤ A) {K X Y Z : A}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    T.map (Prod.mkHom (𝟙 K) (f ≫ g)) =
      T.map (Prod.mkHom (𝟙 K) f) ≫ T.map (Prod.mkHom (𝟙 K) g) := by
  simpa only [Category.id_comp] using tensor_map_comp T (𝟙 K) (𝟙 K) f g

private theorem evaluation_transport
    (T : A × A ⥤ A) (H : Aᵒᵖ × A ⥤ A)
    (adj : ∀ K : A, (Functor.curry.obj T).obj K ⊣ (Functor.curry.obj H).obj (op K))
    (hn : ∀ (K K' M : A) (f : K' ⟶ K),
      T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom f.op (𝟙 M)))) ≫
          (adj K').counit.app M =
        T.map (Prod.mkHom f (𝟙 _)) ≫ (adj K).counit.app M)
    (K K' M M' : A) (f : K' ⟶ K) (g : M ⟶ M') :
    T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom f.op g))) ≫
        (adj K').counit.app M' =
      T.map (Prod.mkHom f (𝟙 (H.obj (op K, M)))) ≫
        (adj K).counit.app M ≫ g := by
  have hh : H.map (Prod.mkHom f.op g) =
      H.map (Prod.mkHom (𝟙 (op K)) g) ≫ H.map (Prod.mkHom f.op (𝟙 M')) := by
    rw [← H.map_comp]
    simp only [prod_comp, Category.id_comp, Category.comp_id]
  rw [hh, tensor_right_comp, Category.assoc, hn]
  have ht : T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom (𝟙 (op K)) g))) ≫
      T.map (Prod.mkHom f (𝟙 _)) =
      T.map (Prod.mkHom f (𝟙 _)) ≫
        T.map (Prod.mkHom (𝟙 K) (H.map (Prod.mkHom (𝟙 (op K)) g))) := by
    simp only [← T.map_comp, prod_comp, Category.id_comp, Category.comp_id]
  erw [← Category.assoc, ht, Category.assoc]
  congr 1
  exact (adj K).counit.naturality g

private def homMap
    {TA : A × A ⥤ A} {TB : B × B ⥤ B}
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (a : ∀ K : A, (Functor.curry.obj TA).obj K ⊣ (Functor.curry.obj HA).obj (op K))
    (b : ∀ K : B, (Functor.curry.obj TB).obj K ⊣ (Functor.curry.obj HB).obj (op K))
    (F : A ⥤ B) (μ : TA ⋙ F ≅ F.prod F ⋙ TB) (K M : A) :
    F.obj (HA.obj (op K, M)) ⟶ HB.obj (op (F.obj K), F.obj M) :=
  (b (F.obj K)).homEquiv _ _ (μ.inv.app (K, HA.obj (op K, M)) ≫
    F.map ((a K).counit.app M))

private theorem uncurry
    (T : A × A ⥤ A) (H : Aᵒᵖ × A ⥤ A)
    (a : ∀ K : A, (Functor.curry.obj T).obj K ⊣ (Functor.curry.obj H).obj (op K))
    {K M N : A} (f : N ⟶ H.obj (op K, M)) :
    ((a K).homEquiv N M).symm f =
      T.map (Prod.mkHom (𝟙 K) f) ≫ (a K).counit.app M :=
  (a K).homEquiv_counit N M f

private theorem homMap_eval
    {TA : A × A ⥤ A} {TB : B × B ⥤ B}
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (a : ∀ K : A, (Functor.curry.obj TA).obj K ⊣ (Functor.curry.obj HA).obj (op K))
    (b : ∀ K : B, (Functor.curry.obj TB).obj K ⊣ (Functor.curry.obj HB).obj (op K))
    (F : A ⥤ B) (μ : TA ⋙ F ≅ F.prod F ⋙ TB) (K M : A) :
    TB.map (Prod.mkHom (𝟙 (F.obj K)) (homMap a b F μ K M)) ≫
        (b (F.obj K)).counit.app (F.obj M) =
      μ.inv.app (K, HA.obj (op K, M)) ≫ F.map ((a K).counit.app M) :=
  ((b (F.obj K)).homEquiv _ _).symm_apply_apply _

private theorem homMap_naturality
    {TA : A × A ⥤ A} {TB : B × B ⥤ B}
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B}
    (a : ∀ K : A, (Functor.curry.obj TA).obj K ⊣ (Functor.curry.obj HA).obj (op K))
    (b : ∀ K : B, (Functor.curry.obj TB).obj K ⊣ (Functor.curry.obj HB).obj (op K))
    (ha : ∀ (K K' M : A) (f : K' ⟶ K),
      TA.map (Prod.mkHom (𝟙 K') (HA.map (Prod.mkHom f.op (𝟙 M)))) ≫
          (a K').counit.app M = TA.map (Prod.mkHom f (𝟙 _)) ≫ (a K).counit.app M)
    (hb : ∀ (K K' M : B) (f : K' ⟶ K),
      TB.map (Prod.mkHom (𝟙 K') (HB.map (Prod.mkHom f.op (𝟙 M)))) ≫
          (b K').counit.app M = TB.map (Prod.mkHom f (𝟙 _)) ≫ (b K).counit.app M)
    (F : A ⥤ B) (μ : TA ⋙ F ≅ F.prod F ⋙ TB)
    (K M K' M' : A) (f : K' ⟶ K) (g : M ⟶ M') :
    F.map (HA.map (Prod.mkHom f.op g)) ≫ homMap a b F μ K' M' =
      homMap a b F μ K M ≫ HB.map (Prod.mkHom (F.map f).op (F.map g)) := by
  apply ((b (F.obj K')).homEquiv _ (F.obj M')).symm.injective
  simp only [uncurry, tensor_right_comp, Category.assoc]
  rw [homMap_eval, evaluation_transport TB HB b hb]
  have hn := μ.inv.naturality (Prod.mkHom (𝟙 K') (HA.map (Prod.mkHom f.op g)))
  have hn' := μ.inv.naturality (Prod.mkHom f (𝟙 (HA.obj (op K, M))))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn hn'
  simp only [F.map_id] at hn hn'
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp,
    evaluation_transport TA HA a ha, F.map_comp, F.map_comp]
  have ht : TB.map (Prod.mkHom (𝟙 (F.obj K')) (homMap a b F μ K M)) ≫
      TB.map (Prod.mkHom (F.map f) (𝟙 _)) =
      TB.map (Prod.mkHom (F.map f) (𝟙 _)) ≫
        TB.map (Prod.mkHom (𝟙 (F.obj K)) (homMap a b F μ K M)) := by
    simp only [← TB.map_comp, prod_comp, Category.id_comp, Category.comp_id]
  rw [reassoc_of% ht, reassoc_of% homMap_eval a b F μ K M,
    ← reassoc_of% hn']

private theorem uncurry_pre
    (T : A × A ⥤ A) (H : Aᵒᵖ × A ⥤ A)
    (a : ∀ K : A, (Functor.curry.obj T).obj K ⊣ (Functor.curry.obj H).obj (op K))
    {K M N P : A} (f : N ⟶ P) (g : P ⟶ H.obj (op K, M)) :
    ((a K).homEquiv N M).symm (f ≫ g) =
      T.map (Prod.mkHom (𝟙 K) f) ≫ ((a K).homEquiv P M).symm g := by
  simp only [uncurry, tensor_right_comp, Category.assoc]

private theorem uncurry_post
    (T : A × A ⥤ A) (H : Aᵒᵖ × A ⥤ A)
    (a : ∀ K : A, (Functor.curry.obj T).obj K ⊣ (Functor.curry.obj H).obj (op K))
    (hn : ∀ (K K' M : A) (f : K' ⟶ K),
      T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom f.op (𝟙 M)))) ≫
          (a K').counit.app M = T.map (Prod.mkHom f (𝟙 _)) ≫ (a K).counit.app M)
    {K K' M M' N : A} (h : N ⟶ H.obj (op K, M)) (f : K' ⟶ K) (g : M ⟶ M') :
    ((a K').homEquiv N M').symm (h ≫ H.map (Prod.mkHom f.op g)) =
      T.map (Prod.mkHom f (𝟙 N)) ≫ ((a K).homEquiv N M).symm h ≫ g := by
  rw [uncurry_pre, uncurry, evaluation_transport T H a hn, uncurry]
  simp only [← Category.assoc, ← T.map_comp]
  congr 2
  simp only [prod_comp, Category.id_comp, Category.comp_id]

private theorem homMap_tower
    {TA : A × A ⥤ A} {TB : B × B ⥤ B} {TC : C × C ⥤ C}
    {HA : Aᵒᵖ × A ⥤ A} {HB : Bᵒᵖ × B ⥤ B} {HC : Cᵒᵖ × C ⥤ C}
    (a : ∀ K : A, (Functor.curry.obj TA).obj K ⊣ (Functor.curry.obj HA).obj (op K))
    (b : ∀ K : B, (Functor.curry.obj TB).obj K ⊣ (Functor.curry.obj HB).obj (op K))
    (c : ∀ K : C, (Functor.curry.obj TC).obj K ⊣ (Functor.curry.obj HC).obj (op K))
    (hc : ∀ (K K' M : C) (f : K' ⟶ K),
      TC.map (Prod.mkHom (𝟙 K') (HC.map (Prod.mkHom f.op (𝟙 M)))) ≫
          (c K').counit.app M = TC.map (Prod.mkHom f (𝟙 _)) ≫ (c K).counit.app M)
    (F : A ⥤ B) (G : B ⥤ C) (J : A ⥤ C)
    (μ : TA ⋙ F ≅ F.prod F ⋙ TB) (ν : TB ⋙ G ≅ G.prod G ⋙ TC)
    (ξ : TA ⋙ J ≅ J.prod J ⋙ TC) (α : F ⋙ G ≅ J)
    (ht : ∀ K M : A,
      G.map (μ.hom.app (K, M)) ≫ ν.hom.app (F.obj K, F.obj M) ≫
          TC.map (Prod.mkHom (α.hom.app K) (α.hom.app M)) =
        α.hom.app (TA.obj (K, M)) ≫ ξ.hom.app (K, M)) (K M : A) :
    G.map (homMap a b F μ K M) ≫ homMap b c G ν (F.obj K) (F.obj M) ≫
        HC.map (Prod.mkHom (α.inv.app K).op (α.hom.app M)) =
      α.hom.app (HA.obj (op K, M)) ≫ homMap a c J ξ K M := by
  have hi (U V : A) :
      ν.inv.app (F.obj U, F.obj V) ≫ G.map (μ.inv.app (U, V)) ≫
          α.hom.app (TA.obj (U, V)) =
        TC.map (Prod.mkHom (α.hom.app U) (α.hom.app V)) ≫ ξ.inv.app (U, V) := by
    apply (cancel_mono (ξ.hom.app (U, V))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← ht]
    simp [← G.map_comp, ← Category.assoc]
  have he : ((c (G.obj (F.obj K))).homEquiv _ (G.obj (F.obj M))).symm
      (G.map (homMap a b F μ K M) ≫ homMap b c G ν (F.obj K) (F.obj M)) =
      ν.inv.app (F.obj K, F.obj (HA.obj (op K, M))) ≫
        G.map (μ.inv.app (K, HA.obj (op K, M))) ≫ G.map (F.map ((a K).counit.app M)) := by
    rw [uncurry_pre, uncurry, homMap_eval]
    have hn := ν.inv.naturality
      (Prod.mkHom (𝟙 (F.obj K)) (homMap a b F μ K M))
    dsimp only [Functor.comp_map, Functor.prod_map] at hn
    simp only [G.map_id] at hn
    rw [← Category.assoc, hn, Category.assoc, ← G.map_comp,
      homMap_eval, G.map_comp]
  apply ((c (J.obj K)).homEquiv _ (J.obj M)).symm.injective
  rw [← Category.assoc, uncurry_post TC HC c hc, he, uncurry_pre, uncurry, homMap_eval]
  have hn := α.hom.naturality ((a K).counit.app M)
  change G.map (F.map ((a K).counit.app M)) ≫ α.hom.app M =
    α.hom.app (TA.obj (K, HA.obj (op K, M))) ≫ J.map ((a K).counit.app M) at hn
  simp only [Category.assoc]
  rw [hn, reassoc_of% hi K (HA.obj (op K, M))]
  rw [← Category.assoc, ← TC.map_comp]
  congr 2
  simp only [prod_comp, Iso.inv_hom_id_app, Category.id_comp]

private theorem transport_tower
    (HB : Bᵒᵖ × B ⥤ B) (HC : Cᵒᵖ × C ⥤ C) (G G' : B ⥤ C)
    {U V N U' V' N' : B} {ZK ZM ZH ZK' ZM' ZH' : C}
    (aK : U ≅ U') (aM : V ≅ V') (aH : N ≅ N')
    (bK : G.obj U' ≅ G'.obj U') (bM : G.obj V' ≅ G'.obj V')
    (bH : G.obj N' ≅ G'.obj N')
    (bQ : G.obj (HB.obj (op U', V')) ≅ G'.obj (HB.obj (op U', V')))
    (dK : ZK ≅ ZK') (dM : ZM ≅ ZM') (dH : ZH ≅ ZH')
    (αK : G.obj U ≅ ZK) (αM : G.obj V ≅ ZM) (αH : G.obj N ≅ ZH)
    (f : N ⟶ HB.obj (op U, V))
    (g : G.obj (HB.obj (op U, V)) ⟶ HC.obj (op (G.obj U), G.obj V))
    (g' : G.obj (HB.obj (op U', V')) ⟶ HC.obj (op (G.obj U'), G.obj V'))
    (h : ZH ⟶ HC.obj (op ZK, ZM))
    (hn : G.map (HB.map (Prod.mkHom aK.inv.op aM.hom)) ≫ g' =
      g ≫ HC.map (Prod.mkHom (G.map aK.inv).op (G.map aM.hom)))
    (ht : G.map f ≫ g ≫ HC.map (Prod.mkHom αK.inv.op αM.hom) = αH.hom ≫ h)
    (hc : G.map (aH.inv ≫ f ≫ HB.map (Prod.mkHom aK.inv.op aM.hom)) ≫ bQ.hom =
      bH.hom ≫ G'.map (aH.inv ≫ f ≫ HB.map (Prod.mkHom aK.inv.op aM.hom))) :
    let γK := bK.symm ≪≫ G.mapIso aK.symm ≪≫ αK ≪≫ dK
    let γM := bM.symm ≪≫ G.mapIso aM.symm ≪≫ αM ≪≫ dM
    let γH := bH.symm ≪≫ G.mapIso aH.symm ≪≫ αH ≪≫ dH
    G'.map (aH.inv ≫ f ≫ HB.map (Prod.mkHom aK.inv.op aM.hom)) ≫
        (bQ.inv ≫ g' ≫ HC.map (Prod.mkHom bK.inv.op bM.hom)) ≫
        HC.map (Prod.mkHom γK.inv.op γM.hom) =
      γH.hom ≫ (dH.inv ≫ h ≫ HC.map (Prod.mkHom dK.inv.op dM.hom)) := by
  dsimp only
  have hc' :
      G'.map (aH.inv ≫ f ≫ HB.map (Prod.mkHom aK.inv.op aM.hom)) ≫ bQ.inv =
        bH.inv ≫ G.map (aH.inv ≫ f ≫ HB.map (Prod.mkHom aK.inv.op aM.hom)) := by
    apply (cancel_mono bQ.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hc, Iso.inv_hom_id_assoc]
  simp only [Category.assoc]
  rw [← Category.assoc _ bQ.inv, hc']
  simp only [G.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  have hp :
      HC.map (Prod.mkHom (G.map aK.inv).op (G.map aM.hom)) ≫
        HC.map (Prod.mkHom bK.inv.op bM.hom) ≫
        HC.map (Prod.mkHom
          (bK.symm ≪≫ G.mapIso aK.symm ≪≫ αK ≪≫ dK).inv.op
          (bM.symm ≪≫ G.mapIso aM.symm ≪≫ αM ≪≫ dM).hom) =
      HC.map (Prod.mkHom αK.inv.op αM.hom) ≫
        HC.map (Prod.mkHom dK.inv.op dM.hom) := by
    simp only [← HC.map_comp, prod_comp, ← op_comp, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
      Category.assoc, Iso.hom_inv_id_assoc, ← G.map_comp_assoc, ← G.map_comp,
      Iso.hom_inv_id, G.map_id, Category.id_comp, Category.comp_id]
  rw [hp, reassoc_of% ht]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Category.assoc, Iso.hom_inv_id_assoc]

end TransposeProof

namespace WeilConjectures.IntegralFiniteExtension

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (X : Scheme.{u})

private theorem completion_inv_naturality
    (K M : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) (hM : IsSfDerivedComplete l E X M)
    (f : K ⟶ M) :
    (integralScalarExtensionOfUniverses l E L ι X).map f ≫
        (completion l E L ι X M hM).inv =
      (completion l E L ι X K hK).inv ≫
        (pbcDerivedExtend (completedCoefficientMap l E L ι X)).map f := by
  apply (cancel_mono (completion l E L ι X M hM).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := (completedScalarComparison l E L ι X).naturality f
  change (pbcDerivedExtend (completedCoefficientMap l E L ι X)).map f ≫
      (completion l E L ι X M hM).hom =
    (completion l E L ι X K hK).hom ≫
      (integralScalarExtensionOfUniverses l E L ι X).map f at hn
  rw [hn, Iso.inv_hom_id_assoc]

private theorem quotient_naturality (n : ℕ)
    (K M : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) (hM : IsSfDerivedComplete l E X M)
    (f : K ⟶ M) :
    (scalarReductionDerivedExtension l L X n).map
        ((integralScalarExtensionOfUniverses l E L ι X).map f) ≫
      (quotient l E L ι X n M hM).hom =
    (quotient l E L ι X n K hK).hom ≫
      (pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)).map
        ((scalarReductionDerivedExtension l E X n).map f) := by
  let RF := scalarReductionDerivedExtension l L X n
  let RE := scalarReductionDerivedExtension l E X n
  let B := pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)
  let P := pbcDerivedExtend (completedCoefficientMap l E L ι X)
  let T := integralScalarExtensionOfUniverses l E L ι X
  let e : P ⋙ RF ≅ RE ⋙ B :=
    Functor.isoWhiskerLeft P (PurCompactSupport.finiteReductionIso l L X n).symm ≪≫
      PurCompactSupport.tensorSquare (completedCoefficientMap l E L ι X)
        (integralScalarQuotientSheafMap l E L ι X n)
        (completedIntegralCommRingProjectionUnrestricted l E X n)
        (completedIntegralCommRingProjectionUnrestricted l L X n)
        ((completedCoefficientMap_existsUnique l E L ι X).exists.choose_spec n) ≪≫
      Functor.isoWhiskerRight (PurCompactSupport.finiteReductionIso l E X n) B
  let cK := completion l E L ι X K hK
  let cM := completion l E L ι X M hM
  have hn := e.hom.naturality f
  change RF.map (P.map f) ≫ e.hom.app M = e.hom.app K ≫ B.map (RE.map f) at hn
  change RF.map (T.map f) ≫ (RF.map cM.inv ≫ e.hom.app M) =
    (RF.map cK.inv ≫ e.hom.app K) ≫ B.map (RE.map f)
  rw [← Category.assoc, ← RF.map_comp,
    completion_inv_naturality l E L ι X K M hK hM f, RF.map_comp,
    Category.assoc, hn, Category.assoc]

private theorem quotient_map_composition
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (j : L →ₐ[Padic l] F) (n : ℕ) :
    integralScalarQuotientSheafMap l E L ι X n ≫
        integralScalarQuotientSheafMap l L F j X n =
      integralScalarQuotientSheafMap l E F (j.comp ι) X n := by
  have h : (integralScalarQuotientMap l L F j n).comp
        (integralScalarQuotientMap l E L ι n) =
      integralScalarQuotientMap l E F (j.comp ι) n := by
    apply RingHom.ext
    intro x
    induction x using Quotient.inductionOn' with
    | h x => rfl
  unfold integralScalarQuotientSheafMap
  rw [← Functor.map_comp]
  congr 1
  ext x
  exact RingHom.congr_fun h x.down

private theorem v_composition
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (hb : ∀ (K K' M : IntegralVerdier.Ambient l L X) (f : K' ⟶ K),
      b.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l L X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (b.adjunction K').counit.app M =
        b.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (b.adjunction K).counit.app M)
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (j : L →ₐ[Padic l] F)
    (c : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l F X))
    (hc : ∀ (K K' M : IntegralVerdier.Ambient l F X) (f : K' ⟶ K),
      c.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l F X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (c.adjunction K').counit.app M =
        c.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (c.adjunction K).counit.app M)
    (K M : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) (hM : IsSfDerivedComplete l E X M) :
    (integralScalarExtensionOfUniverses l L F j X).map
        (v l E L ι X a b K M hK hM) ≫
      v l L F j X b c
        ((integralScalarExtensionOfUniverses l E L ι X).obj K)
        ((integralScalarExtensionOfUniverses l E L ι X).obj M)
        (extension_complete l E L ι X K hK) (extension_complete l E L ι X M hM) ≫
      (IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l F X)).map
        (Prod.mkHom (comp l E L ι X F j K hK).inv.op
          (comp l E L ι X F j M hM).hom) =
    (comp l E L ι X F j
      ((IntegralHom.hom.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l E X)).obj (op K, M))
      (scalarInternalHom_complete l E X K M hM)).hom ≫
      v l E F (j.comp ι) X a c K M hK hM := by
  let P := pbcDerivedExtend (completedCoefficientMap l E L ι X)
  let Q := pbcDerivedExtend (completedCoefficientMap l L F j X)
  let R := pbcDerivedExtend (completedCoefficientMap l E F (j.comp ι) X)
  let Ti := integralScalarExtensionOfUniverses l E L ι X
  let Tj := integralScalarExtensionOfUniverses l L F j X
  let HE := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)
  let HL := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)
  let HF := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l F X)
  let μ := PurCompactSupport.scalarTensor (completedCoefficientMap l E L ι X)
    (tensorModel X a) (tensorModel X b)
  let ν := PurCompactSupport.scalarTensor (completedCoefficientMap l L F j X)
    (tensorModel X b) (tensorModel X c)
  let ξ := PurCompactSupport.scalarTensor (completedCoefficientMap l E F (j.comp ι) X)
    (tensorModel X a) (tensorModel X c)
  let α := PurCompactSupport.tensorComposition (completedCoefficientMap l E L ι X)
    (completedCoefficientMap l L F j X) (completedCoefficientMap l E F (j.comp ι) X)
    (PurCompactSupport.completedMap_composition l E L ι F j X)
  let aK := completion l E L ι X K hK
  let aM := completion l E L ι X M hM
  let aH := completion l E L ι X (HE.obj (op K, M))
    (scalarInternalHom_complete l E X K M hM)
  let bK := completion l L F j X (Ti.obj K) (extension_complete l E L ι X K hK)
  let bM := completion l L F j X (Ti.obj M) (extension_complete l E L ι X M hM)
  let bH := completion l L F j X (Ti.obj (HE.obj (op K, M)))
    (extension_complete l E L ι X _ (scalarInternalHom_complete l E X K M hM))
  let bQ := completion l L F j X (HL.obj (op (Ti.obj K), Ti.obj M))
    (scalarInternalHom_complete l L X _ _ (extension_complete l E L ι X M hM))
  let dK := completion l E F (j.comp ι) X K hK
  let dM := completion l E F (j.comp ι) X M hM
  let dH := completion l E F (j.comp ι) X (HE.obj (op K, M))
    (scalarInternalHom_complete l E X K M hM)
  have hn := TransposeProof.homMap_naturality b.adjunction c.adjunction hb hc Q ν
    (P.obj K) (P.obj M) (Ti.obj K) (Ti.obj M) aK.inv aM.hom
  have ht := TransposeProof.homMap_tower a.adjunction b.adjunction c.adjunction hc
    P Q R μ ν ξ α
    (fun U V ↦ PurCompactSupport.scalarTensor_associator
      (completedCoefficientMap l E L ι X) (completedCoefficientMap l L F j X)
      (completedCoefficientMap l E F (j.comp ι) X)
      (PurCompactSupport.completedMap_composition l E L ι F j X)
      (tensorModel X a) (tensorModel X b) (tensorModel X c) U V) K M
  have hχ := (completedScalarComparison l L F j X).naturality
    (v l E L ι X a b K M hK hM)
  have h := TransposeProof.transport_tower HL HF Q Tj aK aM aH bK bM bH bQ
    dK dM dH (α.app K) (α.app M) (α.app (HE.obj (op K, M)))
    (TransposeProof.homMap a.adjunction b.adjunction P μ K M)
    (TransposeProof.homMap b.adjunction c.adjunction Q ν (P.obj K) (P.obj M))
    (TransposeProof.homMap b.adjunction c.adjunction Q ν (Ti.obj K) (Ti.obj M))
    (TransposeProof.homMap a.adjunction c.adjunction R ξ K M) hn ht hχ
  exact h

private theorem v_naturality_second
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (ha : ∀ (K K' M : IntegralVerdier.Ambient l E X) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l E X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (a.adjunction K').counit.app M =
        a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app M)
    (hb : ∀ (K K' M : IntegralVerdier.Ambient l L X) (f : K' ⟶ K),
      b.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l L X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (b.adjunction K').counit.app M =
        b.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (b.adjunction K).counit.app M)
    (K M N : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) (hM : IsSfDerivedComplete l E X M)
    (hN : IsSfDerivedComplete l E X N) (f : M ⟶ N) :
    (integralScalarExtensionOfUniverses l E L ι X).map
        ((IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)).map
          (Prod.mkHom (𝟙 (op K)) f)) ≫ v l E L ι X a b K N hK hN =
      v l E L ι X a b K M hK hM ≫
        (IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)).map
          (Prod.mkHom (𝟙 _)
            ((integralScalarExtensionOfUniverses l E L ι X).map f)) := by
  let P := pbcDerivedExtend (completedCoefficientMap l E L ι X)
  let T := integralScalarExtensionOfUniverses l E L ι X
  let HE := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X)
  let HL := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)
  let μ := PurCompactSupport.scalarTensor (completedCoefficientMap l E L ι X)
    (tensorModel X a) (tensorModel X b)
  have hh := completion_inv_naturality l E L ι X _ _
    (scalarInternalHom_complete l E X K M hM)
    (scalarInternalHom_complete l E X K N hN) (HE.map (Prod.mkHom (𝟙 (op K)) f))
  have hn := TransposeProof.homMap_naturality a.adjunction b.adjunction ha hb P μ
    K M K N (𝟙 K) f
  simp only [op_id, P.map_id] at hn
  have hm := (completedScalarComparison l E L ι X).naturality f
  change P.map f ≫ (completion l E L ι X N hN).hom =
    (completion l E L ι X M hM).hom ≫ T.map f at hm
  let cK := completion l E L ι X K hK
  let cM := completion l E L ι X M hM
  let cN := completion l E L ι X N hN
  let cHM := completion l E L ι X (HE.obj (op K, M))
    (scalarInternalHom_complete l E X K M hM)
  let cHN := completion l E L ι X (HE.obj (op K, N))
    (scalarInternalHom_complete l E X K N hN)
  let mM := TransposeProof.homMap a.adjunction b.adjunction P μ K M
  let mN := TransposeProof.homMap a.adjunction b.adjunction P μ K N
  change P.map (HE.map (Prod.mkHom (𝟙 (op K)) f)) ≫ mN =
    mM ≫ HL.map (Prod.mkHom (𝟙 _) (P.map f)) at hn
  change T.map (HE.map (Prod.mkHom (𝟙 (op K)) f)) ≫ cHN.inv =
    cHM.inv ≫ P.map (HE.map (Prod.mkHom (𝟙 (op K)) f)) at hh
  have hp : HL.map (Prod.mkHom (𝟙 _) (P.map f)) ≫
      HL.map (Prod.mkHom cK.inv.op cN.hom) =
    HL.map (Prod.mkHom cK.inv.op cM.hom) ≫
      HL.map (Prod.mkHom (𝟙 _) (T.map f)) := by
    rw [← HL.map_comp, ← HL.map_comp]
    congr 1
    apply CategoryTheory.Prod.hom_ext
    · simp only [prod_comp, Category.id_comp, Category.comp_id]
    · exact hm
  change T.map (HE.map (Prod.mkHom (𝟙 (op K)) f)) ≫
      (cHN.inv ≫ mN ≫ HL.map (Prod.mkHom cK.inv.op cN.hom)) =
    (cHM.inv ≫ mM ≫ HL.map (Prod.mkHom cK.inv.op cM.hom)) ≫
      HL.map (Prod.mkHom (𝟙 _) (T.map f))
  simp only [Category.assoc]
  rw [← Category.assoc _ cHN.inv, hh, Category.assoc, reassoc_of% hn, hp]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem u_composition
    (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (j : L →ₐ[Padic l] F) (wF : DualizingDatum l X D hl F) :
    (integralScalarExtensionOfUniverses l L F j X).map
        (u l E L ι X D hl wE wL) ≫ u l L F j X D hl wL wF =
      (comp l E L ι X F j wE.omega.obj wE.omega.property.1).hom ≫
        u l E F (j.comp ι) X D hl wE wF := by
  let A := comp l E L ι X F j wE.omega.obj wE.omega.property.1
  let Ti := integralScalarExtensionOfUniverses l E L ι X
  let Tj := integralScalarExtensionOfUniverses l L F j X
  let ui := u l E L ι X D hl wE wL
  let uj := u l L F j X D hl wL wF
  let f := A.inv ≫ Tj.map ui ≫ uj
  have hf : ∀ n : ℕ,
      (scalarReductionDerivedExtension l F X n).map f ≫ (wF.reduction n).hom =
        (quotient l E F (j.comp ι) X n wE.omega.obj wE.omega.property.1).hom ≫
          (pbcDerivedExtend (integralScalarQuotientSheafMap l E F (j.comp ι) X n)).map
            (wE.reduction n).hom ≫ finiteU l E F (j.comp ι) X D n := by
    intro n
    let R := scalarReductionDerivedExtension l F X n
    let Bi := pbcDerivedExtend (integralScalarQuotientSheafMap l E L ι X n)
    let Bj := pbcDerivedExtend (integralScalarQuotientSheafMap l L F j X n)
    let Bij := pbcDerivedExtend (integralScalarQuotientSheafMap l E F (j.comp ι) X n)
    let α := PurCompactSupport.tensorComposition
      (integralScalarQuotientSheafMap l E L ι X n)
      (integralScalarQuotientSheafMap l L F j X n)
      (integralScalarQuotientSheafMap l E F (j.comp ι) X n)
      (quotient_map_composition l E L ι X F j n)
    have hn := quotient_naturality l L F j X n
      (Ti.obj wE.omega.obj) wL.omega.obj
      (extension_complete l E L ι X wE.omega.obj wE.omega.property.1)
      wL.omega.property.1 ui
    have hp := quotient_scalar_composition l E L ι X F j n
      (quotient_map_composition l E L ι X F j n) wE.omega.obj wE.omega.property.1
    have hv := finiteU_scalar_composition l E L ι X D F j n
      (quotient_map_composition l E L ι X F j n)
    have he := α.hom.naturality (wE.reduction n).hom
    dsimp only [Functor.comp_map] at he
    change Bj.map (Bi.map (wE.reduction n).hom) ≫ α.hom.app _ =
      α.hom.app _ ≫ Bij.map (wE.reduction n).hom at he
    dsimp only [f]
    simp only [Functor.map_comp, Category.assoc]
    rw [u_reduction l L F j X D hl wL wF]
    rw [reassoc_of% hn]
    rw [← Bj.map_comp_assoc, u_reduction l E L ι X D hl wE wL]
    simp only [Bj.map_comp, Category.assoc]
    erw [hv, reassoc_of% he]
    erw [← reassoc_of% hp]
    erw [← R.map_comp_assoc, Iso.inv_hom_id, R.map_id, Category.id_comp]
  have he : f = u l E F (j.comp ι) X D hl wE wF :=
    (u_existsUnique l E F (j.comp ι) X D hl wE wF).unique hf
      (u_reduction l E F (j.comp ι) X D hl wE wF)
  have h := congrArg (fun z ↦ A.hom ≫ z) he
  simpa only [f, Iso.hom_inv_id_assoc] using h

end WeilConjectures.IntegralFiniteExtension

namespace WeilConjectures.IntegralFiniteExtension

/-- Composition equations for u, v and beta, obtained by transposing evaluations.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, final paragraph.
Proof: transpose the two successive evaluation maps under the same scalar
associator. Evaluation naturality identifies both transposes; postcomposition
with internal Hom into the u equation gives the beta equation. Coherent finite
counits and normalized limits preserve these equalities.
-/
theorem comparison_composition_transpose
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L)
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (_hevalE : ∀ (K K' M : IntegralVerdier.Ambient l E X) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l E X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (a.adjunction K').counit.app M =
        a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app M)
    (_hevalL : ∀ (K K' M : IntegralVerdier.Ambient l L X) (f : K' ⟶ K),
      b.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l L X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (b.adjunction K').counit.app M =
        b.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (b.adjunction K).counit.app M) :
    ∀ (F : Type u) [Field F] [Algebra (Padic l) F]
      [FiniteDimensional (Padic l) F]
      (j : L →ₐ[Padic l] F) (wF : DualizingDatum l X D hl F)
      (c : IntegralHom.TensorPresentation.{u, u} X
        (completedIntegralCommRingSheafUnrestricted l F X)),
      (∀ (K K' M : IntegralVerdier.Ambient l F X) (f : K' ⟶ K),
        c.tensor.map (Prod.mkHom (𝟙 K')
            ((IntegralHom.hom.{u, u} X
              (completedIntegralCommRingSheafUnrestricted l F X)).map
              (Prod.mkHom f.op (𝟙 M)))) ≫ (c.adjunction K').counit.app M =
          c.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (c.adjunction K).counit.app M) →
      (integralScalarExtensionOfUniverses l L F j X).map
          (u l E L ι X D hl wE wL) ≫ u l L F j X D hl wL wF =
        (comp l E L ι X F j wE.omega.obj wE.omega.property.1).hom ≫
          u l E F (j.comp ι) X D hl wE wF ∧
      (∀ (K M : sfIntegralConstructibleCategory l E X),
        (integralScalarExtensionOfUniverses l L F j X).map
            (v l E L ι X a b K.obj M.obj K.property.1 M.property.1) ≫
          v l L F j X b c
            ((integralScalarExtensionOfUniverses l E L ι X).obj K.obj)
            ((integralScalarExtensionOfUniverses l E L ι X).obj M.obj)
            (extension_complete l E L ι X K.obj K.property.1)
            (extension_complete l E L ι X M.obj M.property.1) ≫
          (IntegralHom.hom.{u, u}
            X (completedIntegralCommRingSheafUnrestricted l F X)).map
            (Prod.mkHom
              (comp l E L ι X F j K.obj K.property.1).inv.op
              (comp l E L ι X F j M.obj M.property.1).hom) =
        (comp l E L ι X F j
          ((IntegralHom.hom.{u, u}
            X (completedIntegralCommRingSheafUnrestricted l E X)).obj
            (op K.obj, M.obj))
          (scalarInternalHom_complete l E X K.obj M.obj M.property.1)).hom ≫
          v l E F (j.comp ι) X a c K.obj M.obj K.property.1 M.property.1) ∧
      (∀ (K : sfIntegralConstructibleCategory l E X),
        (integralScalarExtensionOfUniverses l L F j X).map
            (beta l E L ι X D hl wE wL a b K.obj K.property.1) ≫
          beta l L F j X D hl wL wF b c
            ((integralScalarExtensionOfUniverses l E L ι X).obj K.obj)
            (extension_complete l E L ι X K.obj K.property.1) ≫
          (IntegralVerdier.dual l F X wF.omega.obj).map
            (comp l E L ι X F j K.obj K.property.1).inv.op =
        (comp l E L ι X F j
          ((IntegralVerdier.dual l E X wE.omega.obj).obj (op K.obj))
          (scalarInternalHom_complete l E X K.obj wE.omega.obj
            wE.omega.property.1)).hom ≫
          beta l E F (j.comp ι) X D hl wE wF a c K.obj K.property.1) := by
  intro F _ _ _ j wF c hc
  have hu := u_composition l E L ι X D hl wE wL F j wF
  refine ⟨hu, ?_, ?_⟩
  · intro K M
    exact v_composition l E L ι X a b _hevalL F j c hc K.obj M.obj
      K.property.1 M.property.1
  · intro K
    let Ti := integralScalarExtensionOfUniverses l E L ι X
    let Tj := integralScalarExtensionOfUniverses l L F j X
    let HF := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l F X)
    let ui := u l E L ι X D hl wE wL
    let uj := u l L F j X D hl wL wF
    let uij := u l E F (j.comp ι) X D hl wE wF
    let aK := comp l E L ι X F j K.obj K.property.1
    let aW := comp l E L ι X F j wE.omega.obj wE.omega.property.1
    have hn := v_naturality_second l L F j X b c _hevalL hc
      (Ti.obj K.obj) (Ti.obj wE.omega.obj) wL.omega.obj
      (extension_complete l E L ι X K.obj K.property.1)
      (extension_complete l E L ι X wE.omega.obj wE.omega.property.1)
      wL.omega.property.1 ui
    have hv := v_composition l E L ι X a b _hevalL F j c hc
      K.obj wE.omega.obj K.property.1 wE.omega.property.1
    have hp : HF.map (Prod.mkHom (𝟙 _) (Tj.map ui)) ≫
        HF.map (Prod.mkHom (𝟙 _) uj) ≫
        (IntegralVerdier.dual l F X wF.omega.obj).map aK.inv.op =
      HF.map (Prod.mkHom aK.inv.op aW.hom) ≫
        HF.map (Prod.mkHom (𝟙 _) uij) := by
      change HF.map (Prod.mkHom (𝟙 _) (Tj.map ui)) ≫
        HF.map (Prod.mkHom (𝟙 _) uj) ≫ HF.map (Prod.mkHom aK.inv.op (𝟙 _)) = _
      simp only [← HF.map_comp, prod_comp, Category.id_comp, Category.comp_id]
      rw [hu]
    dsimp only [beta]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hn, hp]
    erw [reassoc_of% hv]
    rfl

end WeilConjectures.IntegralFiniteExtension
