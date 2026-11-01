/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierModels
import WeilConjectures.SixFunctors.IntegralVerdier.FiniteIntrinsicTensorSymmetry

/-! # Normalized bidual comparison for constant-ring realization

Source: Stacks Project, Tags 00YV, 06YL, 08J9 and 08JA; the coefficient-realization
step of finite intrinsic Verdier biduality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory

private def tensorUncurryAdjunction {C : Type*} [Category C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (a : ∀ K, T.obj K ⊣ H.obj (op K)) (K : C) :
    (Functor.curry.obj (Functor.uncurry.obj T)).obj K ⊣
      (Functor.curry.obj (Functor.uncurry.obj H)).obj (op K) :=
  ((a K).ofNatIsoLeft ((Functor.currying.unitIso.app T).app K)).ofNatIsoRight
    ((Functor.currying.unitIso.app H).app (op K))

private lemma tensorUncurryAdjunction_symm {C : Type*} [Category C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (a : ∀ K, T.obj K ⊣ H.obj (op K)) (K L W : C)
    (f : L ⟶ (H.obj (op K)).obj W) :
    ((tensorUncurryAdjunction T H a K).homEquiv L W).symm f =
      ((a K).homEquiv L W).symm f := by
  unfold tensorUncurryAdjunction
  rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply,
    Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
  change (𝟙 _) ≫ ((a K).homEquiv L W).symm (f ≫ 𝟙 _) = _
  rw [Category.comp_id, Category.id_comp]

private lemma tensorUncurryAdjunction_counit {C : Type*} [Category C]
    (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (a : ∀ K, T.obj K ⊣ H.obj (op K)) (K W : C) :
    (tensorUncurryAdjunction T H a K).counit.app W = (a K).counit.app W := by
  have h := tensorUncurryAdjunction_symm T H a K ((H.obj (op K)).obj W) W (𝟙 _)
  simpa only [Adjunction.homEquiv_counit, Functor.map_id, Category.id_comp] using h

section TensorEquivalence

variable {C D : Type*} [Category C] [Category D]
  (E : C ≌ D) (T : C × C ⥤ C) (H : Cᵒᵖ × C ⥤ C)
  (T' : D × D ⥤ D) (H' : Dᵒᵖ × D ⥤ D)
  (adj : ∀ K, (Functor.curry.obj T).obj K ⊣ (Functor.curry.obj H).obj (op K))
  (adj' : ∀ K, (Functor.curry.obj T').obj K ⊣ (Functor.curry.obj H').obj (op K))
  (μ : E.functor.prod E.functor ⋙ T' ≅ T ⋙ E.functor)

private def tensorClosedMap (K W : C) (M Ω : D)
    (i : E.functor.obj K ≅ M) (w : E.functor.obj W ≅ Ω) :
    E.functor.obj (H.obj (op K, W)) ⟶ H'.obj (op M, Ω) :=
  (adj' M).homEquiv _ _
    (T'.map (Prod.mkHom i.inv (𝟙 _)) ≫ μ.hom.app (K, H.obj (op K, W)) ≫
      E.functor.map ((adj K).counit.app W) ≫ w.hom)

private lemma tensorClosedMap_uncurry (K W : C) (M Ω : D)
    (i : E.functor.obj K ≅ M) (w : E.functor.obj W ≅ Ω) :
    T'.map (Prod.mkHom (𝟙 M) (tensorClosedMap E T H T' H' adj adj' μ K W M Ω i w)) ≫
        (adj' M).counit.app Ω =
      T'.map (Prod.mkHom i.inv (𝟙 _)) ≫ μ.hom.app (K, H.obj (op K, W)) ≫
        E.functor.map ((adj K).counit.app W) ≫ w.hom := by
  exact ((adj' M).homEquiv _ _).symm_apply_apply _

private lemma tensorClosedMap_comp (K L W : C) (M Ω : D)
    (i : E.functor.obj K ≅ M) (w : E.functor.obj W ≅ Ω)
    (f : L ⟶ H.obj (op K, W)) :
    E.functor.map f ≫ tensorClosedMap E T H T' H' adj adj' μ K W M Ω i w =
      (adj' M).homEquiv _ _
        (T'.map (Prod.mkHom i.inv (𝟙 _)) ≫ μ.hom.app (K, L) ≫
          E.functor.map (((adj K).homEquiv L W).symm f) ≫ w.hom) := by
  rw [tensorClosedMap, ← Adjunction.homEquiv_naturality_left]
  congr 1
  rw [Adjunction.homEquiv_counit, E.functor.map_comp]
  have hn := μ.hom.naturality (Prod.mkHom (𝟙 K) f)
  have hn' : T'.map (Prod.mkHom (𝟙 _) (E.functor.map f)) ≫
      μ.hom.app (K, H.obj (op K, W)) =
    μ.hom.app (K, L) ≫ E.functor.map (T.map (Prod.mkHom (𝟙 K) f)) := by
    simpa only [Functor.comp_map, Functor.prod_map, E.functor.map_id] using hn
  have hi : T'.map (Prod.mkHom (𝟙 M) (E.functor.map f)) ≫
      T'.map (Prod.mkHom i.inv (𝟙 _)) =
    T'.map (Prod.mkHom i.inv (𝟙 _)) ≫
      T'.map (Prod.mkHom (𝟙 _) (E.functor.map f)) := by
    simp only [← T'.map_comp, prod_comp, Category.id_comp, Category.comp_id]
  simp only [Category.assoc]
  change T'.map (Prod.mkHom (𝟙 M) (E.functor.map f)) ≫ _ = _
  rw [← Category.assoc, hi, Category.assoc, reassoc_of% hn']
  rfl

private lemma tensorClosedMap_isIso (K W : C) (M Ω : D)
    (i : E.functor.obj K ≅ M) (w : E.functor.obj W ≅ Ω) :
    IsIso (tensorClosedMap E T H T' H' adj adj' μ K W M Ω i w) := by
  have hb (L : C) : Function.Bijective
      (fun f : E.functor.obj L ⟶ E.functor.obj (H.obj (op K, W)) ↦
        f ≫ tensorClosedMap E T H T' H' adj adj' μ K W M Ω i w) := by
    let e : (L ⟶ H.obj (op K, W)) ≃ (E.functor.obj L ⟶ H'.obj (op M, Ω)) :=
      ((adj K).homEquiv L W).symm.trans
        (E.fullyFaithfulFunctor.homEquiv.trans
          (((T'.mapIso (Iso.prod i (Iso.refl (E.functor.obj L)))).symm ≪≫
              μ.app (K, L)).symm.homCongr w |>.trans ((adj' M).homEquiv _ _)))
    have he : (fun f : L ⟶ H.obj (op K, W) ↦
        E.functor.map f ≫ tensorClosedMap E T H T' H' adj adj' μ K W M Ω i w) = e := by
      funext f
      rw [tensorClosedMap_comp]
      dsimp [e, Iso.homCongr, Functor.FullyFaithful.homEquiv, Functor.mapIso, Iso.prod]
      simp only [Category.assoc]
    have h := e.bijective
    rw [← he] at h
    exact (Function.Bijective.of_comp_iff _ E.fullyFaithfulFunctor.homEquiv.bijective).mp h
  let c := tensorClosedMap E T H T' H' adj adj' μ K W M Ω i w
  let j := E.counitIso.app (H'.obj (op M, Ω))
  obtain ⟨g, hg⟩ := (hb (E.inverse.obj (H'.obj (op M, Ω)))).2 j.hom
  change g ≫ c = j.hom at hg
  have hr : (j.inv ≫ g) ≫ c = 𝟙 _ := by
    rw [Category.assoc, hg]
    exact j.inv_hom_id
  refine ⟨⟨j.inv ≫ g, ?_, hr⟩⟩
  apply (hb (H.obj (op K, W))).1
  change (c ≫ (j.inv ≫ g)) ≫ c = (𝟙 _) ≫ c
  rw [Category.assoc, hr]
  exact Category.comp_id c |>.trans (Category.id_comp c).symm

private lemma tensorClosedMap_evaluation (K W : C) (M Ω : D)
    (i : E.functor.obj K ≅ M) (w : E.functor.obj W ≅ Ω) :
    T'.map (Prod.mkHom i.hom
        (tensorClosedMap E T H T' H' adj adj' μ K W M Ω i w)) ≫
        (adj' M).counit.app Ω =
      μ.hom.app (K, H.obj (op K, W)) ≫ E.functor.map ((adj K).counit.app W) ≫
        w.hom := by
  calc
    _ = T'.map (Prod.mkHom i.hom (𝟙 _)) ≫
        (T'.map (Prod.mkHom (𝟙 M)
          (tensorClosedMap E T H T' H' adj adj' μ K W M Ω i w)) ≫
            (adj' M).counit.app Ω) := by
      rw [← Category.assoc, ← T'.map_comp]
      simp only [prod_comp, Category.comp_id, Category.id_comp]
    _ = _ := by
      rw [tensorClosedMap_uncurry]
      simp only [← Category.assoc]
      rw [← T'.map_comp]
      simp only [prod_comp, Iso.hom_inv_id, Category.id_comp, ← prod_id,
        T'.map_id, Category.id_comp]

private lemma tensorBidualComparison
    (b : ∀ K L : C, T.obj (K, L) ≅ T.obj (L, K))
    (b' : ∀ K L : D, T'.obj (K, L) ≅ T'.obj (L, K))
    (hs : ∀ (K L K' L' : D) (f : K ⟶ K') (g : L ⟶ L'),
      T'.map (Prod.mkHom f g) ≫ (b' K' L').hom =
        (b' K L).hom ≫ T'.map (Prod.mkHom g f))
    (hμ : ∀ K L, μ.hom.app (K, L) ≫ E.functor.map (b K L).hom =
      (b' (E.functor.obj K) (E.functor.obj L)).hom ≫ μ.hom.app (L, K))
    (W K : C) (Ω M : D) (w : E.functor.obj W ≅ Ω) (i : E.functor.obj K ≅ M)
    (δ : K ⟶ H.obj (op (H.obj (op K, W)), W))
    (hδ : ((adj (H.obj (op K, W))).homEquiv K W).symm δ =
      (b (H.obj (op K, W)) K).hom ≫ (adj K).counit.app W) :
    ∃ c : E.functor.obj (H.obj (op (H.obj (op K, W)), W)) ≅
        H'.obj (op (H'.obj (op M, Ω)), Ω),
      i.hom ≫ (adj' (H'.obj (op M, Ω))).homEquiv M Ω
          ((b' (H'.obj (op M, Ω)) M).hom ≫ (adj' M).counit.app Ω) =
        E.functor.map δ ≫ c.hom := by
  let DK := H.obj (op K, W)
  let DM := H'.obj (op M, Ω)
  have := tensorClosedMap_isIso E T H T' H' adj adj' μ K W M Ω i w
  let d : E.functor.obj DK ≅ DM :=
    asIso (tensorClosedMap E T H T' H' adj adj' μ K W M Ω i w)
  have := tensorClosedMap_isIso E T H T' H' adj adj' μ DK W DM Ω d w
  let c : E.functor.obj (H.obj (op DK, W)) ≅ H'.obj (op DM, Ω) :=
    asIso (tensorClosedMap E T H T' H' adj adj' μ DK W DM Ω d w)
  have hd : T'.map (Prod.mkHom i.hom d.hom) ≫ (adj' M).counit.app Ω =
      μ.hom.app (K, DK) ≫ E.functor.map ((adj K).counit.app W) ≫ w.hom :=
    tensorClosedMap_evaluation E T H T' H' adj adj' μ K W M Ω i w
  have hc : T'.map (Prod.mkHom d.hom c.hom) ≫ (adj' DM).counit.app Ω =
      μ.hom.app (DK, H.obj (op DK, W)) ≫
        E.functor.map ((adj DK).counit.app W) ≫ w.hom :=
    tensorClosedMap_evaluation E T H T' H' adj adj' μ DK W DM Ω d w
  have hleft : T'.map (Prod.mkHom d.hom (𝟙 (E.functor.obj K))) ≫
        (T'.map (Prod.mkHom (𝟙 DM) i.hom) ≫
          ((b' DM M).hom ≫ (adj' M).counit.app Ω)) =
      μ.hom.app (DK, K) ≫
        E.functor.map ((b DK K).hom ≫ (adj K).counit.app W) ≫ w.hom := by
    calc
      _ = (T'.map (Prod.mkHom d.hom i.hom) ≫ (b' DM M).hom) ≫
          (adj' M).counit.app Ω := by
        simp only [← Category.assoc, ← T'.map_comp, prod_comp,
          Category.id_comp, Category.comp_id]
      _ = (b' (E.functor.obj DK) (E.functor.obj K)).hom ≫
          (T'.map (Prod.mkHom i.hom d.hom) ≫ (adj' M).counit.app Ω) := by
        rw [hs]
        exact Category.assoc _ _ _
      _ = _ := by
        rw [hd, ← Category.assoc, ← hμ DK K, E.functor.map_comp]
        simp only [Category.assoc]
  have hn : T'.map (Prod.mkHom (𝟙 (E.functor.obj DK)) (E.functor.map δ)) ≫
      μ.hom.app (DK, H.obj (op DK, W)) =
        μ.hom.app (DK, K) ≫ E.functor.map (T.map (Prod.mkHom (𝟙 DK) δ)) := by
    simpa only [Functor.comp_map, Functor.prod_map, E.functor.map_id] using
      μ.hom.naturality (Prod.mkHom (𝟙 DK) δ)
  have hδ' : T.map (Prod.mkHom (𝟙 DK) δ) ≫ (adj DK).counit.app W =
      (b DK K).hom ≫ (adj K).counit.app W := hδ
  have hright : T'.map (Prod.mkHom d.hom (𝟙 (E.functor.obj K))) ≫
        (T'.map (Prod.mkHom (𝟙 DM) (E.functor.map δ)) ≫
          (T'.map (Prod.mkHom (𝟙 DM) c.hom) ≫ (adj' DM).counit.app Ω)) =
      μ.hom.app (DK, K) ≫
        E.functor.map ((b DK K).hom ≫ (adj K).counit.app W) ≫ w.hom := by
    calc
      _ = T'.map (Prod.mkHom (𝟙 (E.functor.obj DK)) (E.functor.map δ)) ≫
          (T'.map (Prod.mkHom d.hom c.hom) ≫ (adj' DM).counit.app Ω) := by
        simp only [← Category.assoc, ← T'.map_comp, prod_comp,
          Category.id_comp, Category.comp_id]
      _ = _ := by
        rw [hc, ← Category.assoc, hn]
        simp only [Category.assoc]
        rw [← E.functor.map_comp_assoc, hδ']
  refine ⟨c, ?_⟩
  apply ((adj' DM).homEquiv _ _).symm.injective
  have : IsIso (T'.map (Prod.mkHom d.hom (𝟙 (E.functor.obj K)))) :=
    (T'.mapIso (d.prod (Iso.refl (E.functor.obj K)))).isIso_hom
  apply (cancel_epi (T'.map (Prod.mkHom d.hom (𝟙 (E.functor.obj K))))).1
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply,
    Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_counit]
  change T'.map (Prod.mkHom d.hom (𝟙 (E.functor.obj K))) ≫
      (T'.map (Prod.mkHom (𝟙 DM) i.hom) ≫
        ((b' DM M).hom ≫ (adj' M).counit.app Ω)) =
    T'.map (Prod.mkHom d.hom (𝟙 (E.functor.obj K))) ≫
      (T'.map (Prod.mkHom (𝟙 DM) (E.functor.map δ)) ≫
        (T'.map (Prod.mkHom (𝟙 DM) c.hom) ≫ (adj' DM).counit.app Ω))
  exact hleft.trans hright.symm

end TensorEquivalence

private lemma tensorBidualComparison_curried
    {C D : Type*} [Category C] [Category D]
    (E : C ≌ D) (T : C ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ C)
    (T' : D × D ⥤ D) (H' : Dᵒᵖ × D ⥤ D)
    (a : ∀ K, T.obj K ⊣ H.obj (op K))
    (a' : ∀ K, (Functor.curry.obj T').obj K ⊣ (Functor.curry.obj H').obj (op K))
    (μ : E.functor.prod E.functor ⋙ T' ≅ Functor.uncurry.obj T ⋙ E.functor)
    (b : T ≅ T.flip) (b' : ∀ K L : D, T'.obj (K, L) ≅ T'.obj (L, K))
    (hs : ∀ (K L K' L' : D) (f : K ⟶ K') (g : L ⟶ L'),
      T'.map (Prod.mkHom f g) ≫ (b' K' L').hom =
        (b' K L).hom ≫ T'.map (Prod.mkHom g f))
    (hμ : ∀ K L, μ.hom.app (K, L) ≫ E.functor.map ((b.inv.app L).app K) =
      (b' (E.functor.obj K) (E.functor.obj L)).hom ≫ μ.hom.app (L, K))
    (W K : C) (Ω M : D) (w : E.functor.obj W ≅ Ω) (i : E.functor.obj K ≅ M)
    (e : (T.obj ((H.obj (op K)).obj W)).obj K ⟶ W)
    (δ : K ⟶ (dualityDoubleFunctor H W).obj K)
    (he : (a K).homEquiv _ W (((b.app K).app ((H.obj (op K)).obj W)).hom ≫ e) = 𝟙 _)
    (hδ : δ = (a ((H.obj (op K)).obj W)).homEquiv K W e) :
    ∃ c : E.functor.obj ((dualityDoubleFunctor H W).obj K) ≅
        H'.obj (op (H'.obj (op M, Ω)), Ω),
      i.hom ≫ (a' (H'.obj (op M, Ω))).homEquiv M Ω
          ((b' (H'.obj (op M, Ω)) M).hom ≫ (a' M).counit.app Ω) =
        E.functor.map δ ≫ c.hom := by
  let DK := (H.obj (op K)).obj W
  have heval : ((b.app K).app DK).hom ≫ e = (a K).counit.app W := by
    calc
      _ = ((a K).homEquiv DK W).symm
          ((a K).homEquiv DK W (((b.app K).app DK).hom ≫ e)) :=
        (((a K).homEquiv DK W).symm_apply_apply _).symm
      _ = ((a K).homEquiv DK W).symm (𝟙 _) := congrArg _ he
      _ = _ := by
        rw [Adjunction.homEquiv_counit, Functor.map_id, Category.id_comp]
  have he' : e = ((b.app K).app DK).inv ≫ (a K).counit.app W := by
    rw [← heval, Iso.inv_hom_id_assoc]
  have hδ₀ : ((a DK).homEquiv K W).symm δ =
      ((b.app K).app DK).inv ≫ (a K).counit.app W :=
    (congrArg (((a DK).homEquiv K W).symm) hδ).trans
      ((((a DK).homEquiv K W).symm_apply_apply e).trans he')
  have hδ' : ((tensorUncurryAdjunction T H a DK).homEquiv K W).symm δ =
      ((b.app K).app DK).inv ≫ (tensorUncurryAdjunction T H a K).counit.app W := by
    rw [tensorUncurryAdjunction_symm, tensorUncurryAdjunction_counit]
    exact hδ₀
  exact tensorBidualComparison E (Functor.uncurry.obj T) (Functor.uncurry.obj H)
    T' H' (tensorUncurryAdjunction T H a) a' μ
    (fun L N ↦ ((b.app N).app L).symm) b' hs hμ W K Ω M w i δ hδ'

private lemma tensorBidualComparison_native
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalClosed C]
    (E : C ≌ D)
    (T' : D × D ⥤ D) (H' : Dᵒᵖ × D ⥤ D)
    (a' : ∀ K, (Functor.curry.obj T').obj K ⊣ (Functor.curry.obj H').obj (op K))
    (μ : E.functor.prod E.functor ⋙ T' ≅
      Functor.uncurry.obj (MonoidalCategory.curriedTensor C) ⋙ E.functor)
    (b : MonoidalCategory.curriedTensor C ≅ (MonoidalCategory.curriedTensor C).flip)
    (b' : ∀ K L : D, T'.obj (K, L) ≅ T'.obj (L, K))
    (hs : ∀ (K L K' L' : D) (f : K ⟶ K') (g : L ⟶ L'),
      T'.map (Prod.mkHom f g) ≫ (b' K' L').hom =
        (b' K L).hom ≫ T'.map (Prod.mkHom g f))
    (hμ : ∀ K L, μ.hom.app (K, L) ≫ E.functor.map ((b.inv.app L).app K) =
      (b' (E.functor.obj K) (E.functor.obj L)).hom ≫ μ.hom.app (L, K))
    (W K : C) (Ω M : D) (w : E.functor.obj W ≅ Ω) (i : E.functor.obj K ≅ M)
    (e : ((MonoidalCategory.curriedTensor C).obj
      (((MonoidalClosed.internalHom (C := C)).obj (op K)).obj W)).obj K ⟶ W)
    (δ : K ⟶ (dualityDoubleFunctor (MonoidalClosed.internalHom (C := C)) W).obj K)
    (he : (MonoidalClosed.internalHomAdjunction₂.adj K).homEquiv _ W
      (((b.app K).app (((MonoidalClosed.internalHom (C := C)).obj (op K)).obj W)).hom ≫ e) =
        𝟙 _)
    (hδ : δ = (MonoidalClosed.internalHomAdjunction₂.adj
      (((MonoidalClosed.internalHom (C := C)).obj (op K)).obj W)).homEquiv K W e) :
    ∃ c : E.functor.obj ((dualityDoubleFunctor (MonoidalClosed.internalHom (C := C)) W).obj K) ≅
        H'.obj (op (H'.obj (op M, Ω)), Ω),
      i.hom ≫ (a' (H'.obj (op M, Ω))).homEquiv M Ω
          ((b' (H'.obj (op M, Ω)) M).hom ≫ (a' M).counit.app Ω) =
        E.functor.map δ ≫ c.hom := by
  exact tensorBidualComparison_curried E (MonoidalCategory.curriedTensor C)
    MonoidalClosed.internalHom T' H' MonoidalClosed.internalHomAdjunction₂.adj a' μ
    b b' hs hμ W K Ω M w i e δ he hδ

private lemma proEtaleTensorBidualComparison
    {A : Type*} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    {D : Type*} [Category D] (X : Scheme.{u})
    (E : DerivedCategory (Sheaf (ProEt.topology X) A) ≌ D)
    (T' : D × D ⥤ D) (H' : Dᵒᵖ × D ⥤ D)
    (a' : ∀ K, (Functor.curry.obj T').obj K ⊣ (Functor.curry.obj H').obj (op K))
    (μ : E.functor.prod E.functor ⋙ T' ≅
      Functor.uncurry.obj (MonoidalCategory.curriedTensor _) ⋙ E.functor)
    (b' : ∀ K L : D, T'.obj (K, L) ≅ T'.obj (L, K))
    (hs : ∀ (K L K' L' : D) (f : K ⟶ K') (g : L ⟶ L'),
      T'.map (Prod.mkHom f g) ≫ (b' K' L').hom =
        (b' K L).hom ≫ T'.map (Prod.mkHom g f))
    (W K : DerivedCategory (Sheaf (ProEt.topology X) A))
    (h : ProEtale.AmbientDualityPairing A X W)
    (hμ : ∀ K L, μ.hom.app (K, L) ≫ E.functor.map ((h.choose.inv.app L).app K) =
      (b' (E.functor.obj K) (E.functor.obj L)).hom ≫ μ.hom.app (L, K))
    (Ω M : D) (w : E.functor.obj W ≅ Ω) (i : E.functor.obj K ≅ M) :
    ∃ c : E.functor.obj ((dualityDoubleFunctor MonoidalClosed.internalHom W).obj K) ≅
        H'.obj (op (H'.obj (op M, Ω)), Ω),
      i.hom ≫ (a' (H'.obj (op M, Ω))).homEquiv M Ω
          ((b' (H'.obj (op M, Ω)) M).hom ≫ (a' M).counit.app Ω) =
        E.functor.map (ProEtale.AmbientDualityPairing.bidualityMap A X h K) ≫ c.hom := by
  exact tensorBidualComparison_native E T' H' a' μ h.choose b' hs hμ W K Ω M w i
    (h.choose_spec.2.choose K) (h.choose_spec.2.choose_spec.2.choose K)
    (h.choose_spec.2.choose_spec.1 K) (h.choose_spec.2.choose_spec.2.choose_spec.1 K)

end CategoryTheory

namespace WeilConjectures.IntegralVerdier

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] ProEtale.sheafBraidedCategory
attribute [local irreducible] DerivedCategory.monoidalClosed
  MonoidalClosed.internalHom sfIntrinsicDerivedEquivalence
  finiteIntrinsicTensorRealization

/-- The canonical constant-ring realization identifies the normalized evaluation
transposes, up to the two closed-Hom comparisons and the input isomorphism.
This is a statement about arbitrary objects and finite commutative rings; it has no
constructibility, Tor, finite-field, exceptional-functor, or biduality assumption.

Source: the realization step of lem-sf-finite-intrinsic-verdier-biduality;
Stacks Project, Tags 00YV, 06YL, 08J9 and 08JA
(blueprint: lem-sf-finite-intrinsic-bidual-comparison).

Proof: extend fixed scalar actions along the locally bijective constant-scalar unit.
On module sheaves the resulting exact equivalence preserves the tensor product:
the tensorator sends the pair of scalar-unit images of x and y to the scalar-unit
image of x tensor y. Its inverse is fixed by the same generators. Apply this
comparison termwise on K-flat resolutions and totalize. The Koszul swap commutes
with it on each homogeneous pair, including the sign (-1)^(ij). Local generation
and the localization universal property extend these equations to derived objects.
The tensor-Hom adjunction and full faithfulness of the equivalence then give the
closed comparison F RHom(K,W) isomorphic to RHom(F K,F W). Postcompose in the
second input with w, and precompose in the first input with i inverse, to obtain
the dual comparison at K. Apply the closed comparison once more at RHom(K,W).
Compose it with the inverse of the Hom map induced contravariantly by the first
dual comparison. This gives c. To check the displayed equation, untranspose it.
The source pairing is uniquely normalized by the descended Koszul symmetry and
the tensor-Hom identity. The fields a.evaluation and s.representative give the
same signed Hom-complex evaluation after realization. Thus the two untransposed
maps agree on K-flat tests and K-injective targets, and hence in the derived
category. Naturality in the first tensor input, expressed by he, and symmetry
naturality hs give the final conjugation by i. Transposition is injective.
Zero rings, zero objects and empty sites satisfy the same generator equations;
no nonzero or perfectness condition is used. -/
theorem finiteIntrinsicBidualComparison
    (X : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (a : IntegralHom.TensorPresentation.{u, u} X (proEtaleConstantRing X B))
    (s : SignedSymmetry X (proEtaleConstantRing X B) a)
    (hs : ∀ (K L K' L' : proEtaleDerivedCategory X B)
      (f : K ⟶ K') (g : L ⟶ L'),
      a.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
        (s.swap K L).hom ≫ a.tensor.map (Prod.mkHom g f))
    (he : ∀ (K K' W : proEtaleDerivedCategory X B) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X (proEtaleConstantRing X B)).map
          (Prod.mkHom f.op (𝟙 W)))) ≫ (a.adjunction K').counit.app W =
        a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app W)
    (W K : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
    (h : ProEtale.AmbientDualityPairing
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X W)
    (ω M : proEtaleDerivedCategory X B)
    (w : (sfIntrinsicDerivedEquivalence X B).functor.obj W ≅ ω)
    (i : (sfIntrinsicDerivedEquivalence X B).functor.obj K ≅ M) :
    ∃ c : (sfIntrinsicDerivedEquivalence X B).functor.obj
        ((dualityDoubleFunctor MonoidalClosed.internalHom W).obj K) ≅
          (IntegralHom.hom.{u, u} X (proEtaleConstantRing X B)).obj
            (op ((IntegralHom.hom.{u, u} X (proEtaleConstantRing X B)).obj (op M, ω)), ω),
      i.hom ≫ delta X a s ω M =
        (sfIntrinsicDerivedEquivalence X B).functor.map
          (ProEtale.AmbientDualityPairing.bidualityMap
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) X h K) ≫ c.hom := by
  have _firstInputNaturality := he
  let b := h.choose
  let μ := finiteIntrinsicTensorRealization X B a
  have hμ := finiteIntrinsicTensorSymmetry X B a s hs b h.choose_spec.1
  have result := proEtaleTensorBidualComparison X (sfIntrinsicDerivedEquivalence X B)
    a.tensor (IntegralHom.hom.{u, u} X (proEtaleConstantRing X B)) a.adjunction μ
    s.swap hs W K h hμ ω M w i
  dsimp only [delta, restrictionDualDelta, restrictionDualEvaluation]
  exact result

end WeilConjectures.IntegralVerdier
