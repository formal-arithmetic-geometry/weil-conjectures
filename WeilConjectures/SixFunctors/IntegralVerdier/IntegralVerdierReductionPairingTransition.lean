/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierModels
import WeilConjectures.SixFunctors.IntegralHom.Tensor.IntegralTensorRestrictionTransition

/-! # Split lemma: Finite transition compatibility of normalized evaluation

Source: Stacks Project, Tags 06YL and 08J9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uC uD vC vD
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralVerdier

private theorem restricted_evaluation
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    (T : C × C ⥤ C) (S : D × D ⥤ D)
    (F : C ⥤ D) (U : D ⥤ C) (adj : F ⊣ U)
    (μ : T ⋙ F ≅ F.prod F ⋙ S)
    (K H W : C) (N V : D) (c : F.obj H ⟶ N)
    (e : S.obj (F.obj K, N) ⟶ V) (f : T.obj (K, H) ⟶ W) (r : F.obj W ⟶ V)
    (hc : S.map (Prod.mkHom (𝟙 (F.obj K)) c) ≫ e =
      μ.inv.app (K, H) ≫ F.map f ≫ r) :
    T.map (Prod.mkHom (𝟙 K) (U.map c)) ≫
        adj.homEquiv _ _ (μ.hom.app (K, U.obj N) ≫
          S.map (Prod.mkHom (𝟙 (F.obj K)) (adj.counit.app N)) ≫ e) =
      adj.homEquiv _ _ (μ.hom.app (K, U.obj (F.obj H)) ≫
        S.map (Prod.mkHom (𝟙 (F.obj K)) (adj.counit.app (F.obj H))) ≫
        μ.inv.app (K, H)) ≫ U.map (F.map f ≫ r) := by
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  congr 1
  have hμ := μ.hom.naturality (Prod.mkHom (𝟙 K) (U.map c))
  simp only [Functor.comp_map, Functor.prod_map] at hμ
  rw [← Category.assoc, ← Category.assoc, hμ]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, ← S.map_comp]
  have hε := adj.counit.naturality c
  dsimp only [Functor.comp_map, Functor.id_map] at hε
  have hpair : Prod.mkHom (F.map (𝟙 K)) (F.map (U.map c)) ≫
      Prod.mkHom (𝟙 (F.obj K)) (adj.counit.app N) =
      Prod.mkHom (𝟙 (F.obj K)) (adj.counit.app (F.obj H)) ≫
        Prod.mkHom (𝟙 (F.obj K)) c := by
    ext <;> simp [hε]
  rw [hpair, S.map_comp, Category.assoc, hc]

private theorem transpose_post
    {C : Type uC} {B : Type uD} [Category.{vC} C] [Category.{vD} B]
    {L : C ⥤ B} {R : B ⥤ C} (adj : L ⊣ R)
    {A : C} {V W : B} (f : L.obj A ⟶ V) (r : V ⟶ W) :
    L.map (adj.homEquiv A V f ≫ R.map r) ≫ adj.counit.app W = f ≫ r := by
  rw [← Adjunction.homEquiv_naturality_right]
  exact (adj.homEquiv A W).symm_apply_apply (f ≫ r)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem finiteEvaluation_comparison
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl))
    (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n)
    (K : Ambient l E X) (n : ℕ) :
    a.tensor.map (Prod.mkHom (𝟙 K)
        ((scalarReductionDerivedRestriction l E X n).map
          (comparison l E X D hl (m n) ω r K))) ≫
        finiteEvaluation l E X D hl m K n =
      IntegralHom.restrictionTensor l E X D hl (m n) K
          ((dual l E X ω.obj).obj (op K)) ≫
        (sfDerivedReductionRestricted l E X n).map ((a.adjunction K).counit.app ω.obj) ≫
        (scalarReductionDerivedRestriction l E X n).map (r n).hom := by
  have hc : (m n).target.tensor.map
        (Prod.mkHom (𝟙 ((scalarReductionDerivedExtension l E X n).obj K))
          (comparison l E X D hl (m n) ω r K)) ≫
      ((m n).target.adjunction ((scalarReductionDerivedExtension l E X n).obj K)).counit.app
        (integralDualizingFiniteTerm l E D X n) =
      (m n).mu.inv.app (K, (dual l E X ω.obj).obj (op K)) ≫
        (scalarReductionDerivedExtension l E X n).map ((a.adjunction K).counit.app ω.obj) ≫
          (r n).hom := by
    simpa only [comparison, Functor.curry_obj_obj_map, Functor.curry_obj_obj_obj,
      integralDerivedReduction, Functor.id_obj, Category.assoc] using
      transpose_post
        ((m n).target.adjunction ((scalarReductionDerivedExtension l E X n).obj K))
      ((m n).mu.inv.app (K, (dual l E X ω.obj).obj (op K)) ≫
        (scalarReductionDerivedExtension l E X n).map ((a.adjunction K).counit.app ω.obj))
      (r n).hom
  simpa only [finiteEvaluation, IntegralHom.restrictionTensor, Functor.map_comp,
    sfDerivedReductionRestricted, finiteTerms, Functor.comp_map, Functor.comp_obj,
    Functor.id_obj, Category.assoc] using
    restricted_evaluation a.tensor (m n).target.tensor
      (scalarReductionDerivedExtension l E X n) (scalarReductionDerivedRestriction l E X n)
      (derivedScalarExtensionRestrictionAdjunction.{u, u} l E X n).choose (m n).mu
      K ((dual l E X ω.obj).obj (op K)) ω.obj _ _
      (comparison l E X D hl (m n) ω r K)
      (((m n).target.adjunction ((scalarReductionDerivedExtension l E X n).obj K)).counit.app
        (integralDualizingFiniteTerm l E D X n))
      ((a.adjunction K).counit.app ω.obj) (r n).hom hc

/-- Finite transition compatibility of normalized evaluation.

Source: Stacks Project, Tags 06YL and 08J9.

Prove the finite transition square using normalized K-flat/K-injective models.
The coefficient unit and quotient transition preserve evaluation; transpose through the finite
adjunction and cancel the comparison isomorphisms.
(blueprint: lem-sf-integral-verdier-reduction-pairing-transition). -/
theorem reductionPairing_transition
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheaf l E X D hl))
    (s : SignedSymmetry X (completedIntegralCommRingSheaf l E X D hl) a)
    (hs : ∀ (K L K' L' : Ambient l E X) (f : K ⟶ K') (g : L ⟶ L'),
      a.tensor.map (Prod.mkHom f g) ≫ (s.swap K' L').hom =
        (s.swap K L).hom ≫ a.tensor.map (Prod.mkHom g f))
    (m : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
    (t : ∀ n : ℕ, SignedSymmetry X (integralCoefficientCommRingSheaf l E X n)
      (m n).target)
    (ht : ∀ (n : ℕ) (K L K' L' : DerivedCategory (scalarReductionTarget l E X n))
      (f : K ⟶ K') (g : L ⟶ L'),
      (m n).target.tensor.map (Prod.mkHom f g) ≫ ((t n).swap K' L').hom =
        ((t n).swap K L).hom ≫ (m n).target.tensor.map (Prod.mkHom g f))
    (he : ∀ (K K' W : Ambient l E X) (f : K' ⟶ K),
      a.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X (completedIntegralCommRingSheaf l E X D hl)).map
          (Prod.mkHom f.op (𝟙 W)))) ≫ (a.adjunction K').counit.app W =
      a.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (a.adjunction K).counit.app W)
    (het : ∀ (n : ℕ) (K K' W : DerivedCategory (scalarReductionTarget l E X n))
      (f : K' ⟶ K),
      (m n).target.tensor.map (Prod.mkHom (𝟙 K')
        ((IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
          (Prod.mkHom f.op (𝟙 W)))) ≫ ((m n).target.adjunction K').counit.app W =
      (m n).target.tensor.map (Prod.mkHom f (𝟙 _)) ≫
        ((m n).target.adjunction K).counit.app W)
    (ω : sfIntegralConstructibleCategory l E X)
    (r : ∀ n : ℕ, (scalarReductionDerivedExtension l E X n).obj ω.obj ≅
      integralDualizingFiniteTerm l E D X n)
    (h : ∀ (K : Ambient l E X) (n : ℕ), IsIso (comparison l E X D hl (m n) ω r K)) :
    (∀ (K : Ambient l E X) (n : ℕ),
      a.tensor.map (Prod.mkHom (𝟙 K) (finiteTransition l E X D hl m ω r K (h K) n)) ≫
        finiteEvaluation l E X D hl m K n =
      finiteEvaluation l E X D hl m K (n + 1) ≫ dualizingTransition l E X D ω r n) := by
  -- Retain the original interface; this transition calculation needs no signed swap.
  have _ := hs
  have _ := ht
  have _ := he
  have _ := het
  intro K n
  let V := (dual l E X ω.obj).obj (op K)
  let T := (Functor.curry.obj a.tensor).obj K
  let c (j : ℕ) := restrictedComparison l E X D hl m ω r K (h K) j
  let d (j : ℕ) := (scalarReductionDerivedRestriction l E X j).mapIso (r j)
  let b (j : ℕ) := IntegralHom.restrictionTensor l E X D hl (m j) K V
  let e : a.tensor.obj (K, V) ⟶ ω.obj := (a.adjunction K).counit.app ω.obj
  have heval (j : ℕ) :
      T.map (c j).hom ≫ finiteEvaluation l E X D hl m K j =
        b j ≫ (sfDerivedReductionRestricted l E X j).map e ≫ (d j).hom := by
    exact finiteEvaluation_comparison D l hl E X a m ω r K j
  have hb : T.map ((sfDerivedReductionTransition l E X n).app V) ≫ b n =
      b (n + 1) ≫ (sfDerivedReductionTransition l E X n).app (a.tensor.obj (K, V)) :=
    IntegralHom.restrictionTensor_transition l E X D hl a m K V n
  change T.map (finiteTransition l E X D hl m ω r K (h K) n) ≫ _ = _
  -- Move to the untransported quotient terms before comparing the evaluations.
  apply (cancel_epi (T.map (c (n + 1)).hom)).mp
  simp only [← Category.assoc]
  rw [← T.map_comp]
  have hc : (c (n + 1)).hom ≫ finiteTransition l E X D hl m ω r K (h K) n =
      (sfDerivedReductionTransition l E X n).app V ≫ (c n).hom := by
    simp only [finiteTransition, c, Iso.hom_inv_id_assoc]
    rfl
  rw [hc, T.map_comp]
  simp only [Category.assoc]
  rw [heval, ← Category.assoc (T.map _) (b n), hb]
  simp only [Category.assoc]
  rw [← (sfDerivedReductionTransition l E X n).naturality_assoc e]
  rw [← Category.assoc (T.map (c (n + 1)).hom), heval (n + 1)]
  dsimp only [dualizingTransition, d]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end WeilConjectures.IntegralVerdier
