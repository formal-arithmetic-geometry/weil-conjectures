/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierModels
import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierReductionTensorSymmetry

/-! # Uncurried reduction compatibility for the signed Verdier delta

This is the mate calculation used to prove the reduction compatibility of the signed
Verdier delta.  It is separated from the final statement so that the remaining proof
only uses injectivity of the finite tensor--Hom adjunction.

Source: Stacks Project, Tags 06YL and 08J9; the uncurrying step in the proof of
`lem-sf-integral-verdier-reduction-pairing-delta`.
(blueprint: lem-sf-integral-verdier-reduction-pairing-delta-uncurried).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralVerdier

private theorem uncurry_precomp
    {C : Type*} [Category* C] (T : C × C ⥤ C) (H : Cᵒᵖ × C ⥤ C)
    (adj : ∀ P, (Functor.curry.obj T).obj P ⊣
      (Functor.curry.obj H).obj (op P))
    (he : ∀ (P P' W : C) (f : P' ⟶ P),
      T.map (Prod.mkHom (𝟙 P') (H.map (Prod.mkHom f.op (𝟙 W)))) ≫
          (adj P').counit.app W =
        T.map (Prod.mkHom f (𝟙 _)) ≫ (adj P).counit.app W)
    {V P P' W : C} (f : P' ⟶ P) (g : V ⟶ H.obj (op P, W)) :
    ((adj P').homEquiv V W).symm (g ≫ H.map (Prod.mkHom f.op (𝟙 W))) =
      T.map (Prod.mkHom f (𝟙 V)) ≫ ((adj P).homEquiv V W).symm g := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  change T.map (Prod.mkHom (𝟙 P') (g ≫ H.map (Prod.mkHom f.op (𝟙 W)))) ≫
      (adj P').counit.app W =
    T.map (Prod.mkHom f (𝟙 V)) ≫ T.map (Prod.mkHom (𝟙 P) g) ≫
      (adj P).counit.app W
  have hm : Prod.mkHom (𝟙 P') (g ≫ H.map (Prod.mkHom f.op (𝟙 W))) =
      Prod.mkHom (𝟙 P') g ≫ Prod.mkHom (𝟙 P') (H.map (Prod.mkHom f.op (𝟙 W))) := by
    simp only [prod_comp, Category.id_comp]
  have hep := he P P' W f
  change T.map (Prod.mkHom (𝟙 P') (H.map (Prod.mkHom f.op (𝟙 W)))) ≫
    (adj P').counit.app W = T.map (Prod.mkHom f (𝟙 (H.obj (op P, W)))) ≫
      (adj P).counit.app W at hep
  rw [hm, T.map_comp, Category.assoc, hep]
  simp only [← Category.assoc, ← T.map_comp, prod_comp, Category.id_comp, Category.comp_id]

private theorem uncurry_post
    {C : Type*} [Category* C] {L R : C ⥤ C} (a : L ⊣ R)
    {A B B' : C} (q : L.obj A ⟶ B) (r : B ⟶ B') :
    L.map (a.homEquiv A B q ≫ R.map r) ≫ a.counit.app B' = q ≫ r := by
  rw [← Adjunction.homEquiv_naturality_right]
  exact (a.homEquiv A B').symm_apply_apply (q ≫ r)

private theorem uncurry_reduction
    {C : Type*} {B : Type*} [Category* C] [Category* B]
    (T : C × C ⥤ C) (T' : B × B ⥤ B) (F : C ⥤ B)
    (mu : T ⋙ F ≅ F.prod F ⋙ T') (P : C)
    {R : C ⥤ C} {R' : B ⥤ B}
    (a : (Functor.curry.obj T).obj P ⊣ R)
    (b : (Functor.curry.obj T').obj (F.obj P) ⊣ R')
    {V W : C} {N : B} (f : V ⟶ R.obj W) (r : F.obj W ⟶ N) :
    (b.homEquiv (F.obj V) N).symm
      (F.map f ≫ b.homEquiv (F.obj (R.obj W)) (F.obj W)
        (mu.inv.app (P, R.obj W) ≫ F.map (a.counit.app W)) ≫ R'.map r) =
      mu.inv.app (P, V) ≫ F.map ((a.homEquiv V W).symm f) ≫ r := by
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm,
    Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  rw [Adjunction.homEquiv_counit, F.map_comp]
  have hn := mu.inv.naturality (Prod.mkHom (𝟙 P) f)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simpa only [Category.assoc, Functor.curry_obj_obj_map, F.map_id] using
    congrArg (fun q ↦ q ≫ F.map (a.counit.app W) ≫ r) hn

private theorem swap_cancel
    {C : Type*} [Category* C] (T : C × C ⥤ C)
    (s : ∀ P Q, T.obj (P, Q) ≅ T.obj (Q, P))
    (hs : ∀ (P Q P' Q' : C) (f : P ⟶ P') (g : Q ⟶ Q'),
      T.map (Prod.mkHom f g) ≫ (s P' Q').hom =
        (s P Q).hom ≫ T.map (Prod.mkHom g f))
    {P Q Q' W : C} (c : Q ≅ Q') (e : T.obj (P, Q') ⟶ W) :
    T.map (Prod.mkHom c.inv (𝟙 P)) ≫ (s Q P).hom ≫
        T.map (Prod.mkHom (𝟙 P) c.hom) ≫ e = (s Q' P).hom ≫ e := by
  rw [← Category.assoc, hs, Category.assoc, ← Category.assoc
    (T.map (Prod.mkHom (𝟙 P) c.inv)), ← T.map_comp]
  simp only [prod_comp, Category.id_comp, Iso.inv_hom_id, ← prod_id, T.map_id,
    Category.id_comp]

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

set_option linter.unusedVariables false in
/-- The reduced delta identity after uncurrying through the finite adjunction.

The proof expands both delta maps as transposes of evaluation.  Naturality of the
coefficient comparison and of the two tensor presentations moves the reduction map
through evaluation; `he` and `het` supply the two evaluation compatibilities.  The
signed swap is transported by `hs` and `ht`, and the inverse comparison is forced by
contravariance of the internal Hom.  This is the strict mate calculation; the final
curried identity follows from injectivity of the same adjunction hom-equivalence.

The statement is intentionally the uncurried evaluation equality, which is strictly
simpler than the curried delta equality proved from it.
(blueprint: lem-sf-integral-verdier-reduction-pairing-delta-uncurried). -/
theorem reductionPairing_delta_uncurried
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
    ∀ (K : Ambient l E X) (n : ℕ),
      (((m n).target.adjunction
          ((IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).obj
            (op ((scalarReductionDerivedExtension l E X n).obj K),
              integralDualizingFiniteTerm l E D X n))).homEquiv
        ((scalarReductionDerivedExtension l E X n).obj K)
        (integralDualizingFiniteTerm l E D X n)).symm
      ((scalarReductionDerivedExtension l E X n).map (delta X a s ω.obj K) ≫
        comparison l E X D hl (m n) ω r ((dual l E X ω.obj).obj (op K)) ≫
        (IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).map
          (Prod.mkHom (@asIso _ _ _ _ (comparison l E X D hl (m n) ω r K)
            (h K n)).inv.op (𝟙 (integralDualizingFiniteTerm l E D X n)))) =
      ((t n).swap
          ((IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)).obj
            (op ((scalarReductionDerivedExtension l E X n).obj K),
              integralDualizingFiniteTerm l E D X n))
          ((scalarReductionDerivedExtension l E X n).obj K)).hom ≫
        ((m n).target.adjunction
          ((scalarReductionDerivedExtension l E X n).obj K)).counit.app
          (integralDualizingFiniteTerm l E D X n) := by
  intro K n
  let F := scalarReductionDerivedExtension l E X n
  let H := IntegralHom.hom.{u, u} X (integralCoefficientCommRingSheaf l E X n)
  let DK := (dual l E X ω.obj).obj (op K)
  let c := @asIso _ _ _ _ (comparison l E X D hl (m n) ω r K) (h K n)
  have hr :
      (((m n).target.adjunction (F.obj DK)).homEquiv (F.obj K)
        (integralDualizingFiniteTerm l E D X n)).symm
        (F.map (delta X a s ω.obj K) ≫ comparison l E X D hl (m n) ω r DK) =
      (m n).mu.inv.app (DK, K) ≫
        F.map ((s.swap DK K).hom ≫ (a.adjunction K).counit.app ω.obj) ≫ (r n).hom := by
    with_unfolding_all
      simpa only [comparison, delta, restrictionDualDelta, restrictionDualEvaluation,
        DK, dual, F, completedIntegralCommRingSheaf, Functor.flip_obj_obj,
        Functor.curry_obj_obj_obj, Functor.curry_obj_obj_map,
        Equiv.symm_apply_apply, Category.assoc] using
      uncurry_reduction a.tensor (m n).target.tensor F (m n).mu DK
        (a.adjunction DK) ((m n).target.adjunction (F.obj DK))
        (delta X a s ω.obj K) (r n).hom
  have heval : (m n).target.tensor.map (Prod.mkHom (𝟙 (F.obj K)) c.hom) ≫
      ((m n).target.adjunction (F.obj K)).counit.app
        (integralDualizingFiniteTerm l E D X n) =
      (m n).mu.inv.app (K, DK) ≫ F.map ((a.adjunction K).counit.app ω.obj) ≫
        (r n).hom := by
    with_unfolding_all
      simpa only [comparison, c, asIso_hom, DK, F, dual, Functor.flip_obj_obj,
        Functor.curry_obj_obj_obj, Functor.curry_obj_obj_map, Functor.id_obj,
        completedIntegralCommRingSheaf, Category.assoc] using
      uncurry_post (A := F.obj DK) ((m n).target.adjunction (F.obj K))
        ((m n).mu.inv.app (K, DK) ≫ F.map ((a.adjunction K).counit.app ω.obj)) (r n).hom
  rw [← Category.assoc,
    uncurry_precomp (m n).target.tensor H (m n).target.adjunction (het n), hr]
  rw [F.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc ((m n).mu.inv.app (DK, K)),
    reduction_tensor_symmetry D l hl E X a s hs n (m n) (t n) (ht n) DK K]
  simp only [Category.assoc]
  rw [← heval]
  exact swap_cancel (m n).target.tensor (t n).swap (ht n) c
    (((m n).target.adjunction (F.obj K)).counit.app
      (integralDualizingFiniteTerm l E D X n))

end WeilConjectures.IntegralVerdier
