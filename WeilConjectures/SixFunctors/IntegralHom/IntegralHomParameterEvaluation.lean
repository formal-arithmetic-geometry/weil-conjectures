/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
import WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorKoszulExistence
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationCoefficient
import WeilConjectures.SixFunctors.IntegralHom.HomComplexTensorPureEquivalence
import all Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.SixFunctors.IntegralHom.IntegralHomParameterAdjunction
/-! Coherent evaluation for the integral tensor presentation.
Source: the representative evaluation step in the blueprint proof.
(blueprint: lem-sf-integral-hom-parameter-evaluation) -/
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom

open CategoryTheory.MonoidalCategory

section Transport

variable {A : Type*} [Category* A] {H : Aᵒᵖ × A ⥤ A}

/-- Swap a right tensor adjunction using the specified natural tensor exchange. -/
private noncomputable def swappedAdjunction
    (S : CoefficientClosedStructure H) (σ : S.tensor ≅ CategoryTheory.Prod.swap A A ⋙ S.tensor)
    (K : A) : (Functor.curry.obj S.tensor).obj K ⊣
      (Functor.curry.obj H).obj (op K) := by
  letI := S.monoidal
  exact (S.adjunction K).ofNatIsoLeft
    (NatIso.ofComponents (fun X ↦ (σ.app (K, X)).symm) (by
      intro X X' f
      have h := σ.inv.naturality (Prod.mkHom (𝟙 K) f)
      change (f ⊗ₘ 𝟙 K) ≫ σ.inv.app (K, X') = _ at h
      rw [tensorHom_id] at h
      exact h))

private noncomputable def swappedParameterAdjunction
    (S : CoefficientClosedStructure H) (σ : S.tensor ≅ CategoryTheory.Prod.swap A A ⋙ S.tensor) :
    Functor.curry.obj S.tensor ⊣₂ Functor.curry.obj H := by
  let := S.monoidal
  refine parameterAdjunctionOfCounit (swappedAdjunction S σ) ?_
  intro K K' W f
  change S.tensor.map (Prod.mkHom (𝟙 K) (H.map (Prod.mkHom f.op (𝟙 W)))) ≫
      σ.hom.app (K, H.obj (op K, W)) ≫ (S.adjunction K).counit.app W =
    S.tensor.map (Prod.mkHom f (𝟙 _)) ≫
      σ.hom.app (K', H.obj (op K', W)) ≫ (S.adjunction K').counit.app W
  rw [σ.hom.naturality_assoc, σ.hom.naturality_assoc]
  congr 1
  change (H.map (Prod.mkHom f.op (𝟙 W)) ⊗ₘ 𝟙 K) ≫ _ =
    (𝟙 (H.obj (op K', W)) ⊗ₘ f) ≫ _
  rw [tensorHom_id, id_tensorHom]
  exact S.evaluation_naturality K' K W f

private theorem swappedAdjunction_uncurry
    (S : CoefficientClosedStructure H) (σ : S.tensor ≅ CategoryTheory.Prod.swap A A ⋙ S.tensor)
    (K X I : A) (f : X ⟶ H.obj (op K, I)) :
    ((swappedAdjunction S σ K).homEquiv X I).symm f =
      σ.hom.app (K, X) ≫ (S.transpose X K I).symm f := by
  rw [swappedAdjunction, Adjunction.homEquiv_ofNatIsoLeft_symm_apply]
  rfl

private theorem curry_counit
    (F : A × A ⥤ A) (K : A) (adj : (Functor.curry.obj F).obj K ⊣
      (Functor.curry.obj H).obj (op K))
    (X I : A) (f : X ⟶ H.obj (op K, I)) :
    (adj.homEquiv X I).symm f =
      F.map (Prod.mkHom (𝟙 K) f) ≫ adj.counit.app I := by
  rw [Adjunction.homEquiv_symm_apply]
  rfl

private theorem map_comp_exchange {B : Type*} [Category* B] (F : A ⥤ B)
    {X Y Z : A} {W V : B} (a : W ⟶ F.obj X) (b : W ⟶ V)
    (c : V ⟶ F.obj Y) (d : V ⟶ F.obj Z) (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : a ≫ F.map f = b ≫ c) (h' : c ≫ F.map g = d) :
    a ≫ F.map (f ≫ g) = b ≫ d := by
  rw [Functor.map_comp, ← Category.assoc, h, Category.assoc, h']

end Transport

attribute [local irreducible] derivedInternalHomOfUniverses homComplexFunctor
  completedIntegralCommRingSheaf totalPair evaluate homModelMap

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
variable [EssentiallySmall.{t + 1} Y.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}]
set_option maxHeartbeats 800000 in
-- The representative square elaborates independent site and coefficient universes.
/-- The signed representative evaluation uses an adjunction natural in its tensor parameter.

Source: Stacks Tags 08J9 and 06YU; the normalized Koszul exchange construction.
Proof: transport the native adjunction through the natural Koszul exchange. Its
counits are coherent by exchange naturality and the native evaluation law.
Uncurry the representative map and precompose with the signed chain exchange.
Its pure-section formula and localization square give the stated normalization.
(blueprint: lem-sf-integral-hom-parameter-evaluation) -/
theorem tensor_presentation_parameter_evaluation
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (completedIntegralCommRingSheaf l E Y D hl)))
    (T : CoefficientTensorModels (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheaf l E Y D hl) S)
    : ∃ adj : Functor.curry.obj S.tensor ⊣₂
        Functor.curry.obj (hom Y (completedIntegralCommRingSheaf l E Y D hl)),
    ∀ (P I S' : CochainComplex (Modules.{t,u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) ℤ)
      (hP : flat.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl) P)
      (hS : flat.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl) S'), I.IsKInjective →
      ∀ q : S' ⟶ homComplex.{t+1,t,max u (t+1),max u (t+1)}
        (R := completedIntegralCommRingSheaf l E Y D hl) P I,
      ∃ beta : ((totalTensor.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj P).obj S' ⟶ I,
        (∀ (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
          (x : (P.X i).val.obj U) (s : (S'.X j).val.obj U),
          (beta.f (i+j)).val.app U
            (totalPair.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl) P S' i j U x s) =
            (i*j).negOnePow • evaluate.{t,u} Y (completedIntegralCommRingSheaf l E Y D hl)
              P I j i U ((q.f j).val.app U s) x) ∧
        T.comparison.inv.app (⟨P,hP⟩,⟨S',hS⟩) ≫ DerivedCategory.Q.map beta =
          S.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
            (DerivedCategory.Q.map q ≫ homModelMap.{t,u} Y
              (completedIntegralCommRingSheaf l E Y D hl) P I)) ≫
          (adj.adj (DerivedCategory.Q.obj P)).counit.app (DerivedCategory.Q.obj I) := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let R := completedIntegralCommRingSheaf l E Y D hl
  have hkoszul := ringedTensor_koszul_exists.{t + 1, t, u, (max u (t + 1)) + 1} J R S T
  let σ := hkoszul.choose
  have hσ := hkoszul.choose_spec
  refine ⟨swappedParameterAdjunction S σ, ?_⟩
  intro P I S' hP hS _ q
  have hcomponent (K) :
      (swappedParameterAdjunction S σ).adj K = swappedAdjunction S σ K := by
    rfl
  simp only [hcomponent]
  have hrepresentative := hσ P S' hP hS
  let s := hrepresentative.choose
  have hs := hrepresentative.choose_spec.1
  have hsq := hrepresentative.choose_spec.2
  have hpure := homComplexTensor_pure_equivalence.{t, u} Y R S' P I
  change ∃ e : ((coefficientTotalTensor.{u, t + 1, t} J R).obj (S', P) ⟶ I) ≃
      (S' ⟶ homComplex.{t + 1, t, max u (t + 1), max u (t + 1)} (R := R) P I),
    ∀ (f : (coefficientTotalTensor.{u, t + 1, t} J R).obj (S', P) ⟶ I)
      (i j : ℤ) (U : (AlgebraicGeometry.Scheme.ProEt Y)ᵒᵖ)
      (x : (S'.X i).val.obj U) (y : (P.X j).val.obj U),
      evaluate.{t, u} Y R P I i j U (((e f).f i).val.app U x) y =
        (f.f (j + i)).val.app U
          (coefficientTensorGenerator.{u, t + 1, t} J R S' P i j (j + i)
            (add_comm i j) U x y) at hpure
  let e := hpure.choose
  have he := hpure.choose_spec
  let ψ : (coefficientTotalTensor.{u, t + 1, t} J R).obj (S', P) ⟶ I := e.symm q
  have hψ : IsCoefficientTensorCurry.{u, t + 1, t} J R S' P I ψ q := by
    intro a b U x y
    have hc := (he ψ a b U x y).symm
    change _ = evaluate.{t, u} Y R P I a b U (((e (e.symm q)).f a).val.app U x) y at hc
    rw [Equiv.apply_symm_apply] at hc
    have hc' (k : ℤ) (h : b + a = k) :
        (ψ.f k).val.app U
          (coefficientTensorGenerator.{u, t + 1, t} J R S' P a b k
            ((add_comm a b).trans h) U x y) =
        coefficientHomSectionApply.{u, t + 1, t} J R (P.X b) (I.X k) U
          ((coefficientHomComponent.{u, t + 1, t} J R P I a b k h).val.app U
            ((q.f a).val.app U x)) y := by
      subst k
      rw [evaluate_eq_coefficient] at hc
      exact hc
    exact hc' (a + b) (add_comm b a)
  have hn := coefficientTensorCurry_normalize.{u, t + 1, t, (max u (t + 1)) + 1}
    J R S T S' P I hS hP ψ q hψ
  have hinput : DerivedCategory.Q.map
        (q ≫ ((homComplexFunctor (R := R)).obj (op P)).map
          ((coefficientHomAugmentation.{u, t + 1, t} J R).app I)) ≫
        (coefficientHomResolutionIso.{u, t + 1, t, (max u (t + 1)) + 1} J R P I).inv =
      DerivedCategory.Q.map q ≫ homModelMap.{t, u} Y R P I := by
    simp only [Functor.map_comp, Category.assoc, homModelMap, coefficientHomAugmentation]
    rfl
  rw [hinput] at hn
  refine ⟨s.hom ≫ ψ, ?_, ?_⟩
  · intro i j U x y
    change (ψ.f (i + j)).val.app U
      ((s.hom.f (i + j)).val.app U _) = _
    have hs' := hs i j (i + j) rfl (add_comm j i) U x y
    rw [show totalPair.{t, u} Y R P S' i j U x y =
      coefficientTensorGenerator.{u, t + 1, t} J R P S' i j (i + j) rfl U x y by
      simp only [totalPair, pair, ordinaryTensor, coefficientTensorGenerator,
        CochainComplex.ιMapBifunctor, PresheafOfModules.comp_app, ModuleCat.comp_apply]
      rfl]
    rw [hs']
    simp only [Units.smul_def, map_zsmul]
    congr 1
    have hc := (he ψ j i U y x).symm
    change _ = evaluate.{t, u} Y R P I j i U (((e (e.symm q)).f j).val.app U y) x at hc
    rw [Equiv.apply_symm_apply] at hc
    exact hc
  · change (T.iso J R S P S' hP hS).inv ≫ DerivedCategory.Q.map (s.hom ≫ ψ) = _
    have hswap : (T.iso J R S P S' hP hS).inv ≫ DerivedCategory.Q.map s.hom =
        σ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj S') ≫
          (T.iso J R S S' P hS hP).inv := by
      apply (cancel_epi (T.iso J R S P S' hP hS).hom).1
      apply (cancel_mono (T.iso J R S S' P hS hP).hom).1
      simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
        Category.comp_id] using hsq.symm
    exact (map_comp_exchange DerivedCategory.Q _ _ _ _ s.hom ψ hswap hn.symm).trans
      ((swappedAdjunction_uncurry S σ (DerivedCategory.Q.obj P)
        (DerivedCategory.Q.obj S') (DerivedCategory.Q.obj I)
        (DerivedCategory.Q.map q ≫ homModelMap.{t, u} Y R P I)).symm.trans
          (curry_counit S.tensor (DerivedCategory.Q.obj P)
            (swappedAdjunction S σ (DerivedCategory.Q.obj P)) _ _ _))
end WeilConjectures.IntegralHom
