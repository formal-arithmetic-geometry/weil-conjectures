/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.IntegralHomTensorAdjointNaturality
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization
import WeilConjectures.SixFunctors.IntegralHom.Evaluation.IntegralHomEvaluationCoefficient
import WeilConjectures.SixFunctors.IntegralHom.HomComplexTensorPureEquivalence
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement

/-! # Representative formula for the tensor adjoint comparison

Source: Stacks Tags 06YU, 08J9 and 0FPQ; paragraph 5 of the integral finite-extension proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules
namespace WeilConjectures.IntegralFiniteExtension

/-- The actual Koszul exchange of the signed total tensor complexes.
Source: Stacks 0FPQ (blueprint: new-sf-integral-hom-adjoint-representatives). -/
def tensorComplexSwap (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ) :
    ((IntegralHom.totalTensor.{u, u} X R).obj P).obj Q ≅
      ((IntegralHom.totalTensor.{u, u} X R).obj Q).obj P :=
  letI := SheafOfModules.cochainModulesMonoidal R
  letI := SheafOfModules.cochainModulesSymmetric R
  β_ P Q

/-- The signed interchange on the actual sheafified tensor generators.
Source: Stacks 0FPQ (blueprint: new-sf-integral-hom-adjoint-representatives). -/
theorem tensorComplexSwap_pure (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (p q n : ℤ) (h : p + q = n) (h' : q + p = n)
    (U : X.ProEtᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((tensorComplexSwap X R P Q).hom.f n).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) R
          P Q p q n h U x y) =
      (p * q).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
        (ProEt.topology X) R Q P q p n h' U y x := by
  convert (RingedDerivedNative.complexConstraints.{u + 1, u, u}
    (ProEt.topology X) R).symmetry P Q p q n h h' U x y using 0
  with_unfolding_all rfl

attribute [local irreducible] HasDerivedCategory.standard scalarIntegralClosed
  scalarIntegralModels completedIntegralCommRingSheafUnrestricted
  completedIntegralCoefficientSheafUnrestricted IntegralHom.homModelMap
  IntegralHom.totalPair IntegralHom.evaluate coefficientHomResolutionIso
  tensorComplexSwap

private theorem total_ext (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P Q I : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (f g : ((IntegralHom.totalTensor.{u, u} X R).obj P).obj Q ⟶ I)
    (h : ∀ (i j : ℤ) (U : X.ProEtᵒᵖ) (x : (P.X i).val.obj U)
      (y : (Q.X j).val.obj U),
      (f.f (i + j)).val.app U (IntegralHom.totalPair.{u, u} X R P Q i j U x y) =
        (g.f (i + j)).val.app U (IntegralHom.totalPair.{u, u} X R P Q i j U x y)) : f = g := by
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  change i + j = k at hij
  subst k
  apply SheafOfModules.ScalarHomOrdinary.pure_hom_ext.{u + 1, u, u + 1}
    R (P.X i) (Q.X j) (I.X (i + j))
  intro U x y
  have hh := h i j U x y
  simp only [IntegralHom.totalPair, IntegralHom.pair, IntegralHom.ordinaryTensor,
    CochainComplex.ιMapBifunctor] at hh
  convert hh using 0
  with_unfolding_all rfl

/-- The adjoint comparison carries each supplied tensor representative to the
reversed closed tensor representative, preceded by the Koszul exchange.

Source: Stacks Tags 06YU, 08J9 and 0FPQ; paragraph 5 of
lem-coef-integral-finite-extension.proof.md.

Proof: augment the reversed total tensor to its functorial K-injective resolution,
and curry this chain map. The supplied evaluation field and the ordinary closed
uncurrying formula represent the same curried map. The supplied evaluation equals
the augmentation after Koszul exchange, since the exchange contributes precisely
the sign in its evaluation field; total summands and sheafified pure tensors detect
equality. Uniqueness of left adjoints identifies the two inverse transposes.
Cancel the localized augmentation, which is an isomorphism, and the representative
isomorphisms. This proves the formula also for zero complexes and empty schemes.
(blueprint: new-sf-integral-hom-adjoint-representatives). -/
theorem tensorAdjointComparison_representative
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u})
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (P Q : CochainComplex (integralTowerModules l E X) ℤ)
    (hp : IntegralHom.flat.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X) P)
    (hq : IntegralHom.flat.{u, u} X (completedIntegralCommRingSheafUnrestricted l E X) Q) :
    a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
        (tensorAdjointComparison l E X a).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map
        (tensorComplexSwap X (completedIntegralCommRingSheafUnrestricted l E X) P Q).hom ≫
        ((scalarIntegralModels l E X).iso _ _ _ Q P hq hp).hom := by
  let J := ProEt.topology X
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let S := scalarIntegralClosed l E X
  let T := scalarIntegralModels l E X
  let A := IntegralHom.Modules.{u, u} X R
  let := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1, u, u}
    J R).1
  let V := ((IntegralHom.totalTensor.{u, u} X R).obj Q).obj P
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u + 1} A).obj V
  let η : V ⟶ I := (CochainComplex.toKInjectiveResolution.{u + 1} A).app V
  have hI : I.IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u + 1} A V
  have hη : QuasiIso η :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u + 1} A V).2
  have : IsIso (DerivedCategory.Q.map η) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hη
  obtain ⟨c, hc⟩ := IntegralHom.homComplexTensor_pure_equivalence.{u, u} X R Q P I
  let q := c η
  obtain ⟨β, hβ, hβsquare⟩ := a.evaluation P I Q hp hq hI q
  have hβeq : β = (tensorComplexSwap X R P Q).hom ≫ η := by
    apply total_ext X R P Q I
    intro i j U x y
    rw [hβ]
    have hpair : IntegralHom.totalPair.{u, u} X R P Q i j U x y =
        coefficientTensorGenerator.{u, u + 1, u} J R P Q i j (i + j) rfl U x y := by
      simp only [IntegralHom.totalPair, IntegralHom.pair, IntegralHom.ordinaryTensor,
        coefficientTensorGenerator, CochainComplex.ιMapBifunctor,
        PresheafOfModules.comp_app, ModuleCat.comp_apply]
      rfl
    change _ = (η.f (i + j)).val.app U
      (((tensorComplexSwap X R P Q).hom.f (i + j)).val.app U _)
    rw [hpair]
    have hs' := tensorComplexSwap_pure X R P Q i j (i + j) rfl
      (add_comm j i) U x y
    rw [hs']
    simp only [Units.smul_def, map_zsmul]
    exact congrArg (fun z ↦ ((i * j).negOnePow : ℤ) • z) (hc η j i U y x)
  have hcurry : IsCoefficientTensorCurry.{u, u + 1, u} J R Q P I η q := by
    intro i j U x y
    have h := hc η i j U x y
    have h' (k : ℤ) (hk : j + i = k) :
        (η.f k).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} J R Q P i j k
            ((add_comm i j).trans hk) U x y) =
        coefficientHomSectionApply.{u, u + 1, u} J R (P.X j) (I.X k) U
          ((coefficientHomComponent.{u, u + 1, u} J R P I i j k hk).val.app U
            ((q.f i).val.app U x)) y := by
      subst k
      rw [IntegralHom.evaluate_eq_coefficient] at h
      exact h.symm
    exact h' (i + j) (add_comm j i)
  have hn := coefficientTensorCurry_normalize.{u, u + 1, u, u + 2}
    J R S T Q P I hq hp η q hcurry
  have hinput : DerivedCategory.Q.map
        (q ≫ ((homComplexFunctor (R := R)).obj (op P)).map
          ((coefficientHomAugmentation.{u, u + 1, u} J R).app I)) ≫
        (coefficientHomResolutionIso.{u, u + 1, u, u + 2} J R P I).inv =
      DerivedCategory.Q.map q ≫ IntegralHom.homModelMap.{u, u} X R P I := by
    simp only [Functor.map_comp, Category.assoc, IntegralHom.homModelMap,
      coefficientHomAugmentation]
    rfl
  rw [hinput] at hn
  have hcmp :
      ((a.adjunction (DerivedCategory.Q.obj P)).homEquiv (DerivedCategory.Q.obj Q)
        (DerivedCategory.Q.obj I)).symm
          (DerivedCategory.Q.map q ≫ IntegralHom.homModelMap.{u, u} X R P I) =
      (tensorAdjointComparison l E X a).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (S.transpose _ _ _).symm
          (DerivedCategory.Q.map q ≫ IntegralHom.homModelMap.{u, u} X R P I) := by
    apply ((a.adjunction (DerivedCategory.Q.obj P)).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right]
    rw [show (a.adjunction (DerivedCategory.Q.obj P)).homEquiv _ _
      ((tensorAdjointComparison l E X a).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) =
      (S.adjunction (DerivedCategory.Q.obj P)).unit.app (DerivedCategory.Q.obj Q) from
        Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _]
    change _ = (S.adjunction (DerivedCategory.Q.obj P)).homEquiv _ _
      (((S.adjunction (DerivedCategory.Q.obj P)).homEquiv _ _).symm
        (DerivedCategory.Q.map q ≫ IntegralHom.homModelMap.{u, u} X R P I))
    exact (Equiv.apply_symm_apply _ _).symm
  rw [hβeq, Functor.map_comp] at hβsquare
  rw [Adjunction.homEquiv_counit] at hcmp
  change a.tensor.map (Prod.mkHom (𝟙 (DerivedCategory.Q.obj P))
      (DerivedCategory.Q.map q ≫ IntegralHom.homModelMap.{u, u} X R P I)) ≫
      (a.parameterAdjunction.adj (DerivedCategory.Q.obj P)).counit.app (DerivedCategory.Q.obj I) =
    (tensorAdjointComparison l E X a).hom.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫ _ at hcmp
  rw [hcmp] at hβsquare
  have hnorm : (S.transpose (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q).2
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q).1
        (DerivedCategory.Q.obj I)).symm
        (DerivedCategory.Q.map q ≫ IntegralHom.homModelMap.{u, u} X R P I) =
      (T.iso J R S Q P hq hp).inv ≫ DerivedCategory.Q.map η := by
    with_unfolding_all exact hn
  rw [hnorm] at hβsquare
  have heq := (cancel_mono (DerivedCategory.Q.map η)).1
    (show (a.representative.inv.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
      DerivedCategory.Q.map (tensorComplexSwap X R P Q).hom) ≫ DerivedCategory.Q.map η =
      ((tensorAdjointComparison l E X a).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (T.iso J R S Q P hq hp).inv) ≫ DerivedCategory.Q.map η by
      with_unfolding_all simpa only [Category.assoc] using hβsquare)
  apply (cancel_mono (T.iso J R S Q P hq hp).inv).1
  change (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) ≫
      (tensorAdjointComparison l E X a).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (T.iso J R S Q P hq hp).inv =
    (DerivedCategory.Q.map (tensorComplexSwap X R P Q).hom ≫
      (T.iso J R S Q P hq hp).hom) ≫ (T.iso J R S Q P hq hp).inv
  rw [Category.assoc, ← heq]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact Iso.hom_inv_id_app_assoc a.representative _ _

end WeilConjectures.IntegralFiniteExtension
