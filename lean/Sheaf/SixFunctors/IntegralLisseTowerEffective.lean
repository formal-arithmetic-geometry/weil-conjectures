/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Sheaf.SixFunctors.IntegralLisseReductionConstruction
import Sheaf.SixFunctors.IntegralLisseTowerLocalBases
import Sheaf.SixFunctors.IntegralLisseReductionComplete
import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.LocalProperties

/-!
# IntegralLisseTowerEffective

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.4(1).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

private theorem free_isFiniteLocallyFree (I : Type (u + 1)) [Finite I] :
    (SheafOfModules.free (R := integralLisseRing l E X) I).IsFiniteLocallyFree := by
  constructor
  refine ⟨(SheafOfModules.free.generatingSections
    (R := integralLisseRing l E X) I).localGeneratorsData,
    inferInstance, ?_⟩
  constructor
  intro i
  exact ⟨inferInstanceAs (Finite I)⟩

private theorem finiteScalar_zero (n : ℕ)
    (N : ringedSiteModules.{u + 1}
      ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (integralLisseFiniteRing l E X n))) :
    integralLisseScalar l E X ((integralLisseFiniteRestriction l E X n).obj N)
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) = 0 := by
  let := spectralNorm.normedField ℚ_[l] E
  ext U x
  have hz : (integralLisseReduction l E X n).hom.app U
      (lisseIntegerConstantSized l E X U
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1))) = 0 := by
    apply ULift.ext
    apply ContinuousMap.ext
    intro y
    change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    change _ ∈ Ideal.span {Padic.coefficientExtensionUniformizer l E} ^ (n + 1)
    rw [Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  change N.val.obj U at x
  change (integralLisseReduction l E X n).hom.app U _ • x = 0
  rw [hz, zero_smul]

private theorem towerScalar_zero (F : IntegralReductionTower l E X) (n : ℕ) :
    integralLisseScalar l E X (F.obj.obj (op n))
      (Padic.coefficientExtensionUniformizer l E ^ (n + 1)) = 0 := by
  obtain ⟨N, _, ⟨e⟩⟩ := F.property.1 n
  apply (cancel_epi e.hom).1
  rw [← integralLisseScalar_natural, finiteScalar_zero, zero_comp, comp_zero]

private def localLimitIso (F : IntegralReductionTower l E X) (U : X.ProEt)
    (I : Type (u + 1)) [Finite I]
    (α : F.obj ⋙ SheafOfModules.overFunctor (integralLisseRing l E X) U ≅
      integralLisseCokernelTower l E X (SheafOfModules.free I) ⋙
        SheafOfModules.overFunctor (integralLisseRing l E X) U) :
    (limit F.obj).over U ≅ (SheafOfModules.free (R := integralLisseRing l E X) I).over U := by
  let H := SheafOfModules.overFunctor.{u + 1} (integralLisseRing l E X) U
  have := integralLisseOver_preserves_limits l E X U
  let cF := H.mapCone (limit.cone F.obj)
  let cP := H.mapCone (Cone.mk (SheafOfModules.free I)
    (integralLisseCokernelCone l E X (SheafOfModules.free I)))
  have hF : IsLimit cF := isLimitOfPreserves H (limit.isLimit F.obj)
  have hP : IsLimit cP := isLimitOfPreserves H
    (integralLisseCokernel_isLimit l E X
      ⟨SheafOfModules.free I, free_isFiniteLocallyFree l E X I⟩).some
  exact ((IsLimit.postcomposeHomEquiv α cF).symm hF).conePointUniqueUpToIso hP

private theorem localLimitIso_projection (F : IntegralReductionTower l E X) (U : X.ProEt)
    (I : Type (u + 1)) [Finite I]
    (α : F.obj ⋙ SheafOfModules.overFunctor (integralLisseRing l E X) U ≅
      integralLisseCokernelTower l E X (SheafOfModules.free I) ⋙
        SheafOfModules.overFunctor (integralLisseRing l E X) U) (n : ℕ) :
    (localLimitIso l E X F U I α).hom ≫
      (SheafOfModules.overFunctor (integralLisseRing l E X) U).map
        (cokernel.π (integralLisseScalar l E X (SheafOfModules.free I)
          (Padic.coefficientExtensionUniformizer l E ^ (n + 1)))) =
      (SheafOfModules.overFunctor (integralLisseRing l E X) U).map
        (limit.π F.obj (op n)) ≫ α.hom.app (op n) := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ (op n)

/-- The actual sheaf limit of a normalized tower is finite locally free, and its
projections are the prescribed scalar quotients.

Source: Bhatt--Scholze, Proposition 6.8.4(1), p. 59 (essential surjectivity).
(blueprint: lem-sfb-integral-lisse-tower-effective)

Proof: compatible local bases identify the restricted tower with the scalar-cokernel
tower of a finite free integral module. Completeness and preservation of limits by
slice restriction identify the restricted limit with that module; the limit comparison
commutes with every projection. This proves finite local freeness. Each level is
annihilated by its uniformizer power, so each global projection factors through the
corresponding scalar cokernel. Slice restriction preserves cokernels, and the projection
comparison identifies this factorization locally with the cokernel of an isomorphism.
The factorization is therefore invertible on a cover and hence globally. This proves
the scalar-cokernel universal property, including zero and varying ranks and empty bases. -/
theorem integralLisseTower_effective (F : IntegralReductionTower l E X) :
    (limit F.obj).IsFiniteLocallyFree ∧
      ∀ n : ℕ, IsIntegralLisseQuotient l E X
        (Padic.coefficientExtensionUniformizer l E ^ (n + 1))
        (limit.π F.obj (op n)) := by
  classical
  obtain ⟨I, U, κ, hcover, hfinite, hmodels⟩ := integralLisseTower_localBases l E X F
  let (i : I) : Finite (κ i) := hfinite i
  let α (i : I) := (hmodels i).some
  let e (i : I) := localLimitIso l E X F (U i) (κ i) (α i)
  constructor
  · apply SheafOfModules.isFiniteLocallyFree_of_exists_over_iso_free U hcover κ
    intro i
    have : HasWeakSheafify ((Scheme.ProEt.topology X).over (U i)) AddCommGrpCat.{u + 1} :=
      inferInstance
    have : ((Scheme.ProEt.topology X).over (U i)).WEqualsLocallyBijective
        AddCommGrpCat.{u + 1} := inferInstance
    have := (ringedOverFunctor_exactGeneral (integralLisseRing l E X) (U i)).1
    exact ⟨e i ≪≫ (SheafOfModules.mapFreeIso
      (SheafOfModules.overFunctor (integralLisseRing l E X) (U i)) (κ i) (Iso.refl _)).symm⟩
  · intro n
    let b := Padic.coefficientExtensionUniformizer l E ^ (n + 1)
    let a := integralLisseScalar l E X (limit F.obj) b
    let p := limit.π F.obj (op n)
    have hp : a ≫ p = 0 := by
      rw [integralLisseScalar_natural, towerScalar_zero, comp_zero]
    let d := cokernel.desc a p hp
    have hd (i : I) :
        IsIso ((SheafOfModules.overFunctor (integralLisseRing l E X) (U i)).map d) := by
      let H := SheafOfModules.overFunctor.{u + 1} (integralLisseRing l E X) (U i)
      have : HasWeakSheafify ((Scheme.ProEt.topology X).over (U i))
          AddCommGrpCat.{u + 1} := inferInstance
      have : ((Scheme.ProEt.topology X).over (U i)).WEqualsLocallyBijective
          AddCommGrpCat.{u + 1} := inferInstance
      have := (ringedOverFunctor_exactGeneral (integralLisseRing l E X) (U i)).2.2
      let P := SheafOfModules.free (R := integralLisseRing l E X) (κ i)
      let aP := integralLisseScalar l E X P b
      let eQ : H.obj (cokernel a) ≅ H.obj (cokernel aP) :=
        PreservesCokernel.iso H a ≪≫
          cokernel.mapIso _ (H.map aP) (e i) (e i) (by
            ext V x
            exact ((e i).hom.val.app V).hom.map_smul _ x) ≪≫
          (PreservesCokernel.iso H aP).symm
      have heQ : H.map (cokernel.π a) ≫ eQ.hom =
          (e i).hom ≫ H.map (cokernel.π aP) := by
        simp [eQ, Category.assoc]
      have hcomp : H.map d ≫ (α i).hom.app (op n) = eQ.hom := by
        apply (cancel_epi (H.map (cokernel.π a))).1
        rw [← Category.assoc, ← H.map_comp, cokernel.π_desc, heQ]
        exact (localLimitIso_projection l E X F (U i) (κ i) (α i) n).symm
      have heq : H.map d = eQ.hom ≫ (α i).inv.app (op n) := by
        rw [← hcomp, Category.assoc, ← NatTrans.comp_app, Iso.hom_inv_id]
        exact (Category.comp_id _).symm
      rw [heq]
      infer_instance
    have : IsIso ((SheafOfModules.toSheaf (integralLisseRing l E X)).map d) := by
      apply CategoryTheory.Sheaf.isIso_of_coversTop hcover
      intro i
      change IsIso ((SheafOfModules.toSheaf ((integralLisseRing l E X).over (U i))).map
        ((SheafOfModules.overFunctor (integralLisseRing l E X) (U i)).map d))
      infer_instance
    have : IsIso d := isIso_of_reflects_iso _ (SheafOfModules.toSheaf _)
    have hpd : cokernel.π a ≫ d = p := cokernel.π_desc a p hp
    have : Epi p := by
      rw [← hpd]
      infer_instance
    refine ⟨hp, ⟨CokernelCofork.IsColimit.ofπ' p hp ?_⟩⟩
    intro Y k hk
    refine ⟨inv d ≫ cokernel.desc a k hk, ?_⟩
    rw [← hpd, Category.assoc, IsIso.hom_inv_id_assoc, cokernel.π_desc]

end AlgebraicGeometry.ProEtale
