/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtension
public import WeilConjectures.SmoothPurity.Derived.DerivedCompleteIntegralDetailed
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionFiniteAssociation
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionStrictRepresentatives
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionRepresentativeRoos
import WeilConjectures.SmoothPurity.Coefficient.CoefficientSequenceRoosModel
import WeilConjectures.SmoothPurity.Normalized.NormalizedDVREffectivity

/-! # Effectivity of the scalar quotient tower

## References

* Bhatt--Scholze, *The pro-étale topology for schemes*, Proposition 3.5.1 and
  Lemmas 3.5.4--3.5.5.
-/

@[expose] public section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.SemilinearSections.hasDerived WeilConjectures.SemilinearSections.moduleAbelian

universe d u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : AlgebraicGeometry.Scheme.{u})

/-- Effectivity of the specified strict scalar quotient tower on good representatives. -/
theorem integralScalarTower_effectivity
    (P : (integralOperationsGoodComplex l E Y).FullSubcategory) :
    IsDerivedComplete l L Y D hl
      ((integralScalarExtension l E L ι Y).obj (DerivedCategory.Q.obj P.obj)) ∧
    ∀ n : ℕ, Nonempty
      (((integralDerivedReduction l L Y D hl n).obj
          ((integralScalarExtension l E L ι Y).obj (DerivedCategory.Q.obj P.obj))) ≅
        DerivedCategory.Q.obj ((integralScalarFiniteComplex l E L ι Y n).obj P.obj)) := by
  classical
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0} _
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{u + 1} := integralCoefficientAbSheafify.{u, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} := integralCoefficientAbLocallyBijective.{u, u} Y
  obtain ⟨SE, _⟩ := coefficientDerivedSystemEvaluationCalculus l E Y
  let : EssentiallySmall.{u + 1} (ℕ × Y.ProEt) := essentiallySmallSelf.{0} _
  let S : SemilinearSections.SemilinearDerivedSectionsData.{u + 1, u, u}
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y)
      (coefficientSequenceCommRingTransition l E Y) :=
    (SemilinearSections.semilinearDerivedSections.{u + 1, u, u}
      (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (integralCoefficientCommRingSheaf l E Y)
      (coefficientSequenceCommRingTransition l E Y)).some
  let A : CoefficientExtensionSystems l E L ι Y :=
    S.coefficientExtension (integralCoefficientCommRingSheaf l L Y)
      (coefficientSequenceCommRingTransition l L Y)
      (integralScalarQuotientSheafMap l E L ι Y)
      (coefficientExtensionQuotient_naturality l E L ι Y)
  obtain ⟨s⟩ := coefficientExtensionFiniteAssociation_exists l E L ι Y A
  obtain ⟨direct, evaluation, model, ht, _, hn⟩ :=
    coefficientExtensionStrictRepresentative_exists l E L ι Y A SE
      s.association s.association_section
  obtain ⟨e, _⟩ := coefficientExtensionRepresentativeRoos_exists l E L ι Y A SE
    direct evaluation ht model
  let N := (coefficientExtensionSystem l E L ι Y SE A).obj (DerivedCategory.Q.obj P.obj)
  let M := (integralScalarExtension l E L ι Y).obj (DerivedCategory.Q.obj P.obj)
  let a : M ≅ (coefficientSequenceLimit l L Y).obj N :=
    (integralScalarExtensionComparison l E L ι Y).app P ≪≫ (e.app P).symm
  obtain ⟨T, b, hp, δ, hδ⟩ := coefficientSequence_roosModel l L Y D hl N (hn _)
  let := hp
  let p₀ := Pi.lift (fun n : ℕ ↦ (coefficientSequenceProjection l L Y n).app N ≫
    (normalizedDVRResCompleted l L Y D hl n).map (b n).inv ≫
      (T.evaluationIso n).inv)
  let p := a.hom ≫ p₀
  let δ' := δ ≫ (shiftFunctor _ (1 : ℤ)).map a.inv
  have hc : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l L Y D hl n.le_succ).app T.tower)
      M p δ' := by
    exact (Pretriangulated.distinguished_iff_of_iso
      (Pretriangulated.Triangle.isoMk
        (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism
          (fun n : ℕ ↦ (normalizedDVRTowerTransition l L Y D hl n.le_succ).app T.tower)) δ')
        (Pretriangulated.Triangle.mk p₀ (towerTransitionEndomorphism
          (fun n : ℕ ↦ (normalizedDVRTowerTransition l L Y D hl n.le_succ).app T.tower)) δ)
        a (Iso.refl _) (Iso.refl _) (by simp [p]) (by simp)
        (by simp [δ']))).mpr hδ
  obtain ⟨hi, _, hcomplete⟩ := normalizedDVRTower_effectivity l L Y D hl T M p δ' hc
  refine ⟨hcomplete, fun n ↦ ?_⟩
  have := hi n
  exact ⟨asIso (normalizedDVRCounitComparison l L Y D hl T M p n) ≪≫ b n ≪≫
    (coefficientSequenceDerivedEvaluation.{u, u} l L Y n).mapIso (model.app P) ≪≫
    (coefficientSequenceEvaluation.{u, u} l L Y n).mapDerivedCategoryFactors.app (direct.obj P) ≪≫
    DerivedCategory.Q.mapIso ((evaluation n).app P)⟩

end WeilConjectures
