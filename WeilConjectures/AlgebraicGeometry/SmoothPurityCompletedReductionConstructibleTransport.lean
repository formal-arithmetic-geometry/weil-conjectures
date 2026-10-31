/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SmoothPurityCompletedTowerRoos
import all WeilConjectures.AlgebraicGeometry.IntegralCriterionReductionsSupplement
import WeilConjectures.AlgebraicGeometry.IntegralModelsStacksBlueprint
import WeilConjectures.AlgebraicGeometry.SfIntegralConstructibleTriangulated

/-! # Constructibility transport for completed reduction

Source: latest blueprint, integral criterion and the Restriction paragraph of the
normalized tower equivalence (blueprint: lem-sp-completed-reduction-constant-model).
-/
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
/-- Transport through the point-ring equality and the normalized section equivalence.
The inverse section equivalence followed by the section functor cancels by its counit;
restriction along the coefficient isomorphism cancels by its inverse. The existing
integral criterion then supplies bounded constructibility. -/
private theorem internalConstructible [IsNoetherian T]
    (A : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hA : Mon.mk (DerivedNakayama.integerRing l E) = A) [IsCommMonObj A.X]
    (c : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
      (Scheme.ProEt.topology T) (condensedRingObj A.X T) ≅
        WeilConjectures.completedIntegralCommRingSheafUnrestricted l E T)
    (hc : (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1} ⋙
        forget₂ RingCat.{u + 1} Ab.{u + 1})).map c.hom =
      eqToHom (congrArg (fun B ↦ (coefficientRing T B).X)
        (hA.symm.trans (integralPointMon_eq l E))) ≫
        (integralLimitAbComparison l E T).hom)
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    (hM : WeilConjectures.sfIntegralConstructible l E T M) :
    let := Functor.additive_of_preserves_binary_products
      (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (condensedRingObj A.X T)).inverse
    constantModelBoundedConstructible A.X T
      ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (Scheme.ProEt.topology T) (condensedRingObj A.X T)).inverse.mapDerivedCategory.obj
          ((restrictScalars.{u + 1} ((sheafCompose _
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c.hom)).mapDerivedCategory.obj
              M)) := by
  cases hA
  have he : c = integralSectionRingIso l E T := by
    apply (integralSectionRingIso_existsUnique l E T).unique
    · simpa only [eqToHom_refl, Category.comp_id] using hc
    · exact (integralSectionRingIso_existsUnique l E T).exists.choose_spec
  subst c
  let B := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) (AdicCompletion.ring l E T)
  let : B.functor.Additive := Functor.additive_of_preserves_binary_products _
  let : B.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let c := (sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (integralSectionRingIso l E T)
  let F := restrictScalars.{u + 1} c.hom
  let G := restrictScalars.{u + 1} c.inv
  let : B.functor.IsEquivalence := B.isEquivalence_functor
  let : B.inverse.IsEquivalence := B.isEquivalence_inverse
  let : F.IsEquivalence := restriction_isEquivalence c
  let : G.IsEquivalence := restriction_isEquivalence c.symm
  let K := B.inverse.mapDerivedCategory.obj (F.mapDerivedCategory.obj M)
  change constantModelBoundedConstructible (DerivedNakayama.integerRing l E) T K
  have e : (integralSectionDerivedEquivalence l E T).functor.obj K ≅ M :=
    (Functor.mapDerivedCategoryCompIso B.functor G).app K ≪≫
      G.mapDerivedCategory.mapIso
        (B.mapDerivedCategory.counitIso.app (F.mapDerivedCategory.obj M)) ≪≫
      (Functor.mapDerivedCategoryCompIso F G).symm.app M ≪≫
      (Functor.mapDerivedCategoryNatIso (restrictionRoundTrip c)).app M ≪≫
      (Functor.mapDerivedCategoryIdIso _).app M
  have hK : continuousIntegralConstructible l E T K := by
    apply (continuousIntegralConstructible_iff_sfIntegralConstructible l E T K).mpr
    have := WeilConjectures.sfIntegralConstructible_isClosedUnderIsomorphisms l E T
    exact (WeilConjectures.sfIntegralConstructible l E T).prop_of_iso e.symm hM
  exact IntegralModelsStacks.internal_integral_criterion_reverse l E T K hK.1 (hK.2.1 0)

/-- Normalized coefficient transport takes the intrinsic integral constructibility
predicate to the constant-model predicate required by the reduction tower.
Source: latest blueprint, normalized tower equivalence, Restriction paragraph;
integral criterion, (2) implies (1)
(blueprint: lem-sp-completed-reduction-constant-model).

Proof: uniqueness of the finite-projection-normalized abelian comparison identifies
spIntegralAbComparison with integralLimitAbComparison. The absolute-value and spectral
point rings are equal. Transport along this equality, and uniqueness of the normalized
ring lift identifies R.coefficient with integralSectionRingIso. Let K be the inverse
section equivalence applied after restriction along this ring isomorphism. The counit
of the section equivalence and the inverse scalar-restriction equations identify its
forward image with M in the derived category. Isomorphism closure and the existing
comparison criterion give derived completeness and constructibility of the first
uniformizer reduction of K. The internal integral criterion gives bounded
constructibility of K, which transports back along the point-ring equality. -/
theorem spCompletedReduction_constantModel
    [IsNoetherian T]
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D)
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    (hM : WeilConjectures.sfIntegralConstructible l E T M) :
    constantModelBoundedConstructible (spIntegralCondensed l E) T
      ((spIntegralInternalization l E T).obj
        ((SheafOfModules.restrictScalars.{u + 1}
          ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            R.coefficient.hom)).mapDerivedCategory.obj M)) := by
  have hcmp : spIntegralAbComparison l E T = integralLimitAbComparison l E T := by
    apply (integralLimitAbComparison_existsUnique l E T).unique
    · let H := sfb_integral_coefficient_limit l E T
      let a := H.choose
      let c := H.choose_spec.choose
      let j := H.choose_spec.choose_spec.choose
      have h := H.choose_spec.choose_spec.choose_spec
      have he := h.2.2.2.2.2.choose_spec.1
      exact ⟨he.1, he.2.1, a, c, j, h.1, h.2.1, he.2.2⟩
    · exact (integralLimitAbComparison_existsUnique l E T).exists.choose_spec
  apply internalConstructible l E T (sfbCondensedIntegers l E)
    (integralPointMon_eq l E) R.coefficient ?_ M hM
  ext U x
  rw [← hcmp]
  change ((R.coefficient.hom.hom.app U) x) = _
  exact R.coefficient_normalized U x
end AlgebraicGeometry.ProEtale
