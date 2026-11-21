/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorCoherenceData
public import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionRoosCompletion

/-! # Open-factor data in the fixed coefficient presentation

## References

* Bhatt–Scholze, *The pro-étale topology for schemes*, 3.4.10, 6.5.5 and 6.5.8
* [Stacks, Tag 099N]
* [Stacks, Tag 09BN]
* [Stacks, Tag 09BP]
* [Stacks, Tag 0GL1]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport
namespace WeilConjectures.OpenFactorCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Realize the completed projection and restriction on the fixed tensor models. -/
theorem openFactorProjectionRealization
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (SX : CoefficientDerivedSystemCalculus l E X)
    (SU : CoefficientDerivedSystemCalculus l E U)
    (o : IntegralOpenReduction.Operations l E j)
    (st : IntegralOpenReduction.TensorComparison l E j o)
    (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
    (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
    (m : OpenSemilinearTensor.Comparison l E j o SX SU AX AU st)
    (c : IntegralOpenReduction.Comparison l E j o SX SU st)
    (q : OpenTensorQuotient.Comparison l E j o SX SU AX AU st m c)
    (F : FiniteFieldDatum.{u}) (hl : l ≠ F.p)
    [U.Over (Spec (.of F.k))] [X.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of F.k))] [QuasiCompact (U ↘ Spec (.of F.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of F.k))] [QuasiCompact (X ↘ Spec (.of F.k))]
    [j.IsOver (Spec (.of F.k))]
    (od : Open l E j)
    (hc : OpenProjectionRoos.Completion l E j o SX SU AX AU st m c q) :
    (∀ M N : D l E X, sfIntegralConstructible l E X M →
      sfIntegralConstructible l E X N → IsIso ((q.tensorX.chi l E).app (M, N))) ∧
    (∀ M N : D l E U, sfIntegralConstructible l E U M →
      sfIntegralConstructible l E U N → IsIso ((q.tensorU.chi l E).app (M, N))) ∧
    ∃ r : integralCompletedTensor.{u, u} l E X ⋙ star l E j ≅
        ((star l E j).prod (star l E j)) ⋙ integralCompletedTensor.{u, u} l E U,
      (∀ M N : D l E X, sfIntegralConstructible l E X M →
        sfIntegralConstructible l E X N →
        (star l E j).map ((q.tensorX.chi l E).app (M, N)) ≫ r.hom.app (M, N) =
          (proEtaleCanonicalTensorComparison j ((completed l E).ring X)
            ((completed l E).ring U) ((completed l E).pull j)
            q.tensorX.ordinary q.tensorU.ordinary).hom.app (M, N) ≫
              (q.tensorU.chi l E).app ((star l E j).obj M, (star l E j).obj N)) ∧
      (∀ (K : D l E U) (P : D l E X), sfIntegralConstructible l E U K →
        sfIntegralConstructible l E X P →
        (star l E j).map (gamma l E od q.tensorU q.tensorX K P) ≫
            od.restrictionIso.hom.app ((integralCompletedTensor.{u, u} l E U).obj
              (K, (star l E j).obj P)) =
          r.hom.app ((J l E j).obj K, P) ≫
            (integralCompletedTensor.{u, u} l E U).map
              (Prod.mkHom (od.restrictionIso.hom.app K) (𝟙 _))) := by sorry

end WeilConjectures.OpenFactorCoherence
