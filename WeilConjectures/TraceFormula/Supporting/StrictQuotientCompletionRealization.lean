/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Isomorphism.IsomorphismStrictQuotientModels
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels
import WeilConjectures.TraceFormula.Coherent.CoherentQuotientModelComparison
import WeilConjectures.TraceFormula.Ordinary.OrdinaryQuotientTowerComparison

/-! # Normalized strict quotient completion realization

The simultaneous reduction calculus has a normalized strict quotient Roos realization on good
representatives, compatible with every coherent presentation.

## Implementation details

The simultaneous reduction presentation of a flat-term K-flat complex is used, rather than
separately chosen finite evaluations: its finite presentations induce an isomorphism of strict
towers `a`, and applying the normalized Roos bridge and then `H(a)` gives the natural
isomorphism `rho`. Another coherent presentation is compared through its specified maps `e`,
and functoriality of the bridge gives the same formula. No derived completeness or
boundedness is used.

## References

* Stacks Project, Tags 03CZ, 03EK, 06YY, 08TC, 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CategoryTheory.Limits.limit

universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

attribute [local instance 3000] integralTowerHasDerivedCategory
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  integralOperationsGoodComplex coefficientSequenceLimit TrfCompletionRoosNormalized
  integralDerivedPullback integralDerivedPullbackComparison integralPullbackDescent
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategory DerivedCategory.Q
  integralOperationsRoosMap

attribute [local semireducible] integralOperationsGoodComplex coefficientSequenceLimit

/-- The simultaneous reduction calculus has its normalized strict quotient Roos
realization on every good representative, tested on coherent presentations. -/
theorem strictQuotientCompletionRealization
    (W : Scheme.{t}) (S : CoefficientDerivedSystemCalculus l E W)
    (r : IntegralComparisonRoosModel l E W) :
    ∃ (rho : integralOperationsGoodLocalization l E W ⋙
          (S.reduction ⋙ coefficientSequenceLimit l E W) ≅
        (integralOperationsGoodComplex l E W).ι ⋙ trfQuotientTowerFunctor l E W ⋙
          integralOperationsRoosFunctor ⋙ DerivedCategory.Q),
      TrfCompletionRoosNormalized l E W S r rho := by
  obtain ⟨M, ⟨D⟩⟩ := CompletionUnit.fixedCalculusModels l E W S
  obtain ⟨θ, hθ⟩ := ordinaryQuotientTowerComparison l E W M
  let A := (integralOperationsGoodComplex l E W).ι
  let R := M.quotient l E W
  let U := coefficientSequenceRestriction l E W
  let T := U.mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex
  let H : (ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E W) ℤ) ⥤
      DerivedCategory (scalarReductionSource l E W) :=
    integralOperationsRoosFunctor ⋙ DerivedCategory.Q
  let L := coefficientSequenceLimit l E W
  let η : DerivedCategory.Q ⋙ L ≅ T ⋙ H :=
    Functor.isoWhiskerRight U.mapDerivedCategoryFactors
        (coefficientConstantTowerLimit l E W) ≪≫
      Functor.isoWhiskerLeft (U.mapHomologicalComplex (.up ℤ)) r.comparison
  let d : integralOperationsGoodLocalization l E W ⋙ S.reduction ≅
      A ⋙ R ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun P ↦ by
      exact @asIso _ _ _ _ (D.reductionComparison.app P.obj)
        (D.reduction_isIso P.obj P.property.1 P.property.2)) (by
        intro P Q a
        exact D.reductionComparison.naturality a.hom)
  let rho : integralOperationsGoodLocalization l E W ⋙ (S.reduction ⋙ L) ≅
      A ⋙ trfQuotientTowerFunctor l E W ⋙ H :=
    Functor.isoWhiskerRight d L ≪≫ Functor.isoWhiskerLeft (A ⋙ R) η ≪≫
      Functor.isoWhiskerLeft A (Functor.isoWhiskerRight θ H)
  refine ⟨rho, ?_⟩
  unfold TrfCompletionRoosNormalized
  intro P C e κ _hp hc
  obtain ⟨a, ha, hκ⟩ := coherentQuotientModelComparison l E W S M D P.obj C e κ hc
  let b := T.mapIso a.symm ≪≫ θ.app P.obj
  refine ⟨b, hθ P.obj C a κ hκ, ?_⟩
  have hn := η.hom.naturality a.hom
  change L.map (DerivedCategory.Q.map a.hom) ≫ η.hom.app C =
    η.hom.app (R.obj P.obj) ≫ H.map (T.map a.hom) at hn
  have hb : T.map a.hom ≫ b.hom = θ.hom.app P.obj := by
    change T.map a.hom ≫ (T.map a.inv ≫ θ.hom.app P.obj) = _
    rw [← Category.assoc, ← T.map_comp, a.hom_inv_id, T.map_id, Category.id_comp]
  have hcancel : H.map (T.map a.hom) ≫ H.map b.hom = H.map (θ.hom.app P.obj) := by
    rw [← H.map_comp, hb]
  change L.map (D.reductionComparison.app P.obj) ≫ η.hom.app (R.obj P.obj) ≫
      H.map (θ.hom.app P.obj) =
    L.map e.hom ≫ η.hom.app C ≫ H.map b.hom
  rw [← ha, L.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (L.map (DerivedCategory.Q.map a.hom)), hn]
  simp only [Category.assoc]
  rw [hcancel]

end WeilConjectures
