/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.IntegralHomReductionModels
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedTensorHomModelSupplement
import WeilConjectures.AlgebraicGeometry.IntegralHomParameterEvaluation
/-! Split-off evaluation field for the integral tensor presentation.
Source: the representative evaluation step in the blueprint proof.
(blueprint: lem-sf-integral-hom-models-exist-tensor) -/
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.IntegralHom
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
variable [EssentiallySmall.{t + 1} Y.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}]
set_option maxHeartbeats 800000 in
-- The representative square elaborates independent site and coefficient universes.
/-- There is a left tensor adjunction normalized by signed representative evaluation.

STATEMENT-DISPUTED: the old arbitrary-adjunction formulation is false and is corrected here.
The adjunction is chosen together with its normalization: the formula cannot hold
for every adjunction between these two functors.

Source: blueprint integral Hom reduction, paragraph 2; Stacks Tags 08J9 and 06YU.
Proof: descend the Koszul swap of the specified tensor model. Transport the
recorded right tensor adjunction through that swap. Uncurry q at the chain level,
and precompose with the signed swap. Its pure-section formula gives the sign.
The normalization of uncurrying and the swap comparison square identify its
localization with the counit of the transported adjunction.
(blueprint: new-sf-integral-hom-models-exist-tensor-evaluation) -/
theorem tensor_presentation_evaluation
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses (AlgebraicGeometry.Scheme.ProEt.topology Y)
        (completedIntegralCommRingSheaf l E Y D hl)))
    (T : CoefficientTensorModels (AlgebraicGeometry.Scheme.ProEt.topology Y)
      (completedIntegralCommRingSheaf l E Y D hl) S)
    : ∃ adj : ∀ K : Derived.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl),
      (Functor.curry.obj S.tensor).obj K ⊣
        (Functor.curry.obj (hom Y
          (completedIntegralCommRingSheaf l E Y D hl))).obj (op K),
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
          (adj (DerivedCategory.Q.obj P)).counit.app (DerivedCategory.Q.obj I) := by
  obtain ⟨adj, h⟩ := tensor_presentation_parameter_evaluation l E Y D hl S T
  exact ⟨adj.adj, h⟩
end WeilConjectures.IntegralHom
