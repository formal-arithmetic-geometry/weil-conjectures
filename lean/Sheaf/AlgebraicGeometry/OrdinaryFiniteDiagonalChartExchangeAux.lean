/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents
public import Sheaf.AlgebraicGeometry.EtaleChartExchangePasting

/-! # Identifying the recorded diagonal chart transport

Source: blueprint thm-amb-p1-adjunction.proof.md, selected projection chart. -/

@[expose] public noncomputable section
set_option Elab.async false
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor upperStar
  AlgebraicGeometry.ProjectiveSpace derivedUpperStarLowerStarAdjunction
  rightDerivedLowerStarComp rightDerivedLowerStarCongr

/-- Expand the recorded diagonal chart map and its chart transport. The resulting four factors are
direct image of the adjunction unit, the direct-image composition comparison, the equality
comparison and direct image of the shifted coefficient comparison. Expand the generic chart
coefficient map to the same four factors. The recorded ordinary adjunction is the canonical
derived adjunction by its defining equation, and the recorded ordinary pullback and pushforward
are the canonical derived functors. Replacing these aliases identifies each factor; composition
congruence gives the equality. No projective-line trace or triangle identity is used.

Source: blueprint thm-amb-p1-adjunction.proof.md.
(blueprint: lem-z8-ordinary-finite-diagonal-chart-exchange-aux). -/
theorem ordinaryFiniteDiagonalChartMap_eq_generic (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    ordinaryFiniteP1DiagonalChartMap A N hA t S hS a =
    derivedChartCoefficientMap (ModuleCat.{u + 1} A)
      (projectiveLineDiagonalChart S a).val.hom (projectiveLineDiagonalProjection S a)
      (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)
      (projectiveLineDiagonalChart S a).property
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)
      ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧)
      (ordinaryFiniteShiftedLinePullback A N hA t
        (projectiveLineDiagonalChart S a).val.hom
        ((map_natCast
          ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom N) ▸
          hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom)).hom  := by sorry

end AlgebraicGeometry.Etale
