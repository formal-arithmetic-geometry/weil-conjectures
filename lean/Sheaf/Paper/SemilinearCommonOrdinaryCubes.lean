/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.Paper.SemilinearExchangeCubeData

/-! # Semilinear Frobenius exchange coherence

Assembly of the ordinary, compact-support and refinement cube equations into the
fixed-pair and representative-change laws.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w a b c d e f
open CategoryTheory CategoryTheory.Limits CategoryTheory.Endofunctor AlgebraicGeometry
open CategoryTheory.SuppliedExchangeProjection
open WeilConjectures.PodConstructibleMate
namespace WeilConjectures.PodExchangeCube


/-- Ordinary Frobenius cube equations before passage to fixed pairs.
Source: lem-fix-weil-operations.proof.md, composition and exchange paragraph;
parent proof steps 3--4.
(blueprint: lem-pod-semilinear-common-ordinary-cubes).
Proof: Relabel the source k-structures by geometric Frobenius. The underlying sites,
units and counits are unchanged. Apply square naturality of fix-lem-exchanges to the
Frobenius cube for exchange, and vertical pasting for composition. Substitute the
normalized pullback compositors and their adjunction mates, retaining all coefficient
comparison maps. Rationalization preserves the equality; for the common stage choose
one finite coefficient field for the finite diagram and cancel intermediate scalar
comparisons using their tower cocycle. No inverse to the exchange is used. -/
theorem common_ordinary_cubes
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn)
    (L : Comparisons S.closure.commonStage
      (fun X : Models D ↦ sfCommonStageWeilFrobeniusPullback D C.l C.different X.obj C.Qbar))
    (hL : commonNormalized D C S.closure L) :
  (∀ (Q : ModelSquare D) [IsSeparated Q.f.hom.left] [IsSeparated Q.f'.hom.left]
      [IsSeparated Q.g.hom.left] [IsSeparated Q.g'.hom.left],
    ∀ K,
      ((iterated (L.direct Q.f) (L.pull Q.g))).hom.app K ≫ ((directExchange S.closure.commonStage
        (S.closure.commonStageExchange Q.fiber))).app ((sfCommonStageWeilFrobeniusPullback D C.l
        C.different Q.X.obj C.Qbar).obj K) =
        (sfCommonStageWeilFrobeniusPullback D C.l C.different Q.Y'.obj C.Qbar).map
        (((directExchange S.closure.commonStage (S.closure.commonStageExchange Q.fiber))).app K) ≫
        ((iterated (L.pull Q.g') (L.direct Q.f'))).hom.app K) ∧
  (∀ {X Y Z : Models D} (f : X ⟶ Y) (h : Y ⟶ Z)
      [IsSeparated f.hom.left] [IsSeparated h.hom.left],
    ∀ K,
      ((iterated (L.direct f) (L.direct h))).hom.app K ≫ ((directComposition S.closure.commonStage
        f h).hom).app ((sfCommonStageWeilFrobeniusPullback D C.l C.different X.obj C.Qbar).obj K) =
        (sfCommonStageWeilFrobeniusPullback D C.l C.different Z.obj C.Qbar).map
        (((directComposition S.closure.commonStage f h).hom).app K) ≫ ((L.direct (f ≫ h))).hom.app
        K) := by sorry

end WeilConjectures.PodExchangeCube
