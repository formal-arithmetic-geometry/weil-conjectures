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


/-- Refinement Frobenius cube equations before passage to fixed pairs.
Source: lem-fix-weil-operations.proof.md, composition and exchange paragraph;
parent proof steps 5--6.
(blueprint: lem-pod-semilinear-rational-refinement-cubes).
Proof: Base change a common refinement of the two indexed model compactifications
along Frobenius, and twist its source k-structure. The underlying proper/open sites
and maps are unchanged. Clause (4) of fix-lem-exchanges makes the canonical refinement
comparison commute with the Frobenius exchange. Transport from the two model anchors
to the displayed geometric representatives by their normalization formulas. The
comparison cocycle cancels the intervening maps. Rationalization and common-stage
passage preserve this equality, using one finite field for its finite diagram.
This compares distinct model anchors as a conclusion, without assuming their agreement. -/
theorem rational_refinement_cubes
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn)
    (L : Comparisons S.higher.rational
      (fun X : Models D ↦ sfWeilFrobeniusPullback D C.l C.different X.obj E))
    (hL : rationalNormalized D C E S.higher L) :
  (∀ {X Y : Models D} (f : X ⟶ Y) (c₀ c₀' : Compactification f.hom.left)
      (c c' : Compactification ((fiberModels D).map f).hom.left),
    ∀ K,
      ((L.support f c₀ c)).hom.app K ≫ ((S.higher.rational.comparison ((fiberModels D).map f) c
        c').hom).app
        ((sfWeilFrobeniusPullback D C.l C.different X.obj E).obj K) =
        (sfWeilFrobeniusPullback D C.l C.different Y.obj E).map (((S.higher.rational.comparison
        ((fiberModels
        D).map f) c c').hom).app K) ≫ ((L.support f c₀' c')).hom.app K) := by sorry

end WeilConjectures.PodExchangeCube
