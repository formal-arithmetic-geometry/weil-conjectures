/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.Paper.IntegralMatrixAnalyticData
public import Mathlib.LinearAlgebra.Matrix.Rank
import Sheaf.Paper.GeometricFieldProEtaleEvaluation

/-! # The geometric input to analytic integral matrix charts -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The evaluated integral matrix has constant field rank on a free rational-cokernel
cover member.

Source: Bhatt--Scholze, Section 6.8, continuous integral coefficient framework,
and Example 4.1.10, exact geometric-field evaluation.
(blueprint: lem-weil-pbc-integral-matrix-pointwise-rank)

Proof: choose the supplied rational-cokernel cover and choose its finite free basis
on each member, of rank q. Pull the cokernel presentation and this basis to an
algebraic closure of the residue field at any point. Scheme inverse image preserves
cokernels, as does final-object evaluation over the algebraically closed field.
The coefficient pullback comparison and the canonical continuous realization identify
the evaluated presentation with the pointwise E-matrix displayed here. Evaluation
sends the free target and cokernel to E-vector spaces of dimensions t and q.
Rank-nullity therefore gives matrix rank t-q, independent of the point.
The integral matrix and its E-valued image have the same entries under the scalar
inclusion O_E to E. A rank-zero source, rank-zero target or empty member causes no
exception; the rank formula still applies wherever there is a point. -/
theorem integralMatrix_pointwise_rank (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (n t : ℕ) (X : Scheme.{u})
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t)
    (hC : ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
            (cokernel a)))) :
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k (x y : V.X k),
      Matrix.rank (fun i j ↦ (integralMatrixPullbackFunctions ℓ E (V.f k) a i j x).val) =
        Matrix.rank (fun i j ↦ (integralMatrixPullbackFunctions ℓ E (V.f k) a i j y).val) :=
  by sorry


end AlgebraicGeometry.ProEtale.CondensedRing
