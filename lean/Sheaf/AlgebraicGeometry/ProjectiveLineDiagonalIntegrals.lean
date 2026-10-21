/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData
import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalCartier
import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalChernComponents
import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalTraceCalculation

/-!
# The two integrals of the projective-line diagonal class

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-p1-diagonal-integrals.md
(blueprint: lem-amb-p1-diagonal-integrals).

The Boolean indices false and true designate the first and second projection.
The chart and trace below use canonical pullback and derived-adjunction comparisons.
The supported class is specified by the recorded, uniquely determining Kummer boundary.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Both projective-line projections integrate the supported diagonal class to one.
The Cartier witness and the uniquely normalized supported Ext class explicitly specify
the diagonal's Kummer map; `supportedExactDerivedMap` realizes that class after the
canonical exact closed-direct-image comparison.

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc/lem-amb-p1-diagonal-integrals.md
(blueprint: lem-amb-p1-diagonal-integrals).

Proof plan:
1. Projective-space base change identifies each projection with P1 over P. Properness
and finite type make P Noetherian, and N stays invertible over S.
2. On product affine charts the diagonal equations are v-u, u-v, 1-uv and uv-1.
Coefficient comparison proves they are nonzerodivisors over every base ring. They cut
out the diagonal and agree by units on overlaps, giving its invertible Cartier ideal.
3. Apply lem-asd-ordinary-supported-kummer. Finite closed direct image is exact, so
its Ext realization has source RDelta_* A_P. Derived composition and the composite
adjunction unit formula identify the two units in alpha with the identity source map.
4. On every geometric fibre of either projection, the diagonal is one rational point.
The local equations (b0 y1 - b1 y0)/yi give the O(1) transition relation, including
the point at infinity. Thus its divisor line is the specified O(1).
5. Write c for delta after the constant unit. The supported-Kummer unit equation
identifies c with the Chern class of the diagonal line. Proper geometric-fibre exchange,
its unit/counit mate formula, and Cartier-preserving Kummer pullback identify the
fibre of Rp_* delta after alpha with the adjoint Kummer class of this O(1). The mate
formula and triangle identity fix its scalar and sign.
6. Base-change compatibility of lem-asd-ordinary-finite-p1-adjunction identifies the
trace on that fibre with its projective-line trace. Its value on the Chern adjunct is
one, by pr2 b inverse b in2 = identity, as in def-amb-p1-trace.
7. Full faithfulness of the degree-zero derived embedding turns the resulting
endomorphism into a sheaf endomorphism. Its difference from identity has image with
zero geometric stalks, by their exactness. Conservative stalks kill that image, so
the endomorphism is identity. Apply this separately to both projections. No equality
test on arbitrary derived morphisms is used. -/
theorem projectiveLine_diagonal_integrals (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    ∃ hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible,
      ∃ κ : Ext
        ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (ordinaryFiniteConstant A (ProjectiveLine S)))
        (Scheme.finiteEtaleTateLine
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2,
        SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S)) hI
          (by
            simpa using hS.map
              ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
                (ProjectiveLine S ↘ S)).appTop.hom) κ ∧
        ∀ a : Bool,
          projectiveLineDiagonalAlpha A S a ≫
            (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
              (supportedExactDerivedMap
                (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S)))
                (ordinaryFiniteConstant A (ProjectiveLine S))
                (Scheme.finiteEtaleTateLine
                  (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) κ) ≫
            projectiveLineDiagonalTrace N hN A hA S hS a =
          𝟙 (ordinaryFiniteUnit A (ProjectiveLine S)) := by
  have hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible :=
    projectiveLine_diagonal_ker_isInvertible S
  let hT : IsUnit (N : Γ(pullback (ProjectiveLine S ↘ S)
      (ProjectiveLine S ↘ S), ⊤)) := by
    simpa using hS.map
      ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
        (ProjectiveLine S ↘ S)).appTop.hom
  obtain ⟨κ, c, c₁, t, hc, hκ, hκc, hκc₁, hκt⟩ :=
    ordinary_supported_kummer (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N hN A hA hT
      (pullback.diagonal (ProjectiveLine S ↘ S)) hI
  refine ⟨hI, κ, ?_, ?_⟩
  · simpa [hT] using hκ
  · intro a
    apply projectiveLine_diagonal_trace_calculation N hN A hA S hS a
      (supportedExactDerivedMap
        (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S)))
        (ordinaryFiniteConstant A (ProjectiveLine S))
        (Scheme.finiteEtaleTateLine
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) κ)
    exact projectiveLine_diagonal_chern_components N hN A hA S hS hI κ hT hκ a

end AlgebraicGeometry.Etale
