/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalData
public import Sheaf.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps

/-! # The two Chern components of the projective-line diagonal

Source: blueprint lem-amb-p1-diagonal-integrals, the equation of the diagonal and its
Kummer class (blueprint: lem-amb-p1-diagonal-chern-components).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The Chern adjunct of the diagonal is the sum of the relative hyperplane adjunct
and the shifted twisted unit after the base hyperplane class.
Source: blueprint lem-amb-p1-diagonal-integrals, the equation x0 y1 - x1 y0 and
proof steps 2--5 (blueprint: lem-amb-p1-diagonal-chern-components).

Proof: The four product-chart equations for the diagonal are the local expressions of
one section of pr1^* O(1) tensor pr2^* O(1). Their nonzerodivisor property identifies
its dual ideal with that tensor product. Under either canonical chart this line is
O(1) tensor r^* O(1). Apply the supported-Kummer unit/Chern equation. The Kummer
connecting homomorphism is additive on Picard classes, so its unsupported class is the
sum of the relative hyperplane Chern class and the inverse image of the base hyperplane
Chern class. The integral-generator comparison is bijective, hence gives the equality
of the derived arrows with their prescribed scalar extension. Take adjuncts under r^*
left adjoint to Rr_*. Naturality of its unit gives the base class followed by the
shifted twisted unit; the other summand is precisely the hyperplane Chern adjunct.
The chart adjunction and direct-image composition identify this adjunct with the
left-hand side. All coefficient comparisons are normalized on roots and pure tensors,
so no orientation is chosen. Swapping the factors changes the diagonal equation by
-1, which does not change its divisor line or Chern class. This also covers N=1,
the zero coefficient ring, the empty base, and bases with nilpotents.
-/
theorem projectiveLine_diagonal_chern_components (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible)
    (κ : Ext
      ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2)
    (hT : IsUnit (N : Γ(pullback (ProjectiveLine S ↘ S)
      (ProjectiveLine S ↘ S), ⊤)))
    (hκ : SupportedKummerBoundary A N hA
      (pullback.diagonal (ProjectiveLine S ↘ S)) hI hT κ) (a : Bool) :
    letI : IsLocallyNoetherian (ProjectiveLine S) :=
      LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
    letI : CompactSpace (ProjectiveLine S) :=
      QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
    letI : IsNoetherian (ProjectiveLine S) := ⟨⟩
    let hP := ordinaryFiniteP1_isUnit N S hS
    projectiveLineDiagonalAlpha A S a ≫
      (ordinaryFinitePushforward A (projectiveLineDiagonalProjection S a)).map
        (supportedExactDerivedMap
          (lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S)))
          (ordinaryFiniteConstant A (ProjectiveLine S))
          (Scheme.finiteEtaleTateLine
            (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) κ) ≫
      projectiveLineDiagonalChartPushforward N hN A hA S hS a =
    ordinaryFiniteP1ChernPushforward A N hA (ProjectiveLine S)
        (projectiveLineTraceDatum N hN A hA (ProjectiveLine S) hP).chern +
      (projectiveLineTraceDatum N hN A hA S hS).chern ≫
        ordinaryFiniteP1Unit A N hA (projectiveLineTraceTransport N hN A hA)
          (ProjectiveLine S) hP := by
  sorry

end AlgebraicGeometry.Etale
