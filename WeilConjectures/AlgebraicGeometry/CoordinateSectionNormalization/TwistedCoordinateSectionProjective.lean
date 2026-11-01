/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionOrdinary
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-!
# Projective coordinate-section Kummer normalization

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
cor-pur-affine-space-zero-section-purity.proof.md, rank-one Cartier normalization
(blueprint: def-pur-coordinate-section-projective-arrows).

The supported arrow is the derived realization of the unique relative Kummer boundary.
The normalization uses the actual supported constant unit and the positive Chern class
specified by the projective-line trace.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProEtale.CoordinateSectionNormalization

/-- The zero section followed by the standard chart `x ↦ [x : 1]`.
Source: blueprint cor-pur-affine-space-zero-section-purity.proof.md, rank-one paragraph
(blueprint: def-pur-coordinate-section-projective-arrows). -/
def projectiveZero (T : Scheme.{u}) : T ⟶ ProjectiveLine T :=
  sectionMap T ≫ ProjectiveLine.affineChart T

/-- The derived realization of the unique supported ordinary Kummer boundary of the
projective zero divisor. Uniqueness fixes the chosen Ext class; no orientation is chosen.
Source: blueprint cor-pur-affine-space-zero-section-purity.proof.md, Cartier map paragraph;
Stacks 03PL and 0A45 (blueprint: def-pur-coordinate-section-projective-arrows). -/
def projectiveSupported (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsClosedImmersion (projectiveZero T)]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(ProjectiveLine T, ⊤)))
    (hI : (projectiveZero T).ker.IsInvertible) :
    (Etale.ordinaryFinitePushforward A (projectiveZero T)).obj
      (Etale.ordinaryFiniteUnit A T) ⟶
        (Etale.ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧ :=
  Etale.supportedExactDerivedMap
    (Etale.lowerStar (ModuleCat.{u + 1} A) (projectiveZero T))
    (Etale.ordinaryFiniteConstant A T)
    (Scheme.finiteEtaleTateLine (ProjectiveLine T) N A hA)
    (Etale.ordinary_supported_kummer_uniqueBoundary (ProjectiveLine T) N hN A hA hT
      (projectiveZero T) hI).exists.choose

/-- The projective zero divisor has invertible ideal, its dual ideal is the specified
`O(1)`, and forgetting support gives the positive Kummer Chern class used by the trace,
at every positive invertible exponent annihilating the coefficient ring.
Source: blueprint cor-pur-affine-space-zero-section-purity.proof.md, the equality
`c₁(O(s(T))) = c₁(O(1)) = h` (blueprint: def-pur-coordinate-section-projective-arrows). -/
def ProjectiveNormalization (P : WeilConjectures.PurityFiniteSetting.{u}) (T : Scheme.{u})
    [IsNoetherian T] [IsClosedImmersion (projectiveZero T)] : Prop :=
  ∃ hI : (projectiveZero T).ker.IsInvertible,
    Nonempty ((projectiveZero T).ker.toModulesᵛ ≅
      ProjectiveSpace.twist (ULift.{u} (Fin 2)) T 1) ∧
    ∀ (N : ℕ) (hN : 0 < N) (hA : (N : P.Coefficient) = 0)
      (hT : IsUnit (N : Γ(T, ⊤))),
      Etale.supportedDerivedUnit P.Coefficient (projectiveZero T) ≫
        projectiveSupported P.Coefficient T N hN hA
          (Etale.projectiveLineTraceDatum N hN P.Coefficient hA T hT).invertible_on_projectiveLine
          hI = (Etale.projectiveLineTraceDatum N hN P.Coefficient hA T hT).chern

end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
