/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.TwistedCoordinateSectionOrdinary
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

/-! # The projective zero-divisor clause
Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, rank-one compactification
(blueprint: def-pur-coordinate-section-projective-arrows).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.CoordinateSectionNormalization

/-- The projective zero-section divisor, as the literal composite of the affine section
and the standard affine chart. Source: blueprint D_0
(blueprint: def-pur-coordinate-section-projective-arrows). -/
def projectiveZero (T : Scheme.{u}) : T ⟶ ProjectiveLine T :=
  sectionMap T ≫ ProjectiveLine.affineChart T

/-- Its ordinary supported Cartier map, selected by the same unique relative-boundary
normalization as the affine map. Source: blueprint c^e_(D_0,A)
(blueprint: def-pur-coordinate-section-projective-arrows). -/
def projectiveSupported (A : Type (u + 1)) [CommRing A] [Finite A]
    (T : Scheme.{u}) [IsClosedImmersion (projectiveZero T)]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (projectiveZero T).ker.IsInvertible) :=
  Etale.supportedExactDerivedMap
    (Etale.lowerStar (ModuleCat.{u + 1} A) (projectiveZero T))
    (Etale.ordinaryFiniteConstant A T)
    (Scheme.finiteEtaleTateLine (ProjectiveLine T) N A hA)
    ((Etale.ordinary_supported_kummer_uniqueBoundary (ProjectiveLine T) N hN A hA
      (affineTraceProjectiveInvertible N T hT) (projectiveZero T) hI).exists.choose)

/-- The zero divisor has O(D_0)=O(1), and its actual supported map forgets to the
positive Kummer Chern class. Applying the q-adjunction gives exactly h in the node.
Source: blueprint projective divisor and forgetting-support clauses, Steps 1--3
(blueprint: def-pur-coordinate-section-projective-arrows). -/
def ProjectiveNormalization (P : WeilConjectures.PurityFiniteSetting.{u})
    (T : Scheme.{u}) [IsNoetherian T] [IsClosedImmersion (projectiveZero T)] : Prop :=
  ∃ hI : (projectiveZero T).ker.IsInvertible,
    Nonempty ((projectiveZero T).ker.toModules.dual ≅
      ProjectiveSpace.twist (ULift.{u} (Fin 2)) T 1) ∧
    ∀ (b : ℕ)
      (hA : ((P.coefficients.l ^ (b + 1) : ℕ) : AffineLinePurity.Ring P) = 0)
      (hT : IsUnit ((P.coefficients.l ^ (b + 1) : ℕ) : Γ(T, ⊤))),
      Etale.supportedDerivedUnit (AffineLinePurity.Ring P) (projectiveZero T) ≫
          projectiveSupported (AffineLinePurity.Ring P) T (P.coefficients.l ^ (b + 1))
            (pow_pos (Fact.out : P.coefficients.l.Prime).pos _) hA hT hI =
        (Etale.projectiveLineTraceDatum (P.coefficients.l ^ (b + 1))
          (pow_pos (Fact.out : P.coefficients.l.Prime).pos _)
          (AffineLinePurity.Ring P) hA T hT).chern

end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
