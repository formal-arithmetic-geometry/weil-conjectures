/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData

/-! # Scalar compatibility of the normalized finite diagonal

Source: current general-ring smooth purity, paragraphs (1)--(2).
(blueprint: lem-sp-finite-scalar-diagonal-compatibility). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- The scalar square for an already constructed, normalized ordinary orientation.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.proof.md, paragraphs (1)--(2).
(blueprint: lem-sp-finite-scalar-diagonal-compatibility).

Proof: compute the exceptional coefficient mate on a smooth etale chart by the
scalar extension of the compact-support adjunction counit. The two free summands
in the projective-line calculation and the Kummer boundary class extend along
phi, so the normalized local adjunctions have the same scalar-extension formula.
Tensoring the rank-one lines computes derived extension without any assumption
that the target coefficient ring is flat. Pull back these comparisons to the
smooth diagonal. On its deformation space, both coefficient comparisons restrict
to the specified comparison at t=1. Uniqueness of this normalization identifies
them on the Rees space and therefore at t=0. The bundle integration adjunctions
are the same local adjunctions just computed; compatibility on overlapping charts
identifies their gluing. After cancelling the common cohomological shift, these
are maps of locally constant rank-one sheaves, so equality on the chart cover
implies global equality. Finally paste the exact etale/pro-etale realization
square and its scalar unit. The comparison counit is invertible at the coefficient
unit, and the exceptional coefficient mate is invertible by finite coefficient
change. This proves invertibility of both specified maps and the displayed square.
Dimension zero uses the empty tensor; the argument requires neither nonzero
coefficients nor a nonempty scheme. No data are chosen in this statement.
-/
theorem finiteScalarDiagonalCompatibility
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (A : Type u) [CommRing A] [Finite A]
    (hA : (P.diagonalExponent : A) = 0) (phi : P.Ring →+* A)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [QuasiCompact f] [HasCompactification f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (t : Etale.FiniteSmoothPurity.CoefficientLineComparison
      (RingHom.ulift.{u + 1, u + 1, u, u} phi)
      P.diagonalExponent P.diagonalExponent P.diagonalExponent_annihilates
      (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) X)
    (G : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (alpha : Etale.dualizingComplex (ULift.{u + 1, u} A) f ≅
      Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} A) P.diagonalExponent
        (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) X d)
    (hα : Etale.FiniteSmoothPurity.OrientationNormalized (ULift.{u + 1, u} A)
      P.diagonalExponent (pow_pos P.coefficients.prime.out.pos P.level)
      (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA)
      f d G (P.diagonalExponent_isUnit (f ≫ aY)) alpha) :
    ∃ hu : IsIso (finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f),
      IsIso (finiteGeneralRingReduction P phi f) ∧
      finiteGeneralRingReduction P phi f ≫
        @inv _ _ _ _ (finiteGeneralRingDualizingUnitMap (ULift.{u + 1, u} A) f) hu ≫
        (Etale.FiniteSmoothPurity.comparison (ULift.{u + 1, u} A) X).map alpha.hom =
      (finiteGeneralRingOrientationExtension P phi
        (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) d f aY t).hom := by sorry

end AlgebraicGeometry.ProEtale
