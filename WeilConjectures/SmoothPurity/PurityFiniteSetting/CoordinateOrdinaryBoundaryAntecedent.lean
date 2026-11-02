/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Coordinate.CoordinateLocalizationSplice
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineBoundaryRealization
import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateOrdinaryBoundaryAntecedentProTransport
import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateOrdinaryBoundaryAntecedentFaithfulTransport

/-! # Ordinary antecedent of the coordinate exceptional transpose

This isolates the shifted ordinary adjunction from closed-image site transport.
(blueprint: lem-pur-coordinate-ordinary-boundary-antecedent).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- The coordinate transpose is the comparison of its ordinary closed antecedent,
and the ordinary inverse adjunct of that antecedent is the original Ext morphism.

Source: current blueprint, cor-pur-affine-space-zero-section-purity.proof.md,
composition of ordinary adjunctions and finite etale-origin transport paragraphs;
Milne, Section 9, Example 9.5.
(blueprint: lem-pur-coordinate-ordinary-boundary-antecedent).

Proof: the affine-line boundary realization (lem-pur-affine-line-boundary-realization)
gives, for every realizing morphism, a unique ordinary etale antecedent with respect to
the comparison eK, and eK.hom = boundaryExceptionalComparison. Applied to
coordinateOrdinaryToGysin of the exact derived realization of c, this gives b and the
first equation. The second equation follows from the pro-etale counit transport
(new-lem-pur-coordinate-ordinary-boundary-antecedent-pro-transport), which gives it after
nu and the shift comparison, and the faithful descent along nu
(new-lem-pur-coordinate-ordinary-boundary-antecedent-faithful-transport). -/
theorem coordinateOrdinary_boundaryAntecedent
    (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aT] [QuasiCompact aT] [IsSeparated aT]
    (c : Ext ((Etale.lowerStar (Modules P) (zeroSection T)).obj (P.constantEtale T))
      (P.twistEtale h (Line T)) 2) :
    ∃ b : (DerivedCategory.singleFunctor (EtSheaves P T) 0).obj
        (P.constantEtale T) ⟶ P.boundaryEtaleValue h T,
      P.coordinateOrdinaryToGysin h T
          (Etale.supportedExactDerivedMap (Etale.lowerStar (Modules P) (zeroSection T))
            (P.constantEtale T) (P.twistEtale h (Line T)) c) =
        ((comparisonUpperStar (Modules P) T).mapDerivedCategorySingleFunctor 0).inv.app
          (P.constantEtale T) ≫ (nu P T).map b ≫ P.boundaryExceptionalComparison h T ∧
      ((Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategorySingleFunctor
          0).inv.app (P.constantEtale T) ≫
        (Etale.lowerStar (Modules P) (zeroSection T)).mapDerivedCategory.map b ≫
        P.boundaryEtaleCounit h T = c.hom := by
  obtain ⟨_, _, eK, _, _, heK, _, _, ⟨cc⟩, hrest⟩ :
      P.AffineLineBoundaryRealization h T aT :=
    (affine_line_boundary_realization P h T aT).2.2.2.2.2.2.2.2.2.2
  obtain ⟨_, _, _, _, _, _, _, _, hante, _⟩ := hrest cc
  obtain ⟨b, hb⟩ := (hante (P.coordinateOrdinaryToGysin h T
    (Etale.supportedExactDerivedMap
      (Etale.lowerStar (Modules P) (zeroSection T)) (P.constantEtale T)
      (P.twistEtale h (Line T)) c))).exists
  rw [heK] at hb
  exact ⟨b, hb.symm, coordinateOrdinary_boundaryAntecedent_faithfulTransport P h T aT c b
    (coordinateOrdinary_boundaryAntecedent_proTransport P h T aT c b hb)⟩

end WeilConjectures.PurityFiniteSetting
