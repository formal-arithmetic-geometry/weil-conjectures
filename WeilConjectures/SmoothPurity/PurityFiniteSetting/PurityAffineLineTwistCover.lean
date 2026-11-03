/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructure
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar

/-! # A common etale cover for the two finite root lines -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

/-- One finite etale cover trivializes the ordinary and comparison-pulled-back root lines.
Source: finite etale twist-line theorem and naturality of comparison inverse image.
(blueprint: lem-pur-affine-line-boundary-cover). -/
theorem affine_line_boundary_cover (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :
    ∃ V : Scheme.Cover.{u} Scheme.etalePrecoverage (Line Y), ∀ i : V.I₀,
      Nonempty ((Etale.upperStar (Modules P) (V.f i)).obj (P.twistEtale h (Line Y)) ≅
        P.constantEtale (V.X i)) ∧
      Nonempty ((upperStar (Modules P) (V.f i)).obj (P.twist h (Line Y)) ≅
        P.constant (V.X i)) := by
  have hN : 0 < P.exponent := pow_pos (Fact.out : P.coefficients.l.Prime).pos _
  have hInv (t : Line Y) : IsUnit (P.exponent : (Line Y).presheaf.stalk t) := by
    simpa only [map_natCast] using (P.exponent_isUnit (Line Y)
      (lineProjection Y ≫ a)).map ((Line Y).presheaf.germ ⊤ t (by trivial)).hom
  obtain ⟨V, hV⟩ := (Scheme.finite_etale_torsion_twist_line (Line Y)
    P.exponent hN hInv P.Coefficient (P.exponent_coefficient_eq_zero h) 1).1
  refine ⟨V, fun i ↦ ?_⟩
  let U := V.etalePrecoverageToEtale i
  let cst := (Scheme.Etale.overEquiv U).constantSheafSheafCongrIso
    ((Line Y).smallEtaleTopology.over U) U.left.smallEtaleTopology (Modules P)
    Over.mkIdTerminal
  let ei : (Etale.upperStar (Modules P) (V.f i)).obj (P.twistEtale h (Line Y)) ≅
      P.constantEtale (V.X i) :=
    (Scheme.overSheafEquivFunctorObjOverIso (Modules P) U _).symm ≪≫
      (Scheme.Etale.overSheafEquiv U (Modules P)).functor.mapIso (hV i).some ≪≫
      cst.app (ModuleCat.of P.Coefficient P.Coefficient)
  refine ⟨⟨ei⟩, ⟨?_⟩⟩
  exact (comparisonUpperStarUpperStarIso (Modules P) (V.f i)).app
    (P.twistEtale h (Line Y)) ≪≫ (comparisonUpperStar (Modules P) (V.X i)).mapIso ei

end WeilConjectures.PurityFiniteSetting
