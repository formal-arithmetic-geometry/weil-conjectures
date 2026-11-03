/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityGysinStructure
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval

/-! # The finite root line has Tor interval zero on both sites -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport
namespace WeilConjectures.PurityFiniteSetting

/-- Flatness of the actual finite etale line gives the zero Tor interval; comparison
preserves that exact interval, including tests on nonclassical pro-etale modules.
Source: finite twist-line flatness and comparison Tor-interval theorem.
(blueprint: lem-pur-affine-line-boundary-twist-tor). -/
theorem affine_line_boundary_twist_tor (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k)) :
    Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient (Line Y) 0 0
      (P.gysinEtaleInput h Y).obj ∧
    Scheme.HasProEtaleTorAmplitude (Line Y) P.Ring
      ((finiteCoefficientIntrinsicRealization (Line Y) P.Ring).mapDerivedCategory.obj
        (P.gysinInput h Y).obj) 0 0 := by
  have hN : 0 < P.exponent := pow_pos (Fact.out : P.coefficients.l.Prime).pos _
  have hInv (t : Line Y) : IsUnit (P.exponent : (Line Y).presheaf.stalk t) := by
    simpa only [map_natCast] using (P.exponent_isUnit (Line Y)
      (lineProjection Y ≫ a)).map ((Line Y).presheaf.germ ⊤ t (by trivial)).hom
  let := Sheaf.monoidalCategory (Line Y).smallEtaleTopology (Modules P)
  have hflat : ObjectProperty.flat (P.twistEtale h (Line Y)) := by
    apply (ObjectProperty.flat_iff_preservesFiniteLimits _).2
    exact (Scheme.finite_etale_torsion_twist_line (Line Y) P.exponent hN hInv
      P.Coefficient (P.exponent_coefficient_eq_zero h) 1).2.2.1
  have ht : Etale.DerivedCategory.hasTorAmplitudeIn P.Coefficient (Line Y) 0 0
      (P.gysinEtaleInput h Y).obj :=
    Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2
      (DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat hflat)
  exact ⟨ht, (comparison_torAmplitudeIn_iff P.Ring (Line Y) 0 0 le_rfl
    (P.gysinEtaleInput h Y)).1 ht⟩

end WeilConjectures.PurityFiniteSetting
