/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.Paper.FiniteSmoothAdjunctionData
import Sheaf.Paper.FiniteNormalizedOrientationScalar

/-! # Quotient reduction of the normalized inverse orientation

Source: latest blueprint, reduction compatibility (3), Orientation.
(blueprint: lem-pur-quotient-inverse-orientation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- Only the dualizing orientation, before tensoring with an arbitrary input,
commutes with quotient coefficients.
Source: latest blueprint, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-compatibilities.proof.md (3), Orientation.
(blueprint: lem-pur-quotient-inverse-orientation).

Proof: apply the existing normalizedOrientation_scalar theorem to the actual
quotient, with N=ell^r and M=ell^m. Primality gives positivity and m<=r gives
divisibility. Germwise invertibility of ell gives invertibility on global sections
of Y, hence of N. The two levels already supply the required invertibility on X.
Their geometry witnesses lie in Prop, so proof irrelevance identifies them; their
orientation witnesses are exactly the two required normalizations. This yields
the inverse-orientation equation directly, including r=m and d=0. -/
theorem quotientInverseOrientation
    (ell : ℕ) [Fact ell.Prime]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    [LocallyOfFiniteType f] (d : ℕ) [SmoothOfRelativeDimension d f]
    (hY : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y))
    (r m : ℕ) (_hm : 1 ≤ m) (hmr : m ≤ r)
    (a : Level ell r f d) (b : Level ell m f d)
    (e : CoefficientLineComparison (FiniteReduction.quotient ell hmr)
      (ell ^ r) (ell ^ m) (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) X) :
    (ordinaryScalar (FiniteReduction.quotient ell hmr) X).map a.alpha.inv ≫
        ExceptionalCoefficients.dualizingScalarMap (FiniteReduction.quotient ell hmr) f =
      (e.tensorPower d).hom ≫ b.alpha.inv := by
  have hYunit : IsUnit (ell : Γ(Y, ⊤)) := by
    apply Y.toRingedSpace.isUnit_of_isUnit_germ
    intro y hy
    simpa only [map_natCast] using hY y
  have hYr : IsUnit (ell ^ r : Γ(Y, ⊤)) := hYunit.pow r
  exact normalizedOrientation_scalar (FiniteReduction.quotient ell hmr)
    (ell ^ r) (ell ^ m) (pow_pos (Fact.out : ell.Prime).pos r)
    (pow_pos (Fact.out : ell.Prime).pos m) (pow_dvd_pow ell hmr)
    (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _)
    (by simpa only [Nat.cast_pow] using hYr) f d a.geometry
    a.invertible b.invertible a.alpha b.alpha a.orientation b.orientation e

end AlgebraicGeometry.Etale.FiniteSmoothPurity
