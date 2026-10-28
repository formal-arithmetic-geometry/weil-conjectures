/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J7
-/
module

public import Sheaf.Paper.LisseTowerPulledScalar

/-! # Level comparisons for localized actual realizations

This is the level-comparison part of the actual localized realization argument.
Source: Stacks Project, Tags 03CY and 03DA.
(blueprint: lem-weil-pbc-lisse-tower-localized-actual-levels).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow lisseTowerAlgebraArrow

/-- Construct the actual comparison at every finite level after one more pro-etale
localization.  The construction pastes the canonical inverse-image comparison with
the supplied level comparison `e`; it uses no transition equation.
Source: Stacks Project, Tags 03CY and 03DA.
(blueprint: lem-weil-pbc-lisse-tower-localized-actual-levels).

Proof: identify fixed realization after inverse image with module inverse image after
fixed realization using the sheafification and inverse-image adjunctions.  Localize
that canonical comparison and paste the inverse-image compositors for `f.left`,
`V.hom`, and `U.hom` followed by `g`; the equality encoded by `f.w` identifies the
resulting scheme map with `W.hom`.  Apply the resulting comparison to `e n` for each
`n`.
-/
theorem lisseTower_localized_actual_levels
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (U : Y.ProEt) (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom))
    (D : ∀ n : ℕ, DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (e : ∀ n : ℕ, (lisseTowerEtaleRealization (U.hom ≫ g) d n).obj (D n) ≅
      (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n)) :
    let L (j : ℕ) := (ProEtale.upperStar
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f.left).mapDerivedCategory ⋙
        lisseTowerFixedRealization (W.hom ≫ g) d j
    Nonempty (∀ (n : ℕ),
    (L n).obj
      ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≅
      (adicTowerPullback (W.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n)) := by
  sorry

end AlgebraicGeometry.Scheme
