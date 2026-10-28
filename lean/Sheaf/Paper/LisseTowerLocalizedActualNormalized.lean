/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J7
-/
module

public import Sheaf.Paper.LisseTowerPulledScalar

/-! # Normalized transitions for localized actual realizations

This is the transition-equation part of the actual localized realization argument.
Source: Stacks Project, Tags 03CY, 03DA and 06YY.
(blueprint: lem-weil-pbc-lisse-tower-localized-actual-normalized).
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

/-- The localized level comparisons satisfy the displayed normalized transition
identity.  This statement takes a family of level comparisons as input, so it is
strictly the coherence half of the actual-localization argument.
Source: Stacks Project, Tags 03CY, 03DA and 06YY.
(blueprint: lem-weil-pbc-lisse-tower-localized-actual-normalized).

Proof: compare the two composites before localization after forgetting to abelian
sheaves.  The section-normalized scalar square makes the coefficient-interchange cube
commute.  Localize this equality, retain the canonical inverse-image and restriction
compositors, and apply it to `hδ`; naturality of the level comparisons moves `e n` and
`e (n+1)` through the cube.  The result is the stated equation after the common
invertible comparison factors are cancelled.
-/
theorem lisseTower_localized_actual_normalized
    (X Y : Scheme.{u}) (g : Y ⟶ X)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (U : Y.ProEt) (V : U.left.ProEt) (W : Y.ProEt)
    (f : W ⟶ ProEt.mk (V.hom ≫ U.hom))
    (D : ∀ n : ℕ, DerivedCategory
      (Sheaf U.left.smallEtaleTopology (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))))
    (c : ∀ n : ℕ, LisseTowerScalarSquare (U.hom ≫ g) d n)
    (hc : ∀ n : ℕ, LisseTowerScalarSquareSections (U.hom ≫ g) d n (c n))
    (δ : ∀ n : ℕ, D (n + 1) ⟶
      (normalizationRestrict U.left.smallEtaleTopology (lisseTowerEtaleQuotient d n)).obj
        (D n))
    (e : ∀ n : ℕ, (lisseTowerEtaleRealization (U.hom ≫ g) d n).obj (D n) ≅
      (adicTowerPullback (U.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n))
    (hδ : ∀ n : ℕ,
      (lisseTowerEtaleRealization (U.hom ≫ g) d (n + 1)).map (δ n) ≫
          (lisseTowerEtaleScalarIso (U.hom ≫ g) d n (c n)).hom.app (D n) ≫
          (pbcDerivedRestrict ((adicTowerInverseImage (U.hom ≫ g)).map
            (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))).map (e n).hom =
        (e (n + 1)).hom ≫
          adicTowerRestrictedTransition d (U.hom ≫ g) M (n + 1) n (Nat.le_succ n))
    (actual : ∀ (n : ℕ),
      ((ProEtale.upperStar
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) f.left).mapDerivedCategory ⋙
        lisseTowerFixedRealization (W.hom ≫ g) d n).obj
        ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≅
      (adicTowerPullback (W.hom ≫ g) ((pbcAdicRings X d).obj (op n))).obj (M.level n)) :
    ∀ (n : ℕ),
    let L (j : ℕ) := (ProEtale.upperStar
      (ModuleCat.{u + 1} (lisseTowerEtaleRing d j)) f.left).mapDerivedCategory ⋙
        lisseTowerFixedRealization (W.hom ≫ g) d j
    let H (k : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection (W.hom ≫ g) d k)
    (H (n + 1)).map ((L (n + 1)).map
      (localProEtaleNormalization V.hom (lisseTowerEtaleQuotient d n) (δ n))) ≫
      (lisseTowerPulledScalarIso (W.hom ≫ g) f.left d n).hom.app
        ((localProEtaleComparison V.hom (lisseTowerEtaleRing d n)).obj (D n)) ≫
      (H n).map (actual n).hom =
    (H (n + 1)).map (actual (n + 1)).hom ≫
      constantAdicRestrictedStep (W.hom ≫ g) d M n := by
  sorry

end AlgebraicGeometry.Scheme
