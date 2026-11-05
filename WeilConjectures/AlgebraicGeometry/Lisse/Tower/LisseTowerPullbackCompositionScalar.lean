/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerFixedPullbackScalar
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
import all WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantCoherence
import all WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerFixedPullbackScalar

/-! # Composition of ringed inverse images and restriction of coefficients

The composition comparison of module inverse images, conjugate to the restriction of
sections along the fibre-product pasting isomorphism, is compatible with the
restriction/pullback mates along the quotient coefficient maps.

Source: Stacks Project, Modules on Sites, Tags 03D8 and 03DA; Cohomology on Sites,
Tag 0D6D.
-/

public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

section Composition

variable {X Y W : Scheme.{u}} (f : W ⟶ Y) (g : Y ⟶ X)
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (j : ℕ)

/- Restriction of a section of a sheaf of modules along a morphism. -/

/-- The restriction/pullback comparison for the identified-coefficient inverse image. -/
@[expose] def lisseTowerBaseRestriction (g : Y ⟶ X) (n : ℕ) :
    pbcRestrict (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)) ⋙
        proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op (n + 1)))
          (lisseTowerPulledRing d g (n + 1)) (Iso.refl _) ⟶
      proEtaleRingModulePullback g ((pbcAdicRings X d).obj (op n))
          (lisseTowerPulledRing d g n) (Iso.refl _) ⋙
        pbcRestrict ((adicTowerInverseImage g).map
          (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))) :=
  proEtaleRingRestrictionPullbackInv g ((pbcAdicRings X d).obj (op (n + 1)))
    ((pbcAdicRings X d).obj (op n)) (lisseTowerPulledRing d g (n + 1))
    (lisseTowerPulledRing d g n) (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n))
    ((adicTowerInverseImage g).map (pbcAdicQuotient X d (n + 1) n (Nat.le_succ n)))
    (Iso.refl _) (Iso.refl _) ((Category.id_comp _).trans (Category.comp_id _).symm)

end Composition

end AlgebraicGeometry.Scheme
