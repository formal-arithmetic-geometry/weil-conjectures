/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProperOpenGamma
public import WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
public import WeilConjectures.CategoryTheory.Adjunction.ProperOpenTransport

/-!
# Strict reduction comparisons for completed operations

Strict reduction followed by constant-coefficient restriction compares completed-ring
objects with derived strict towers of constant-coefficient modules. This file records its
comparisons with inverse images.

Source: Weil conjectures blueprint, node thm-cbc-complete-proetale, proof step 8
(blueprint: thm-cbc-complete-proetale).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe t

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- Strict reduction followed by constant-coefficient restriction: the comparison of
completed-ring objects with derived strict towers of constant-coefficient modules.
Source: blueprint step 8 (blueprint: thm-cbc-complete-proetale). -/
abbrev cbcStrictReduction (T : Scheme.{t}) : d.derived T ⥤ ProEtale.StrictTower.Derived A T :=
  completedReductionTower T d ⋙ exchangeTowerRes d T

/-- Strict reduction commutes with inverse image: the normalized reduction/pullback
comparison followed by the restriction/pullback comparison.
Source: blueprint step 8 (blueprint: thm-cbc-complete-proetale). -/
def cbcStrictPull {U V : Scheme.{t}} (f : U ⟶ V) :
    d.pull f ⋙ cbcStrictReduction d U ≅
      cbcStrictReduction d V ⋙ ProEtale.StrictTower.G A f :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (d.reductionTowerPullbackIso f).symm (exchangeTowerRes d U) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (completedReductionTower V d) (exchangeResPull d f) ≪≫
    (Functor.associator _ _ _).symm

end AlgebraicGeometry.Scheme
