/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek

/-! # An ambient exchange formalism without a fixed base field

All schemes are allowed in the indexing category. This permits the same formal
pasting laws to be applied to geometric-fiber squares and to squares over a fixed field.
The pullbacks and adjunctions are the existing derived constructions.
-/

set_option profiler true
set_option profiler.threshold 0

@[expose] public noncomputable section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The derived exchange formalism on all schemes, so cross-field squares are included. -/
def purityAmbientExchangeFormalism : CompactSupportFormalism where
  obj X := DerivedCategory
    (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
  pb f := L((f)^*⟦Λ⟧)
  pbId X := leftDerivedUpperStarId Λ X
  pbComp f g := leftDerivedUpperStarComp Λ f g
  pbComp_assoc f g h K := leftDerivedUpperStarComp_assoc_app Λ f g h K
  pbId_comp f K := leftDerivedUpperStarComp_id_left_app Λ f K
  pbComp_id f K := leftDerivedUpperStarComp_id_right_app Λ f K
  pf f := R((f)_*⟦Λ⟧)
  adj f := derivedUpperStarLowerStarAdjunction Λ f
  sh j hj := have := hj.out; D((j)_!open⟦Λ⟧)
  shAdj j hj := have := hj.out;
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
      (leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm

end AlgebraicGeometry.ProEtale.CondensedRing
