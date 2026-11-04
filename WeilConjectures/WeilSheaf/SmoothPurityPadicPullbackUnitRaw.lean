/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarPullback

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

attribute [local instance 20000] Sheaf.monoidalCategory Sheaf.braidedCategory

variable {X U : Scheme.{u}} (g : U ⟶ X) (l : ℕ) [Fact l.Prime]

set_option diagnostics true in
set_option diagnostics.threshold 1000 in
/-- The integral coefficient pullback unit with a fixed instance convention. -/
noncomputable def purityPadicPullbackUnitRaw
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj ℤ_[l]) X)) :
    (g)^*[Ab.{u + 1}].obj M.X ⟶
      ((g)^*⟦Profinite.continuousMapRingObj ℤ_[l]⟧.obj M).X :=
  CondensedRing.upperStarUnitHom (Profinite.continuousMapRingObj ℤ_[l]) g M

end AlgebraicGeometry.ProEtale
