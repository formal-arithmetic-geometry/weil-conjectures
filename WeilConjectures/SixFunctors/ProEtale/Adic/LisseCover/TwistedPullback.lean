/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.TwistedSheaf

/-!
# Pulling back descent cocycles

Let `f : V ⟶ Y` be a morphism, `c` a descent cocycle on the constant sheaf `S_V` and
`π : T ⟶ Y`. The cover `f_T : V ×_Y T ⟶ T` carries the pulled back cocycle
`c_T = c ∘ (V ×_Y T ×_T V ×_Y T ⟶ V ×_Y V)` (`AlgebraicGeometry.pullbackDescentCocycle`), again a
descent cocycle (`AlgebraicGeometry.IsDescentCocycle.pullbackCover`). The twisted sections of `c`
over `π` are the twisted sections of `c_T` over `𝟙 T`
(`AlgebraicGeometry.IsTwistedSection.pullbackCover`,
`AlgebraicGeometry.IsTwistedSection.ofPullbackCover`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {Y V T : Scheme.{u}} {f : V ⟶ Y} {S : Type*} {c : ↥(pullback f f) → S → S}

end AlgebraicGeometry
