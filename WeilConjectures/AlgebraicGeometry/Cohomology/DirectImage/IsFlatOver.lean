/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-!
# Transport of flatness over the base

Flatness of an `𝒪_X`-module over the base (`AlgebraicGeometry.Scheme.Modules.IsFlatOver`) is
invariant under isomorphisms of modules, passes to the pullback along an open immersion into the
source, and can be checked after composing with an open immersion of the base.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X X' T T' : Scheme.{u}}

/-- Flatness over the base is invariant under isomorphisms of modules. -/
theorem IsFlatOver.of_iso {ℱ ℱ' : X.Modules} (e : ℱ ≅ ℱ') {f : X ⟶ T} (h : ℱ.IsFlatOver f) :
    ℱ'.IsFlatOver f :=
  sorry

/-- Flatness over the base passes to the pullback along an open immersion into the source. -/
theorem IsFlatOver.pullback_of_isOpenImmersion {ℱ : X.Modules} {f : X ⟶ T} (h : ℱ.IsFlatOver f)
    (j : X' ⟶ X) [IsOpenImmersion j] : ((Modules.pullback j).obj ℱ).IsFlatOver (j ≫ f) :=
  sorry

/-- Flatness over the base can be checked after composing with an open immersion of the base. -/
theorem IsFlatOver.of_comp_isOpenImmersion {ℱ : X.Modules} {f : X ⟶ T} (ι : T ⟶ T')
    [IsOpenImmersion ι] (h : ℱ.IsFlatOver (f ≫ ι)) : ℱ.IsFlatOver f :=
  sorry

end AlgebraicGeometry.Scheme.Modules
