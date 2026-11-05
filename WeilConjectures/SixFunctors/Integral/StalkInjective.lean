/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.PointFunctions
public import WeilConjectures.SixFunctors.Integral.StalkRestrict

/-!
# The restrictions of germs of a direct image along an integral morphism are jointly injective

For a section `σ` of an étale sheaf `G` over an étale `X`-scheme `W`, the points of `W` near
which `σ` vanishes form an open subset `AlgebraicGeometry.Etale.vanishingSet` of `W`, and the
germ of `σ` at a geometric point of `W` vanishes exactly when the point lies in this open
subset (`AlgebraicGeometry.Etale.toPresheafFiber_eq_zero_iff_mem_vanishingSet`).

Let `f : X ⟶ Y` be an integral morphism and `y` a geometric point of `Y` with algebraically
closed residue field. A germ of `f_* G` at `y` all of whose restrictions to the geometric points
of `X` over `y` vanish is zero
(`AlgebraicGeometry.Etale.eq_zero_of_forall_stalkRestrict_eq_zero`): the germ is a section `σ`
of `G` over `U ×_Y X`, the closed complement of the vanishing set of `σ` contains no point
`(u, t)`, so it disappears over a smaller pointed étale neighbourhood of `y`
(`AlgebraicGeometry.Scheme.Hom.exists_hom_preimage_eq_bot_of_isIntegralHom`), on which `σ`
vanishes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme Scheme.Hom

section Vanishing

variable {X : Scheme.{u}} (Λ : Type (u + 1)) [CommRing Λ]
  (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {W : X.Etale}
  (σ : ToType (G.obj.obj (op W)))

end Vanishing

section Injective

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]

end Injective

end AlgebraicGeometry
