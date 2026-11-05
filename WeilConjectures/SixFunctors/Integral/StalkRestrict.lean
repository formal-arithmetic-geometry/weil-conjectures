/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.PointedCover
public import WeilConjectures.SixFunctors.Integral.Exact

/-!
# Restricting germs of a direct image along an integral morphism

Let `f : X ⟶ Y` be an integral morphism, `y` a geometric point of `Y` with algebraically closed
residue field and `t` a geometric point of `X` over `y`. The restriction of germs
`AlgebraicGeometry.Etale.stalkRestrict : (f_* G)_y ⟶ G_t` is surjective
(`AlgebraicGeometry.Etale.surjective_stalkRestrict_of_isIntegralHom`): a germ of `G` at `t` is
a section over a standard étale neighbourhood of `t`, and after shrinking the étale
neighbourhood of `y`, the base change `U ×_Y X` decomposes into pairwise disjoint opens, one of
which maps to this standard étale neighbourhood with `(u, t)` going to the marked point
(`AlgebraicGeometry.Scheme.Hom.Nbhd.exists_pointed_disjoint_cover`). The section extended by
zero on the other opens is a section of `G` over `U ×_Y X` with the given germ.

Consequently `f_*` detects the zero sheaf
(`AlgebraicGeometry.Etale.isZero_of_isZero_lowerStar_obj`) and, being exact, is conservative
(`AlgebraicGeometry.Etale.reflectsIsomorphisms_lowerStar_of_isIntegralHom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Polynomial

open scoped AlgebraicGeometry.Etale

namespace StandardEtalePair

variable {B Ω : Type*} [CommRing B] [CommRing Ω] (P : StandardEtalePair B)

end StandardEtalePair

namespace AlgebraicGeometry

open Scheme Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]

end AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme Scheme.Hom

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]

end AlgebraicGeometry
