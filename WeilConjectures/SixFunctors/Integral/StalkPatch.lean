/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.FibreTopology
public import WeilConjectures.SixFunctors.Integral.StalkInjective

/-!
# Patching germs of a direct image along an integral morphism

Let `f : X ⟶ Y` be an integral morphism, `y` a geometric point of `Y` with algebraically closed
residue field and `(U₀, u₀)` an affine pointed étale neighbourhood of `y`. Given finitely many
germs `a i` of `f_* G` at `y` and a decomposition `m` of the geometric fibre of `f` over `y`
which only depends on the values of `(u₀, t)` on finitely many functions on `U₀ ×_Y X`, there is
a germ of `f_* G` at `y` whose restriction to every geometric point `t` over `y` is that of
`a (m t)` (`AlgebraicGeometry.Etale.exists_stalkRestrict_eq_of_finset`): after shrinking the
neighbourhood, `U ×_Y X` decomposes into disjoint opens adapted to `m`
(`AlgebraicGeometry.Scheme.Hom.Nbhd.exists_pointed_disjoint_cover`), and the representatives of
the `a i` glue along this decomposition.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme Scheme.Hom

namespace Scheme.Hom.Nbhd

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] {y : Spec (.of Ω) ⟶ Y}

end Scheme.Hom.Nbhd

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f]

end AlgebraicGeometry
