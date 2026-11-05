/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.DisjointCover
public import WeilConjectures.AlgebraicGeometry.Morphisms.Integral.GeometricFiber

/-!
# Pointed decompositions of the base change of an integral morphism

Let `f : X ⟶ Y` be integral, `y : Spec Ω ⟶ Y` a geometric point with `Ω` algebraically closed
and `(U₀, u₀)` an affine pointed étale neighbourhood of `y`, with `U₀ ×_Y X = Spec B`. Suppose
that to every geometric point `t` of `X` over `y` is attached a standard étale `B`-algebra
`P (m t)` and a point `χ t` of it over `t`, in a way which only depends on the values of `t` on
finitely many elements of `B`. Then there is a smaller pointed étale neighbourhood `(U, u)` of
`y` and a decomposition of `U ×_Y X` into pairwise disjoint opens, each mapping to one of the
`Spec (P j)` over `Spec B`, such that the point `(u, t)` is carried to `χ t`
(`AlgebraicGeometry.Scheme.Hom.Nbhd.exists_pointed_disjoint_cover`).

This is the pointed refinement of `AlgebraicGeometry.Scheme.Hom.Nbhd.exists_hom_disjoint_cover`,
and it is proved in the same way: the data descend to a subalgebra `B₂ ⊆ B` finite over `A`,
where the pieces of a split neighbourhood of the finite morphism `Spec B₂ ⟶ U₀` realise them
(`AlgebraicGeometry.Scheme.Hom.SplitNbhd.exists_pieceFunctor_obj_hom`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TensorProduct RingHom

namespace AlgebraicGeometry

namespace Scheme.Hom.Nbhd

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
  {y : Spec (.of Ω) ⟶ Y}

end Scheme.Hom.Nbhd

end AlgebraicGeometry
