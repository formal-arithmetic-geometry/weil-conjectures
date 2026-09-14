/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.Modules.PicardField
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal

/-!
# A line bundle pulled back along a constant morphism is trivial

Let `K` be a field, let `S` and `V` be `K`-schemes and let `v ∈ V(K)` be a `K`-rational point of
`V`. The *constant morphism at `v`* is the composite `π ≫ v : S ⟶ V` of the structure morphism
`π : S ⟶ Spec K` with `v : Spec K ⟶ V`. This file proves that every line bundle on `V` pulls
back along it to the structure sheaf of `S`.

The proof is the one of the blueprint: pullback is pseudofunctorial, so `(π ≫ v)^* N` is
`π^* (v^* N)`; the line bundle `v^* N` on `Spec K` is trivial because the Picard group of the
spectrum of a field is trivial; and `π^*` is monoidal, so it takes the structure sheaf of
`Spec K` to the structure sheaf of `S`.

The two corollaries are the forms used later, on the category `Over (Spec (CommRingCat.of K))`
of `K`-schemes: the constant morphism at a `K`-point `v : 𝟙_ _ ⟶ V`, and, when `V` carries a
group structure, the constant morphism at its identity section `η[V]`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_tensorUnit_of_comp`
  (`lem:cube-pullback-constant`): the pullback of a line bundle along a constant morphism
  `π ≫ v : S ⟶ V` of `K`-schemes is isomorphic to the structure sheaf of `S`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_tensorUnit_of_toUnit_comp`
  (`lem:cube-pullback-constant`): the same statement for `K`-schemes `S` and `V` in
  `Over (Spec (CommRingCat.of K))` and a `K`-point `v` of `V`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_tensorUnit_of_toUnit_comp_one`
  (`lem:cube-pullback-constant`): the same statement for the constant morphism at the identity
  section of a group scheme over `K`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

open scoped MonObj

namespace AlgebraicGeometry.Scheme

variable {K : Type u} [Field K]

/-- **A line bundle pulled back along a constant morphism is trivial.** Let `S` and `V` be
`K`-schemes, let `v : Spec K ⟶ V` be a `K`-rational point of `V` and let `π ≫ v : S ⟶ V` be the
constant morphism at `v`, `π : S ⟶ Spec K` being the structure morphism of `S`. Then the
pullback of a line bundle `N` on `V` along `π ≫ v` is isomorphic to the structure sheaf of `S`.

This is `lem:cube-pullback-constant` of the theorem-of-the-cube chapter. -/
theorem Modules.nonempty_pullback_iso_tensorUnit_of_comp {S V : Scheme.{u}}
    (π : S ⟶ Spec (.of K)) (v : Spec (.of K) ⟶ V) {N : V.Modules} (hN : N.Invertible) :
    Nonempty ((Modules.pullback (π ≫ v)).obj N ≅ 𝟙_ S.Modules) := by
  obtain ⟨e⟩ := Modules.nonempty_iso_tensorUnit_of_invertible (hN.pullback v)
  exact ⟨(Modules.pullbackComp π v).symm.app N ≪≫ (Modules.pullback π).mapIso e ≪≫
    (Functor.Monoidal.εIso (Modules.pullback π)).symm⟩

variable {S V : Over (Spec (.of K))}

/-- **A line bundle pulled back along a constant morphism is trivial**, for `K`-schemes `S` and
`V` presented as objects of `Over (Spec (CommRingCat.of K))` and a `K`-point `v` of `V`, the
constant morphism at `v` being `toUnit S ≫ v`. -/
theorem Modules.nonempty_pullback_iso_tensorUnit_of_toUnit_comp (v : 𝟙_ (Over (Spec (.of K))) ⟶ V)
    {N : V.left.Modules} (hN : N.Invertible) :
    Nonempty ((Modules.pullback (toUnit S ≫ v).left).obj N ≅ 𝟙_ S.left.Modules) :=
  Modules.nonempty_pullback_iso_tensorUnit_of_comp S.hom v.left hN

/-- **A line bundle pulled back along the constant morphism at the identity section of a group
scheme is trivial.** If `V` is a group scheme over `K` with identity section `η[V]` and `S` is a
`K`-scheme, the pullback of a line bundle on `V` along `toUnit S ≫ η[V]` is isomorphic to the
structure sheaf of `S`. -/
theorem Modules.nonempty_pullback_iso_tensorUnit_of_toUnit_comp_one [GrpObj V]
    {N : V.left.Modules} (hN : N.Invertible) :
    Nonempty ((Modules.pullback (toUnit S ≫ η[V]).left).obj N ≅ 𝟙_ S.left.Modules) :=
  Modules.nonempty_pullback_iso_tensorUnit_of_toUnit_comp η[V] hN

end AlgebraicGeometry.Scheme
