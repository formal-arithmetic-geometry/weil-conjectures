/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Flatness of a sheaf of modules over the base of a morphism

Let `f : X ⟶ Y` be a morphism of schemes. A sheaf of `𝒪_X`-modules `F` is *flat over `Y`* if
each of its stalks `F_x` is a flat module over the local ring `𝒪_{Y, f x}` of the base, the
module structure being restriction of scalars along `f.stalkMap x`. This is the definition of
[Stacks, 01U3], and it is the flatness hypothesis of the semicontinuity theorem and of Grauert's
theorem in the chapter on the theorem of the cube.

Note that flatness of `F` over `Y` is a condition on the pair `(F, f)`: it is *not* flatness of
`f` itself, and it is not flatness of `F` over `X`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.FlatOver`: a sheaf of `𝒪_X`-modules is flat over the base of
  `f : X ⟶ Y` if each of its stalks is a flat module over the corresponding local ring of `Y`.

## Implementation notes

* `FlatOver` is a `class`, like `SheafOfModules.IsCoherent`, `SheafOfModules.IsLocallyFree` and
  `SheafOfModules.IsFiniteType`: the statements that consume it — semicontinuity and Grauert —
  take it as an instance argument, and the lemmas that will produce it (a locally free sheaf is
  flat over the base, flatness is stable along a flat morphism of bases) are meant to be
  instances too.
* The module structure on the stalk over the local ring of the base is
  `AlgebraicGeometry.Scheme.Modules.moduleStalkBase`. It cannot be an instance, since it depends
  on `f`, so it is introduced by `letI` in the definition.

## References

* [Stacks, 01U3](https://stacks.math.columbia.edu/tag/01U3)

## Blueprint

Flatness of a sheaf of modules over the base of a morphism is part of the open obligation
attached to `prop:cube-semicontinuity` in the chapter on the theorem of the cube; it is the
hypothesis "`F` is flat over `T`" of that proposition and of `prop:cube-grauert`.
-/

@[expose] public section

universe u

open CategoryTheory SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

/-- A sheaf of `𝒪_X`-modules `F` is **flat over `Y`** along `f : X ⟶ Y` if for every `x : X` the
stalk `F_x` is a flat module over the local ring `𝒪_{Y, f x}` of the base, the module structure
being the one given by `AlgebraicGeometry.Scheme.Modules.moduleStalkBase`. -/
@[stacks 01U3]
class FlatOver (F : X.Modules) (f : X ⟶ Y) : Prop where
  /-- Every stalk of `F` is flat over the local ring of the base at its image. -/
  flat_stalk (x : X) : letI := moduleStalkBase F f x
    Module.Flat (Y.presheaf.stalk (f.base x)) (F.presheaf.stalk x)

end AlgebraicGeometry.Scheme.Modules
