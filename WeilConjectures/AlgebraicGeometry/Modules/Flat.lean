/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyTrivial
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

The file also proves that a **line bundle on the source of a flat morphism is flat over the
base**: its stalks are free of rank one over the local rings of the source, which are flat over
the local rings of the base.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.FlatOver`: a sheaf of `𝒪_X`-modules is flat over the base of
  `f : X ⟶ Y` if each of its stalks is a flat module over the corresponding local ring of `Y`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.flatOver_of_flat_stalk`: a sheaf of modules whose stalks are
  flat over the local rings of the source is flat over the base of a flat morphism.
- `SheafOfModules.Invertible.flat_stalk` and `SheafOfModules.Invertible.flatOver`: the stalks of
  an invertible sheaf of modules are flat over the local rings of the scheme, and it is
  therefore flat over the base of a flat morphism.

## Implementation notes

* `FlatOver` is a `class`, like `SheafOfModules.IsCoherent`, `SheafOfModules.IsLocallyFree` and
  `SheafOfModules.IsFiniteType`: the statements that consume it — semicontinuity and Grauert —
  take it as an instance argument.
* Neither producing lemma below is an instance. `SheafOfModules.Invertible` is a `Prop`-valued
  `def` and not a class, so `SheafOfModules.Invertible.flatOver` takes it as an explicit
  hypothesis; and `AlgebraicGeometry.Scheme.Modules.flatOver_of_flat_stalk` takes the flatness of
  the stalks as an explicit hypothesis as well. The instance one would want instead is that the
  stalk of an `SheafOfModules.IsLocallyFree` sheaf is free over the local ring; that needs the
  stalk of `SheafOfModules.free ι` through sheafification, which is not available — see the
  design note in `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Stalk`.
* The module structure on the stalk over the local ring of the base is
  `AlgebraicGeometry.Scheme.Modules.moduleStalkBase`. It cannot be an instance, since it depends
  on `f`, so it is introduced by `letI` in the definition.

## References

* [Stacks, 01U3](https://stacks.math.columbia.edu/tag/01U3)

## Blueprint

Flatness of a sheaf of modules over the base of a morphism is part of the open obligation
attached to `prop:cube-semicontinuity` in the chapter on the theorem of the cube; it is the
hypothesis "`F` is flat over `T`" of that proposition and of `prop:cube-grauert`.
`SheafOfModules.Invertible.flatOver` is item (4) of `lem:cube-projection-proper-flat` of that
chapter.
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

/-- **The stalks of a line bundle are flat over the local rings of the scheme.** -/
theorem _root_.SheafOfModules.Invertible.flat_stalk {L : X.Modules} (hL : L.Invertible) (x : X) :
    Module.Flat (X.presheaf.stalk x) (L.presheaf.stalk x) := by
  obtain ⟨V, hxV, ⟨e⟩⟩ := hL.exists_restrict_iso_unit x
  have e' : (restrictFunctor V.ι).obj L ≅ (restrictFunctor V.ι).obj X.structureModules :=
    e ≪≫ (restrictUnitIso V.ι).symm
  -- the point `V.ι ⟨x, hxV⟩` of `X` is `x` itself, so the statement below *is* the goal; it has
  -- to be spelled out because the module structures of the comparison are only found when the
  -- local ring and the stalk are written at the same point
  have key : Module.Flat (X.presheaf.stalk (V.ι ⟨x, hxV⟩)) (L.presheaf.stalk (V.ι ⟨x, hxV⟩)) :=
    Module.Flat.of_linearEquiv (stalkLinearEquivOfRestrictIso V.ι ⟨x, hxV⟩ e')
  exact key

/-- **A sheaf of modules whose stalks are flat is flat over the base of a flat morphism.** -/
theorem flatOver_of_flat_stalk (F : X.Modules) (f : X ⟶ Y) [AlgebraicGeometry.Flat f]
    (h : ∀ x : X, Module.Flat (X.presheaf.stalk x) (F.presheaf.stalk x)) : F.FlatOver f := by
  refine ⟨fun x ↦ ?_⟩
  let _ : Module (Y.presheaf.stalk (f.base x)) (F.presheaf.stalk x) := moduleStalkBase F f x
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    AlgebraicGeometry.Flat.stalkMap f x
  have : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  have := h x
  exact Module.Flat.trans _ (X.presheaf.stalk x) _

/-- **A line bundle on the source of a flat morphism is flat over the base.**

This is `lem:cube-projection-proper-flat` (4) of the chapter on the theorem of the cube. -/
theorem _root_.SheafOfModules.Invertible.flatOver {L : X.Modules} (hL : L.Invertible) (f : X ⟶ Y)
    [AlgebraicGeometry.Flat f] : L.FlatOver f :=
  flatOver_of_flat_stalk L f hL.flat_stalk

end AlgebraicGeometry.Scheme.Modules
