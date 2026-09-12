/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Proper
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The fibrewise dimension of the global sections, and semicontinuity

Let `f : W ⟶ T` be a morphism of schemes and let `F` be a sheaf of `𝒪_W`-modules. For a point
`t : T` the scheme-theoretic fibre `W_t = f.fiber t` is a scheme over the residue field `κ(t)`,
and the restriction `F_t` of `F` to it is a sheaf of `𝒪_{W_t}`-modules; its global sections
`Γ(W_t, F_t)` are therefore a `κ(t)`-vector space. This file introduces that vector space, shows
that it is finite dimensional when `f` is proper and `F` is coherent, and packages its dimension
as a function `h⁰ : T → ℕ`. The semicontinuity theorem — that `{t | n ≤ h⁰ t}` is closed — is
stated, and is `sorry` by design.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.fiberSectionsFunctor`: the global sections of a sheaf of
  modules on the fibre `W_t`, as a functor to `κ(t)`-vector spaces.
- `AlgebraicGeometry.Scheme.Modules.fiberSections`: the `κ(t)`-vector space `Γ(W_t, F_t)`.
- `AlgebraicGeometry.Scheme.Modules.h0` (blueprint `prop:cube-semicontinuity`): the fibrewise
  dimension function `h⁰(t) = dim_{κ(t)} Γ(W_t, F_t)`.
- `AlgebraicGeometry.Scheme.Modules.IsFlatOver`: a sheaf of `𝒪_W`-modules is flat over the base
  of `f : W ⟶ T` if each of its stalks is a flat module over the corresponding local ring of `T`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.finiteDimensional_fiberSections`: for `f` proper and `F`
  coherent, `Γ(W_t, F_t)` is a finite-dimensional `κ(t)`-vector space, so that `h⁰` really is the
  dimension of that space.
- `AlgebraicGeometry.Scheme.Modules.isClosed_setOf_le_h0` (blueprint
  `prop:cube-semicontinuity`): **semicontinuity**. For `T` Noetherian, `f : W ⟶ T` proper and `F`
  coherent and flat over `T`, the set `{t | n ≤ h⁰(t)}` is closed in `T`, for every `n`. This is
  `sorry` by design; see the implementation notes.

## Implementation notes

* `isClosed_setOf_le_h0` is `sorry` **by design**: it is [Stacks, 0BDN], and the blueprint marks
  it as an open obligation rather than proving it. The standard proof computes the cohomology of
  all the fibres from a single perfect complex on the base, so it needs the cohomology of a sheaf
  of modules in every degree, which the project does not have; only the finiteness of the values
  of `h⁰` is proved here, and that is `finiteDimensional_fiberSections`. The `sorry` is stated as
  a `theorem` rather than an `instance` on purpose, so that every place depending on it is
  visible in the source.
* `h0` is defined by `Module.finrank`, which takes the junk value `0` on a space that is not
  finite dimensional. Without properness and coherence there is therefore no guarantee that
  `h0 f F t` is the dimension of `Γ(W_t, F_t)`; under those hypotheses there is, by
  `finiteDimensional_fiberSections`.
* `IsFlatOver` is an auxiliary: flatness of a sheaf of modules over the base of a morphism is
  part of the same open obligation, and is introduced here only because the two statements of
  this subtree cannot be stated without it. It is spelled on stalks, which is the definition of
  [Stacks, 01U3]. It is a plain `def` and not a class, since it is a hypothesis of `sorry`ed
  statements and should be passed explicitly.
* The `κ(t)`-vector space structure on `Γ(W_t, F_t)` is the one carried by the object
  `fiberSections f F t` of `ModuleCat κ(t)`; it comes from viewing `Γ(W_t, F_t)` as the global
  sections on `Spec κ(t)` of the direct image of `F_t` along `W_t ⟶ Spec κ(t)`.

## References

* [Stacks, 0BDN](https://stacks.math.columbia.edu/tag/0BDN)
* [Stacks, 01U3](https://stacks.math.columbia.edu/tag/01U3)
* [Hartshorne, *Algebraic geometry*][hartshorne1977], III, Theorem 12.8

## Blueprint

`isClosed_setOf_le_h0` implements `prop:cube-semicontinuity` of the chapter on the theorem of the
cube, and `h0` is the fibrewise dimension function of that statement.
-/

@[expose] public section

universe u

open CategoryTheory SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {W T : Scheme.{u}}

/-- The global sections of a sheaf of modules on the scheme-theoretic fibre `W_t` of
`f : W ⟶ T` over `t : T`, as a `κ(t)`-vector space: the fibre is a scheme over `Spec κ(t)`, and
this is the direct image along that structure morphism, evaluated at the top open. -/
noncomputable def fiberSectionsFunctor (f : W ⟶ T) (t : T) :
    (f.fiber t).Modules ⥤ ModuleCat (T.residueField t) :=
  pushforward (f.fiberToSpecResidueField t) ⋙ moduleSpecΓFunctor (R := T.residueField t)

/-- The `κ(t)`-vector space `Γ(W_t, F_t)` of global sections of the restriction of a sheaf of
`𝒪_W`-modules `F` to the fibre of `f : W ⟶ T` over `t : T`. -/
noncomputable abbrev fiberSections (f : W ⟶ T) (F : W.Modules) (t : T) :
    ModuleCat (T.residueField t) :=
  (fiberSectionsFunctor f t).obj ((restrictToFiber f t).obj F)

/-- The structure morphism `W_t ⟶ Spec κ(t)` of the fibre of a proper morphism is proper. -/
instance (f : W ⟶ T) [IsProper f] (t : T) : IsProper (f.fiberToSpecResidueField t) :=
  inferInstanceAs (IsProper (Limits.pullback.snd f (T.fromSpecResidueField t)))

/-- **The fibrewise global sections of a coherent sheaf along a proper morphism are finite
dimensional.** This is what makes the function `h0` below the dimension of `Γ(W_t, F_t)`.

It is `AlgebraicGeometry.Scheme.Modules.finiteDimensional_sections` applied to the proper
`κ(t)`-scheme `W_t` and the coherent sheaf `F_t`, and so inherits the `sorry` of
`AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward`. -/
theorem finiteDimensional_fiberSections (f : W ⟶ T) [IsProper f] (F : W.Modules) [F.IsCoherent]
    (t : T) : FiniteDimensional (T.residueField t) (fiberSections f F t) :=
  finiteDimensional_sections (f.fiberToSpecResidueField t) ((restrictToFiber f t).obj F)

/-- **The fibrewise dimension function** `h⁰` of a sheaf of `𝒪_W`-modules `F` along a morphism
`f : W ⟶ T`: the `κ(t)`-dimension of the global sections `Γ(W_t, F_t)` of the restriction of `F`
to the fibre of `f` over `t`.

This is the function `h⁰` of `prop:cube-semicontinuity`. It is defined by `Module.finrank`, which
takes the junk value `0` when `Γ(W_t, F_t)` is not finite dimensional; for `f` proper and `F`
coherent that never happens, by `finiteDimensional_fiberSections`. -/
noncomputable def h0 (f : W ⟶ T) (F : W.Modules) (t : T) : ℕ :=
  Module.finrank (T.residueField t) (fiberSections f F t)

section Flat

/-- The module structure on the stalk `F_x` of a sheaf of `𝒪_W`-modules over the local ring
`𝒪_{T, f x}` of the base of `f : W ⟶ T`, by restriction of scalars along `f.stalkMap x`. -/
@[instance_reducible]
noncomputable def stalkModuleOver (F : W.Modules) (f : W ⟶ T) (x : W) :
    Module (T.presheaf.stalk (f.base x)) (F.presheaf.stalk x) :=
  Module.compHom _ (f.stalkMap x).hom

/-- A sheaf of `𝒪_W`-modules `F` is **flat over `T`** along `f : W ⟶ T` if for every `x : W` the
stalk `F_x` is a flat module over the local ring `𝒪_{T, f x}` of the base, the module structure
being the one given by `AlgebraicGeometry.Scheme.Modules.stalkModuleOver`. -/
@[stacks 01U3]
def IsFlatOver (F : W.Modules) (f : W ⟶ T) : Prop :=
  ∀ x : W, letI := stalkModuleOver F f x
    Module.Flat (T.presheaf.stalk (f.base x)) (F.presheaf.stalk x)

end Flat

/-- **Semicontinuity of the fibrewise dimension of the global sections.**

For a Noetherian scheme `T`, a proper morphism `f : W ⟶ T` and a coherent sheaf of `𝒪_W`-modules
`F` which is flat over `T`, the set of points `t : T` at which `h⁰(t) ≥ n` is closed in `T`, for
every natural number `n`. This is `prop:cube-semicontinuity` of the blueprint.

This is [Stacks, 0BDN] and is `sorry` by design; see the implementation notes of this file. -/
@[stacks 0BDN]
theorem isClosed_setOf_le_h0 [IsNoetherian T] (f : W ⟶ T) [IsProper f] (F : W.Modules)
    [F.IsCoherent] (hflat : F.IsFlatOver f) (n : ℕ) :
    IsClosed {t : T | n ≤ h0 f F t} :=
  sorry

end AlgebraicGeometry.Scheme.Modules
