/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Proper
public import WeilConjectures.AlgebraicGeometry.Modules.Flat
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The fibrewise dimension of the global sections, and semicontinuity

Let `f : W ⟶ T` be a morphism of schemes and let `F` be a sheaf of `𝒪_W`-modules. For a point
`t : T` the scheme-theoretic fibre `W_t = f.fiber t` is a scheme over the residue field `κ(t)`,
and the restriction `F_t` of `F` to it is a sheaf of `𝒪_{W_t}`-modules; its global sections
`Γ(W_t, F_t)` are therefore a `κ(t)`-vector space
(`AlgebraicGeometry.Scheme.Modules.fiberSections`). This file shows that that vector space is
finite dimensional when `f` is proper and `F` is coherent, and packages its dimension as a
function `h⁰ : T → ℕ`. The semicontinuity theorem — that `{t | n ≤ h⁰ t}` is closed — is
stated, and is `sorry` by design.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.finrankFiberSections` (blueprint
  `prop:cube-semicontinuity`): the fibrewise dimension function
  `h⁰(t) = dim_{κ(t)} Γ(W_t, F_t)`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.finiteDimensional_fiberSections`: for `f` proper and `F`
  coherent, `Γ(W_t, F_t)` is a finite-dimensional `κ(t)`-vector space, so that
  `finrankFiberSections` really is the dimension of that space.
- `AlgebraicGeometry.Scheme.Modules.isClosed_setOf_le_finrankFiberSections` (blueprint
  `prop:cube-semicontinuity`): **semicontinuity**. For `T` Noetherian, `f : W ⟶ T` proper and `F`
  coherent and flat over `T`, the set `{t | n ≤ h⁰(t)}` is closed in `T`, for every `n`. This is
  `sorry` by design; see the implementation notes.

## Implementation notes

* `isClosed_setOf_le_finrankFiberSections` is `sorry` **by design**: it is [Stacks, 0BDN], and
  the blueprint marks it as an open obligation rather than proving it. The standard proof
  computes the cohomology of all the fibres from a single perfect complex on the base, so what
  it needs beyond what this project has is the higher direct images `R^i f_*`, perfect complexes
  on the base, and the base change theorem for them; the cohomology of a sheaf of modules in a
  single degree is available, as `AlgebraicGeometry.Scheme.Modules.H` of
  `WeilConjectures.AlgebraicGeometry.Cohomology.Basic`. Only the finiteness of the values of
  `h⁰` is proved here, and that is `finiteDimensional_fiberSections`. The `sorry` is stated as a
  `theorem` rather than an `instance` on purpose, so that every place depending on it is visible
  in the source.
* `finrankFiberSections` is defined by `Module.finrank`, which takes the junk value `0` on a
  space that is not finite dimensional. Without properness and coherence there is therefore no
  guarantee that `finrankFiberSections f F t` is the dimension of `Γ(W_t, F_t)`; under those
  hypotheses there is, by `finiteDimensional_fiberSections`.
* `finrankFiberSections` is defined from the sections `Γ(W_t, F_t)` and not from `H^0(W_t, F_t)`,
  although the project's convention for fibrewise dimensions elsewhere — in
  `WeilConjectures.AlgebraicGeometry.Cohomology.EulerCharacteristic` — is
  `Module.finrank k (F.H i)`. The reason is the scalars: `H^0(W_t, F_t)` carries a
  `Γ(W_t, 𝒪_{W_t})`-module structure, and a `κ(t)`-structure only through an
  `Over (Spec κ(t))` instance on `W_t`, which the fibre does not have (only the `@[reducible]`
  `Scheme.Hom.fiberOverSpecResidueField`), whereas `fiberSections` is a `κ(t)`-vector space by
  construction. Bridging the two is `AlgebraicGeometry.Scheme.Modules.H.linearEquiv₀` with
  scalars restricted along `κ(t) ⟶ Γ(W_t, 𝒪_{W_t})`; that comparison is left to the pull request
  that first needs the Euler characteristic of a fibre.

## References

* [Stacks, 0BDN](https://stacks.math.columbia.edu/tag/0BDN)
* [Hartshorne, *Algebraic geometry*][hartshorne1977], III, Theorem 12.8

## Blueprint

`isClosed_setOf_le_finrankFiberSections` implements `prop:cube-semicontinuity` of the chapter on
the theorem of the cube, and `finrankFiberSections` is the fibrewise dimension function of that
statement.
-/

@[expose] public section

universe u

open CategoryTheory SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {W T : Scheme.{u}}

/-- **The fibrewise global sections of a coherent sheaf along a proper morphism are finite
dimensional.** This is what makes the function `finrankFiberSections` below the dimension of
`Γ(W_t, F_t)`.

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
noncomputable def finrankFiberSections (f : W ⟶ T) (F : W.Modules) (t : T) : ℕ :=
  Module.finrank (T.residueField t) (fiberSections f F t)

/-- **Semicontinuity of the fibrewise dimension of the global sections.**

For a Noetherian scheme `T`, a proper morphism `f : W ⟶ T` and a coherent sheaf of `𝒪_W`-modules
`F` which is flat over `T`, the set of points `t : T` at which `h⁰(t) ≥ n` is closed in `T`, for
every natural number `n`. This is `prop:cube-semicontinuity` of the blueprint.

This is [Stacks, 0BDN] and is `sorry` by design; see the implementation notes of this file. -/
@[stacks 0BDN]
theorem isClosed_setOf_le_finrankFiberSections [IsNoetherian T] (f : W ⟶ T) [IsProper f]
    (F : W.Modules) [F.IsCoherent] [F.FlatOver f] (n : ℕ) :
    IsClosed {t : T | n ≤ finrankFiberSections f F t} :=
  sorry

end AlgebraicGeometry.Scheme.Modules
