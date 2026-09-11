/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

/-!
# Coherence of the direct image along a proper morphism

The cohomological input of the chapter on the theorem of the cube is the finiteness theorem for
proper morphisms: for a proper morphism `f : W ⟶ T` onto a locally Noetherian scheme, the direct
image of a coherent sheaf is coherent. This file states that theorem in degree zero.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward` (blueprint
  `prop:cube-proper-pushforward-coherent`): for `T` locally Noetherian, `f : W ⟶ T` proper and
  `F` a coherent sheaf of `𝒪_W`-modules, the direct image `f_* F` is a coherent sheaf of
  `𝒪_T`-modules. This is `sorry` by design; see the implementation notes.

## Implementation notes

* `isCoherent_pushforward` is `sorry` **by design**: it is the degree-zero case of
  [Stacks, 02O5], and the blueprint marks it as an open obligation rather than proving it. The
  degree-zero case is not appreciably easier than the general one — the standard proof is a
  dévissage over a finite affine cover which computes all degrees at once — so this file states
  it and leaves the proof to a subtree of its own. In the classification of the thirteen open
  obligations of the cube and degree chapters recorded on issue 837 it is obligation 1, rated
  "sorry (deep)", at an estimated four to six pull requests, sharing its infrastructure with
  obligation 8 (`prop:deg-cohomology-finiteness`).
* It is stated as a `theorem` rather than an `instance` on purpose: a statement that rests on a
  `sorry` should be applied by name, so that every place depending on it is visible in the
  source, rather than being picked up silently by typeclass inference.
* `IsCoherent` here is the notion of
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`, namely quasi-coherent
  and of finite type; over the locally Noetherian schemes of this statement it agrees with the
  usual notion of coherence.

## TODO

* Deduce `prop:cube-coherent-finiteness`: for `X` proper over a field `K` and `F` coherent,
  `Γ(X, F)` is a finite-dimensional `K`-vector space. Applying `isCoherent_pushforward` to the
  structure morphism `X ⟶ Spec K` makes `f_* F` coherent on `Spec K`, and `Γ(X, F)` is
  `Γ(Spec K, f_* F)` by definition of the direct image; what is still missing is the remaining
  half of the affine characterisation of coherence, that a sheaf of finite type on an affine
  scheme has a finitely generated module of global sections.

## References

* [Stacks, 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Hartshorne, *Algebraic geometry*][hartshorne1977], III, §8

## Blueprint

`isCoherent_pushforward` implements `prop:cube-proper-pushforward-coherent` of the chapter on
the theorem of the cube.
-/

@[expose] public section

universe u

open CategoryTheory SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

/-- **Coherence of the direct image along a proper morphism**, in degree zero.

For a locally Noetherian scheme `T`, a proper morphism `f : W ⟶ T` and a coherent sheaf of
`𝒪_W`-modules `F`, the direct image `f_* F` is a coherent sheaf of `𝒪_T`-modules. This is
`prop:cube-proper-pushforward-coherent` of the blueprint.

This is the degree-zero case of [Stacks, 02O5] and is `sorry` by design; see the implementation
notes of this file. -/
@[stacks 02O5]
theorem isCoherent_pushforward {W T : Scheme.{u}} (f : W ⟶ T) [IsLocallyNoetherian T]
    [IsProper f] (F : W.Modules) [F.IsCoherent] :
    ((pushforward f).obj F).IsCoherent :=
  sorry

end AlgebraicGeometry.Scheme.Modules
