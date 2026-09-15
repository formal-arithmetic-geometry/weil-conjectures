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
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Coherence of the direct image along a proper morphism

The cohomological input of the chapter on the theorem of the cube is the finiteness theorem for
proper morphisms: for a proper morphism `f : W ⟶ T` onto a locally Noetherian scheme, the direct
image of a coherent sheaf is coherent. This file states that theorem in degree zero, and deduces
from it the case the chapter actually uses: over a field, the global sections of a coherent sheaf
on a proper scheme form a finite-dimensional vector space.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward` (blueprint
  `prop:cube-proper-pushforward-coherent`): for `T` locally Noetherian, `f : W ⟶ T` proper and
  `F` a coherent sheaf of `𝒪_W`-modules, the direct image `f_* F` is a coherent sheaf of
  `𝒪_T`-modules. This is `sorry` by design; see the implementation notes.
- `AlgebraicGeometry.Scheme.Modules.finiteDimensional_sections` (blueprint
  `prop:cube-coherent-finiteness`): for a field `K`, a proper `K`-scheme `f : X ⟶ Spec K` and
  `F` a coherent sheaf of `𝒪_X`-modules, the global sections `Γ(X, F)` form a finite-dimensional
  `K`-vector space. The `K`-vector space structure is
  `AlgebraicGeometry.Scheme.Modules.sectionsModule`.

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
* The `K`-vector space structure on `Γ(X, F)` used by `finiteDimensional_sections` is not an
  instance: it depends on the structure morphism `f`, which typeclass inference cannot recover
  from `Γ(F, ⊤)`. It is packaged as the `def` `sectionsModule` and introduced by `letI` in the
  statement of the theorem. If `X` does come with an `X.Over (Spec K)` instance, so that the
  structure morphism *is* recoverable, this is the instance
  `AlgebraicGeometry.Scheme.Modules.moduleSections`, by `sectionsModule_eq_moduleSections`.

## References

* [Stacks, 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Hartshorne, *Algebraic geometry*][hartshorne1977], III, §8

## Blueprint

`isCoherent_pushforward` implements `prop:cube-proper-pushforward-coherent` and
`finiteDimensional_sections` implements `prop:cube-coherent-finiteness` of the chapter on the
theorem of the cube.
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

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- The `K`-vector space structure on the global sections of a sheaf of modules `F` on a
`K`-scheme `f : X ⟶ Spec K`: the sections `Γ(F, ⊤)` are a module over `Γ(X, 𝒪_X)`, and scalars
are restricted along `K ≅ Γ(Spec K, 𝒪) ⟶ Γ(X, 𝒪_X)`.

Equivalently, and this is how it is defined, `Γ(F, ⊤)` is the module of global sections of the
direct image `f_* F` on `Spec K`. -/
@[instance_reducible]
noncomputable def sectionsModule (f : X ⟶ Spec (.of K)) (F : X.Modules) : Module K Γ(F, ⊤) :=
  ((moduleSpecΓFunctor (R := .of K)).obj ((pushforward f).obj F)).isModule

/-- For a scheme over `Spec K`, the vector space structure `sectionsModule` along the structure
morphism is the restriction-of-scalars instance
`AlgebraicGeometry.Scheme.Modules.moduleSections`. -/
lemma sectionsModule_eq_moduleSections [X.Over (Spec (.of K))] (F : X.Modules) :
    sectionsModule (X ↘ Spec (.of K)) F = moduleSections K F :=
  rfl

/-- **Finiteness of the global sections of a coherent sheaf on a proper scheme over a field.**

For a field `K`, a proper `K`-scheme `f : X ⟶ Spec K` and a coherent sheaf of `𝒪_X`-modules `F`,
the global sections `Γ(X, F)` form a finite-dimensional `K`-vector space. This is
`prop:cube-coherent-finiteness` of the blueprint.

The proof applies `isCoherent_pushforward` to `f`, which is proper over the Noetherian scheme
`Spec K`, so that `f_* F` is coherent on `Spec K`; a coherent sheaf on an affine scheme has a
finite module of global sections, and `Γ(Spec K, f_* F) = Γ(X, F)` by definition of the direct
image. It therefore inherits the `sorry` of `isCoherent_pushforward`. -/
theorem finiteDimensional_sections (f : X ⟶ Spec (.of K)) [IsProper f] (F : X.Modules)
    [F.IsCoherent] :
    letI := sectionsModule f F
    FiniteDimensional K Γ(F, ⊤) := by
  have : ((pushforward f).obj F).IsCoherent := isCoherent_pushforward f F
  change Module.Finite K ((moduleSpecΓFunctor (R := .of K)).obj ((pushforward f).obj F))
  exact (Scheme.Modules.isCoherent_iff _).mp this

end AlgebraicGeometry.Scheme.Modules
