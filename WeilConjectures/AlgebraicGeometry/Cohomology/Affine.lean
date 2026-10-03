/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Cohomology of quasi-coherent sheaves on affine schemes

Serre's vanishing theorem says that the higher cohomology of a quasi-coherent sheaf of modules
on an affine scheme vanishes. Its standard consequence is Leray's theorem: the Čech cohomology
of an open covering all of whose finite intersections are affine computes the sheaf cohomology
of any quasi-coherent sheaf of modules. This applies to every open affine covering of a scheme
which is separated over an affine base.

The Čech complex of a family of open subsets `U : ι → X.Opens` with coefficients in a presheaf
is `CategoryTheory.cechComplexFunctor`: the finite products used there are the finite
intersections `U i₀ ⊓ ⋯ ⊓ U iₙ`, so its `q`-th cohomology is the Čech cohomology `Ȟ^q(𝔘, ℱ)`
of the covering. We take the coefficients in `ℱ.presheafModuleCat`, the presheaf of
`Γ(X, ⊤)`-modules underlying `ℱ`, so that `Ȟ^q(𝔘, ℱ)` is a `Γ(X, ⊤)`-module.

## Implementation notes

The blueprint states Leray's theorem as "the edge map of the Čech-to-derived spectral sequence
is an isomorphism". The edge map is not available as a definition, so
`nonempty_cechComplex_linearEquiv_H` only records the existence of a `Γ(X, ⊤)`-linear
isomorphism, without identifying it with the edge map. For `X` over a base `S`, linearity over
`Γ(X, ⊤)` gives linearity over `Γ(S, 𝒪_S)` acting through `X ⟶ S`, and over `k` when
`S = Spec k`, which is what the tangent-space computation of the Jacobian needs. Identifying
the isomorphism awaits the edge map of `CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_succ_of_isAffine`: the higher cohomology of a
  quasi-coherent sheaf of modules on an affine scheme vanishes.
- `AlgebraicGeometry.Scheme.Modules.nonempty_cechComplex_linearEquiv_H`: Leray's theorem, i.e.
  Čech cohomology of an open covering with affine finite intersections computes the cohomology
  of a quasi-coherent sheaf, linearly over the global functions.
- `AlgebraicGeometry.Scheme.Modules.nonempty_cechComplex_linearEquiv_H_of_isSeparated`: the
  case of an open affine covering of a scheme separated over an affine base.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Vanishing of cohomology on affine schemes.** Let `X = Spec A` be affine. For every
quasi-coherent `𝒪_X`-module `ℱ` and every `q > 0` we have `H^q(X, ℱ) = 0`; the vanishing of the
abelian group `ℱ.H (q + 1)` is expressed as it being a subsingleton.

(blueprint: `sk-lem-picard-affine`) -/
theorem subsingleton_H_succ_of_isAffine [IsAffine X] (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Subsingleton (ℱ.H (q + 1)) :=
  sorry

/-- **Leray's theorem for quasi-coherent sheaves.** Let `𝔘 = (U i)` be an open covering of `X`
all of whose nonempty finite intersections `U i₀ ⊓ ⋯ ⊓ U iₙ` are affine. Then for every
quasi-coherent `𝒪_X`-module `ℱ` and every `q` the Čech cohomology of the covering agrees with
the sheaf cohomology, `Ȟ^q(𝔘, ℱ) ≅ H^q(X, ℱ)`, as `Γ(X, ⊤)`-modules.

The left-hand side is the `q`-th cohomology of the Čech complex `cechComplexFunctor U` of the
family `U` with coefficients in the presheaf of `Γ(X, ⊤)`-modules `ℱ.presheafModuleCat`; the
right-hand side carries the `Γ(X, ⊤)`-module structure
`AlgebraicGeometry.Scheme.Modules.moduleH`.

The isomorphism ought to be the edge map of the Čech-to-derived spectral sequence
`CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence`, which is an isomorphism because
the higher rows of that spectral sequence vanish by `subsingleton_H_succ_of_isAffine`; see the
implementation notes of this module for what is lost by not naming it. -/
@[stacks 01XD]
theorem nonempty_cechComplex_linearEquiv_H {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hU' : iSup U = ⊤)
    (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty (((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q ≃ₗ[Γ(X, ⊤)] ℱ.H q) :=
  sorry

/-- **Leray's theorem for schemes separated over an affine base.** Let `X` be separated over an
affine base `S` and let `𝔘 = (U i)` be a covering of `X` by open affines. Then for every
quasi-coherent `𝒪_X`-module `ℱ` and every `q` we have `Ȟ^q(𝔘, ℱ) ≅ H^q(X, ℱ)` as
`Γ(X, ⊤)`-modules. This is `nonempty_cechComplex_linearEquiv_H`, the finite intersections of
the `U i` being affine because `X` is separated.

Restricting scalars along `f.appTop`, the isomorphism is `Γ(S, 𝒪_S)`-linear, and `k`-linear
when `S = Spec k`.

(blueprint: `sk-lem-picard-cech-computes`) -/
theorem nonempty_cechComplex_linearEquiv_H_of_isSeparated {S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [IsAffine S] {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hU' : iSup U = ⊤) (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty (((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q ≃ₗ[Γ(X, ⊤)] ℱ.H q) :=
  haveI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  nonempty_cechComplex_linearEquiv_H U
    (fun s hs ↦ IsAffineOpen.biInf (s : Set ι) s.finite_toSet hs (fun i _ ↦ hU i)) hU' ℱ q

end AlgebraicGeometry.Scheme.Modules
