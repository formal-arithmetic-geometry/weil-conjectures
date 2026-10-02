/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

/-!
# Cohomology of quasi-coherent sheaves on affine schemes

Serre's vanishing theorem says that the higher cohomology of a quasi-coherent sheaf of modules
on an affine scheme vanishes. Its standard consequence is Leray's theorem: on a scheme which is
separated over an affine base, the Čech cohomology of an open affine covering computes the
sheaf cohomology of any quasi-coherent sheaf of modules.

The Čech complex of a family of open subsets `U : ι → X.Opens` with coefficients in a presheaf
is `CategoryTheory.cechComplexFunctor`: the finite products used there are the finite
intersections `U i₀ ⊓ ⋯ ⊓ U iₙ`, so its `q`-th cohomology is the Čech cohomology `Ȟ^q(𝔘, ℱ)`
of the covering. We take the coefficients in `ℱ.presheafModuleCat`, the presheaf of
`Γ(X, ⊤)`-modules underlying `ℱ`, so that `Ȟ^q(𝔘, ℱ)` is a `Γ(X, ⊤)`-module.

## Implementation notes

The blueprint states Leray's theorem as "the edge map of the Čech-to-derived spectral sequence
is an isomorphism". The edge map is not available as a definition, so
`nonempty_cechComplex_linearEquiv_H` only records the existence of a `Γ(X, ⊤)`-linear
isomorphism, without identifying it with the edge map. Linearity over `Γ(X, ⊤)` gives
linearity over `Γ(S, 𝒪_S)` acting through `f`, and over `k` when `S = Spec k`, which is what
the tangent-space computation of the Jacobian needs. Identifying the isomorphism awaits the
edge map of `CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.presheafModuleCat`: the presheaf of `Γ(X, ⊤)`-modules
  underlying a sheaf of modules.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_succ_of_isAffine`: the higher cohomology of a
  quasi-coherent sheaf of modules on an affine scheme vanishes.
- `AlgebraicGeometry.Scheme.Modules.nonempty_cechComplex_linearEquiv_H`: Leray's theorem, i.e.
  Čech cohomology of an open affine covering computes the cohomology of a quasi-coherent sheaf,
  linearly over the global functions.
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

/-- The presheaf of `Γ(X, ⊤)`-modules underlying a sheaf of modules `ℱ`: its value on an open
`U` is `Γ(U, ℱ)`, a `Γ(X, ⊤)`-module by restriction of scalars along `Γ(X, ⊤) ⟶ Γ(X, U)`. -/
noncomputable def presheafModuleCat (ℱ : X.Modules) : X.Opensᵒᵖ ⥤ ModuleCat.{u} Γ(X, ⊤) :=
  (PresheafOfModules.forgetToPresheafModuleCat (Opposite.op ⊤) isTerminalTop.op).obj ℱ.val

/-- **Leray's theorem for quasi-coherent sheaves.** Let `X` be separated over an affine base `S`
and let `𝔘 = (U i)` be a covering of `X` by open affines. Then for every quasi-coherent
`𝒪_X`-module `ℱ` and every `q` the Čech cohomology of the covering agrees with the sheaf
cohomology, `Ȟ^q(𝔘, ℱ) ≅ H^q(X, ℱ)`, as `Γ(X, ⊤)`-modules.

The left-hand side is the `q`-th cohomology of the Čech complex `cechComplexFunctor U` of the
family `U` with coefficients in the presheaf of `Γ(X, ⊤)`-modules `ℱ.presheafModuleCat`; the
right-hand side carries the `Γ(X, ⊤)`-module structure `moduleH`. Restricting scalars along
`f.appTop`, the isomorphism is `Γ(S, 𝒪_S)`-linear, and `k`-linear when `S = Spec k`.

The isomorphism ought to be the edge map of the Čech-to-derived spectral sequence
`CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence`, which is an isomorphism because
the higher rows of that spectral sequence vanish by `subsingleton_H_succ_of_isAffine`; see the
implementation notes of this module for what is lost by not naming it.

(blueprint: `sk-lem-picard-cech-computes`) -/
theorem nonempty_cechComplex_linearEquiv_H {S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [IsAffine S] {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hU' : iSup U = ⊤) (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty (((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q ≃ₗ[Γ(X, ⊤)] ℱ.H q) :=
  sorry

end AlgebraicGeometry.Scheme.Modules
