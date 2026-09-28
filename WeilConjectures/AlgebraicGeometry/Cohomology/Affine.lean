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
of abelian groups is `CategoryTheory.cechComplexFunctor`: the finite products used there are the
finite intersections `U i₀ ⊓ ⋯ ⊓ U iₙ`, so its `q`-th cohomology is the Čech cohomology
`Ȟ^q(𝔘, ℱ)` of the covering.

## Implementation notes

The blueprint states Leray's theorem as "the edge map of the Čech-to-derived spectral sequence
is an isomorphism". The edge map is not available as a definition, so
`nonempty_cechComplex_homology_iso_H` only records the existence of an isomorphism of abelian
groups. That is weaker than the blueprint statement in two ways: the isomorphism is not
identified with the edge map, and it is not known to be linear over `Γ(X, ⊤)` — which a
`k`-linear Koszul computation of the cohomology of projective space would need. Strengthening
it awaits the edge map of
`CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.subsingleton_H_succ_of_isAffine`: the higher cohomology of a
  quasi-coherent sheaf of modules on an affine scheme vanishes.
- `AlgebraicGeometry.Scheme.Modules.nonempty_cechComplex_homology_iso_H`: Leray's theorem, i.e.
  Čech cohomology of an open affine covering computes the cohomology of a quasi-coherent sheaf.
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

/-- **Leray's theorem for quasi-coherent sheaves.** Let `X` be separated over an affine base `S`
and let `𝔘 = (U i)` be a covering of `X` by open affines. Then for every quasi-coherent
`𝒪_X`-module `ℱ` and every `q` the Čech cohomology of the covering agrees with the sheaf
cohomology, `Ȟ^q(𝔘, ℱ) ≅ H^q(X, ℱ)`.

The left-hand side is the `q`-th cohomology of the Čech complex `cechComplexFunctor U` of the
family `U` with coefficients in the underlying presheaf of abelian groups of `ℱ`. The
isomorphism ought to be the edge map of the Čech-to-derived spectral sequence
`CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence`, which is an isomorphism because
the higher rows of that spectral sequence vanish by `subsingleton_H_succ_of_isAffine`; see the
implementation notes of this module for what is lost by not naming it.

(blueprint: `sk-lem-picard-cech-computes`) -/
theorem nonempty_cechComplex_homology_iso_H {S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [IsAffine S] {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hU' : iSup U = ⊤) (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty (((cechComplexFunctor U).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).obj).homology q ≅
      AddCommGrpCat.of (ℱ.H q)) :=
  sorry

end AlgebraicGeometry.Scheme.Modules
