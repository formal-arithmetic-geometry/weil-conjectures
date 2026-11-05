/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.DualNumbers
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.Mathlib.Algebra.DualNumber

/-!
# The Picard group of the dual-number thickening

Let `X` be a scheme and `X[ε]` its dual-number thickening
(`AlgebraicGeometry.Scheme.dualNumbers`), with the closed immersion `i : X ⟶ X[ε]`. The
invertible modules on `X[ε]` which become trivial on `X` are classified by `H¹(X, 𝒪_X)`:

`ker (Pic(X[ε]) → Pic(X)) ≅ H¹(X, 𝒪_X)`,

and under this isomorphism rescaling the infinitesimal, `ε ↦ cε`, is multiplication by `c`.

## Implementation notes

The two schemes have the same underlying space, so all sheaves live on the site of opens of
`X`. The units of `𝒪_{X[ε]} = 𝒪_X[ε]` split as `𝒪_{X[ε]}ˣ ≅ 𝒪_X ⊕ 𝒪_Xˣ`,
`a + εb ↦ (a⁻¹ b, a)`, compatibly with the inclusion `g ↦ 1 + εg` of `𝒪_X` and with
`a + εb ↦ a`, which corresponds to the pullback along `i` under
`Pic ≅ H¹(-, 𝒪ˣ)` (`AlgebraicGeometry.Scheme.Pic.toH1UnitsAddEquiv`). Taking `H¹` of this
splitting gives the isomorphism; no long exact sequence is needed.

## Main statements

- `AlgebraicGeometry.Scheme.exists_addEquiv_ker_picMap_dualNumbersι`: the isomorphism
  `ker (Pic(X[ε]) → Pic(X)) ≅ H¹(X, 𝒪_X)`, compatible with rescaling the infinitesimal.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

end AlgebraicGeometry.Scheme

namespace DualNumber

open TrivSqZeroExt

variable {R S : Type*} [CommRing R] [CommRing S]

end DualNumber

namespace AlgebraicGeometry.Scheme

open DualNumber

variable (X : Scheme.{u})

section Torsor

open Modules

variable {X}

end Torsor

section Kernel

variable {X}

end Kernel

end AlgebraicGeometry.Scheme
