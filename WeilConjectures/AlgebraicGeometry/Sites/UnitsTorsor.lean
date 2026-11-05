/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.PicardFunctor
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.Mathlib.Algebra.Category.Grp.Adjunctions
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Invertible modules and `𝒪ˣ`-torsors on the Zariski site

For a scheme `X`, invertible `𝒪_X`-modules up to isomorphism are in bijection with torsors under
the sheaf `𝒪_Xˣ` of units on the Zariski site, up to isomorphism.

## Main definitions

- `AlgebraicGeometry.Scheme.unitsSheaf`: the sheaf `𝒪_Xˣ` of units on the Zariski site.
- `AlgebraicGeometry.Scheme.Modules.generatorsTorsor`: for `M` invertible, the `𝒪_Xˣ`-torsor
  `Isom(𝒪_X, M)` of local generators of `M`.
- `AlgebraicGeometry.Scheme.Modules.ofUnitsTorsor`: for a torsor `T`, the invertible module
  `(T × 𝒪_X) / 𝒪_Xˣ`.

## Main statements

- `AlgebraicGeometry.Scheme.Pic.bijective_torsorClass`: the map `L ↦ Isom(𝒪_X, L)`
  (`AlgebraicGeometry.Scheme.Pic.torsorClass`) is a bijection from `Pic(X)` to the isomorphism
  classes of `𝒪_Xˣ`-torsors, with inverse `T ↦ (T × 𝒪_X) / 𝒪_Xˣ`. The bijection is
  `AlgebraicGeometry.Scheme.picEquivQuotientTorsorUnitsSheaf`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

variable {X}

namespace Modules

variable {M : X.Modules}

section OfUnitsTorsor

variable (T : Sheaf.Torsor X.unitsSheaf)

variable {T}

end OfUnitsTorsor

section Comparison

variable {T T' : Sheaf.Torsor X.unitsSheaf}

section ToOfUnitsTorsor

variable [M.IsInvertible]

end ToOfUnitsTorsor

end Comparison

end Modules

open Modules

end AlgebraicGeometry.Scheme
