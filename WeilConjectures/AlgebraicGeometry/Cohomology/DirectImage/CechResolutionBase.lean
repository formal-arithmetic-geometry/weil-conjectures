/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.CechResolution

/-!
# The Čech resolution over an arbitrary base

Let `f : X ⟶ S` be separated and `U` a finite family of opens of `X` covering `X` such that every
finite intersection `U_y` of members of `U` is affine over `S`, i.e. `U_y ⟶ X ⟶ S` is an affine
morphism. For a quasi-coherent `𝒪_X`-module `ℱ` the higher direct image `R^q f_* ℱ` is the `q`-th
cohomology sheaf of `f_* Č(U, ℱ)`
(`AlgebraicGeometry.Scheme.Modules.higherDirectImageIsoCechResolutionOfIsAffineHom`). This
generalises `AlgebraicGeometry.Scheme.Modules.higherDirectImageIsoCechResolution`, where `S` is
affine and the `U_y` are affine opens.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S)

variable {ι : Type u} (U : ι → X.Opens)

end AlgebraicGeometry.Scheme.Modules
