/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

/-!
# Serre's criterion for affineness

A quasi-compact quasi-separated scheme `X` with `H¹(X, ℐ) = 0` for every quasi-coherent sheaf of
ideals `ℐ ⊆ 𝒪_X` of finite type is affine (Stacks 01XF).

## Main statements

- `AlgebraicGeometry.isAffine_of_subsingleton_H_one`: Serre's criterion.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- **Serre's criterion for affineness.** Let `X` be a quasi-compact quasi-separated scheme such
that `H¹(X, ℐ) = 0` for every quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_X` of finite type. Then `X`
is affine.

(blueprint: `pqf-lem-serre-criterion`) -/
@[stacks 01XF]
theorem isAffine_of_subsingleton_H_one (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (h : ∀ I : X.IdealSheafData,
      SheafOfModules.IsFiniteType (R := X.ringCatSheaf) I.toModules →
        Subsingleton (I.toModules.H 1)) :
    IsAffine X :=
  sorry

end AlgebraicGeometry
