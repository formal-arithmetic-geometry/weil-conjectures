/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage

/-! # Acyclic direct images from affine opens

Source: blueprint lem-pc-cech-resolution, proof paragraphs 2 and 3.
(blueprint: lem-pc-affine-open-pushforward-acyclic).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An affine open direct image is acyclic for a separated map to an affine scheme.
Source: blueprint lem-pc-cech-resolution, proof paragraphs 2 and 3.
(blueprint: lem-pc-affine-open-pushforward-acyclic)

Proof: X is separated over an affine base. Intersections of affine opens are affine,
so the inclusion j : W → X is affine. The composite W → Spec A is affine as both
its source and target are affine. Restriction of a quasi-coherent module to W is
quasi-coherent. Affine higher-direct-image vanishing therefore gives R^q j_* F|W = 0
and R^q (f j)_* F|W = 0 for q > 0. Restriction to W is an exact left adjoint of j_*,
so j_* preserves injectives. The Grothendieck spectral sequence for (j_*, f_*) has
only its q = 0 row left, so its finite abutment filtration identifies
R^p f_* (j_* F|W) with R^p (f j)_* F|W, which vanishes for p > 0.
This is precisely rightAcyclic for moduleDirectImage f. The empty affine open and
the zero module have zero direct images and satisfy the same conclusion. -/
theorem affine_open_pushforward_rightAcyclic
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A) [IsSeparated f]
    [HasInjectiveResolutions (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (W : X.Opens) (hW : IsAffineOpen W) (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F] :
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightAcyclic
      ((Scheme.Modules.pushforward W.ι).obj (F.restrict W.ι)) := by
  sorry

end AlgebraicGeometry
