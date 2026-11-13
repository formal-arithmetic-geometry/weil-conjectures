/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.AlgebraicGeometry.OpenPushforwardDerivedComparison

/-! # Acyclic direct images from affine opens

Source: blueprint lem-pc-cech-resolution, proof paragraphs 2 and 3.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An affine open direct image is acyclic for a separated map to an affine scheme.
Source: blueprint lem-pc-cech-resolution, proof paragraphs 2 and 3. -/
theorem affine_open_pushforward_rightAcyclic
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A) [IsSeparated f]
    [HasInjectiveResolutions (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (W : X.Opens) (hW : IsAffineOpen W) (F : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F] :
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightAcyclic
      ((Scheme.Modules.pushforward W.ι).obj (F.restrict W.ι)) := by
  have := Scheme.Modules.isGrothendieckAbelian W.toScheme
  have : IsAffine W.toScheme := hW
  have : IsAffineHom (W.ι ≫ f) := inferInstance
  have : IsAffineHom W.ι := IsAffineHom.of_comp W.ι f
  have hJ : (Scheme.Modules.pushforward W.ι).rightAcyclic (F.restrict W.ι) := by
    intro q
    exact Scheme.Modules.isZero_higherDirectImage_of_isAffineHom W.ι
      (F.restrict W.ι) (by omega)
  intro q
  obtain ⟨e⟩ := open_pushforward_rightDerived_comparison f W (F.restrict W.ι) hJ (q + 1)
  exact (Scheme.Modules.isZero_higherDirectImage_of_isAffineHom (W.ι ≫ f)
    (F.restrict W.ι) (q := q + 1) (by omega)).of_iso e

end AlgebraicGeometry
