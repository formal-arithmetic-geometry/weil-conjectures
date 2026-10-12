/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.Topology.OpenModuleCohomology
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.LerayDegenerateSections
import Sheaf.Topology.RestrictInjectiveResolution
import Sheaf.Paper.HigherDirectImagePresheaf
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

/-! # Leray comparison on affine opens of the target

Source: Stacks Project, Tag 01XK, with open restriction Tag 01E1.
(blueprint: lem-pc-affine-open-higher-direct-image-sections-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Cohomology over the inverse image of an affine open is the group of sections of
the corresponding higher direct image. Both sides use resolutions on the original X.
Source: Stacks Project, Tag 01XK; Tags 01XJ (1), 01E1 and 01F4 (2).
(blueprint: lem-pc-affine-open-higher-direct-image-sections-iso).

Proof: Restrict f to V = f^{-1}U -> U. Restriction of M is quasi-coherent. Both
quasi-compactness and quasi-separatedness are preserved by this base change. By
Tag 01XJ (1) the higher direct images of the restriction are quasi-coherent. Since U
is affine, their positive cohomology vanishes. The Leray edge of Tag 01F4 (2) is
therefore an isomorphism in every degree, as in Tag 01XK. Restriction of an injective
resolution on X to V is injective (Tag 01E1); its section complex is the original
resolution evaluated on V. Direct image and its higher derived functors commute
with restriction to U, computed by the same restricted resolution (Tag 01E4).
These two comparisons identify the edge's source and target with the displayed
objects. Degree zero gives the ordinary section equality, including empty opens. -/
theorem nonempty_affineOpen_higherDirectImage_sections_iso
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (U : S.Opens) (hU : IsAffineOpen U)
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (hM : M.IsQuasicoherent)
    (p : ℕ) :
    Nonempty
      ((((RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ U)).rightDerived p).obj M) ≅
        (RingedSpace.openModuleSections S.toRingedSpace U).obj
          (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj M)) :=
  by sorry

end AlgebraicGeometry
