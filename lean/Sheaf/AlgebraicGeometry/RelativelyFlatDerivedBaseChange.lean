/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Sheaf.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage

/-! # Derived base change for a relatively flat module

Source: Weil conjectures blueprint, sec-picard-framework/sk-thm-picard-semicon,
lemma lem-pc-rf-base-change-flat-module (blueprint: lem-pc-rf-base-change-flat-module).
-/

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Derived pullback of the derived direct image of a quasi-coherent module flat over
its base is isomorphic to the derived direct image of its ordinary tensor pullback.
Source: Weil conjectures blueprint, sec-picard-framework/sk-thm-picard-semicon,
lemma lem-pc-rf-base-change-flat-module (blueprint: lem-pc-rf-base-change-flat-module).

Proof (the five steps of the node):
1. Restrict the canonical base-change map to affine opens of S and T, using exactness
   of open restriction and its compatibility with derived pullback and direct image
   (lem-pc-base-change-map-cech). Choose a finite affine cover of X; separatedness
   makes its intersections affine. Its bounded Cech complex K computes Rf_*G by
   lem-pc-cech-resolution.
2. Relative flatness makes every module of sections on these affine intersections
   flat over the base ring A. Finite products of flat modules are flat, hence all
   terms of K are A-flat.
3. The associated sheaf complex is bounded and termwise flat. Apply
   lem-pc-flat-complex-derived-pullback to compute Lg^* by ordinary pullback.
   lem-weil-pbc-module-pullback-affine-sections identifies this with (K tensor_A B)~.
4. The pullback affine cover has sections N_J tensor_A B by
   lem-weil-pbc-module-pullback-affine-sections. The component comparisons respect
   the Cech differentials by lem-pc-base-change-map-cech, so identify K tensor_A B
   with the Cech complex of G_T.
5. Under both Cech-resolution identifications (lem-pc-cech-resolution), the canonical
   map is the composite of the isomorphisms in steps 3 and 4, by
   lem-pc-base-change-map-cech. It therefore supplies the asserted isomorphism. -/
theorem nonempty_derivedBaseChange_iso_of_isFlatOver
    {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [IsSeparated f]
    (G : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    [SheafOfModules.IsQuasicoherent.{u} (R := moduleRings X.toRingedSpace) G]
    (hflat : Scheme.Modules.IsFlatOver G f)
    (g : T ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace))] :
    Nonempty
      ((derivedPullback g).obj
        ((schemeDerivedDirectImage f).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G)) ≅
        (schemeDerivedDirectImage (pullback.snd f g)).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings (pullback f g).toRingedSpace)) 0).obj
              ((Scheme.Modules.tensorPullback (pullback.fst f g)).obj G))) := by
  sorry

end AlgebraicGeometry
