/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Affine pushforward detects degree-zero concentration

Source: Stacks Project, Tags 0AVW, 08I8, and 01XC
(blueprint: lem-sc-affine-derived-concentration).
-/

universe uA wXA wYA

open CategoryTheory

namespace AlgebraicGeometry

/-- An object of `D_QCoh(X)` is represented by a quasi-coherent module in degree zero
if and only if its affine derived direct image is. In that case its degree-zero
higher direct image is the ordinary direct image of any representing module.
Source: Stacks Project, Tags 0AVW, 08I8, and 01XC
(blueprint: lem-sc-affine-derived-concentration).

Proof:
1. If E is represented by F[0], affine higher-direct-image vanishing and preservation
   of quasi-coherence (lem-pc-affine-morphism-hi) show that Rf_*E is represented by
   (f_*F)[0], using def-pc-derived-direct-image.
2. Conversely, affine derived t-exactness and conservativity
   (lem-sc-affine-derived-pushforward-t-exact) reflect both standard truncation bounds.
   Hence E has no cohomology outside degree zero and is represented by H^0(E)[0];
   H^0(E) is quasi-coherent by the assumption E in D_QCoh(X).
3. The degree-zero part of lem-pc-affine-morphism-hi, with the definition of higher
   direct images (def-pc-derived-direct-image), identifies H^0(Rf_*E) with f_*F. -/
theorem affine_derived_concentration {X Y : Scheme.{uA}}
    [HasDerivedCategory.{wXA} (SheafOfModules.{uA} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wYA} (SheafOfModules.{uA} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [IsAffineHom f] (E : schemeDerivedCategory X)
    (hE : schemeDerivedQCohProperty X E) :
    ((∃ F : SheafOfModules.{uA} (moduleRings X.toRingedSpace),
        F.IsQuasicoherent ∧ Nonempty (E ≅
          (DerivedCategory.singleFunctor
            (SheafOfModules.{uA} (moduleRings X.toRingedSpace)) 0).obj F)) ↔
      (∃ G : SheafOfModules.{uA} (moduleRings Y.toRingedSpace),
        G.IsQuasicoherent ∧ Nonempty ((schemeDerivedDirectImage f).obj E ≅
          (DerivedCategory.singleFunctor
            (SheafOfModules.{uA} (moduleRings Y.toRingedSpace)) 0).obj G))) ∧
    (∀ F : SheafOfModules.{uA} (moduleRings X.toRingedSpace),
      F.IsQuasicoherent →
      Nonempty (E ≅ (DerivedCategory.singleFunctor
        (SheafOfModules.{uA} (moduleRings X.toRingedSpace)) 0).obj F) →
      Nonempty ((schemeHigherDirectImage f 0).obj E ≅
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).obj F)) := by
  sorry

end AlgebraicGeometry
