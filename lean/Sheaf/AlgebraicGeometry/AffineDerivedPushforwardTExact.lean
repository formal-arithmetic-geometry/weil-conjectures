/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Sheaf.AlgebraicGeometry.AffineDerivedCohomology
import Sheaf.AlgebraicGeometry.AffineDerivedPushforwardConservative

/-!
# Affine derived direct image preserves and reflects standard cohomological bounds

Source: Stacks Project, Derived Categories of Schemes, Tags 0AVW and 08I8
(blueprint: lem-sc-affine-derived-pushforward-t-exact).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- Affine derived direct image takes quasi-coherent cohomology to quasi-coherent cohomology,
preserves and reflects both bounds of the standard t-structure, and reflects isomorphisms
between objects with quasi-coherent cohomology.
Source: Stacks Project, Tags 0AVW and 08I8
(blueprint: lem-sc-affine-derived-pushforward-t-exact).

Proof:
1. The affine cohomology comparison `lem-sc-affine-derived-cohomology` identifies
   H^i(Rf_*E) with f_*H^i(E), which is quasi-coherent, for every integer i.
2. This comparison preserves cohomology vanishing above or below every integer n.
   Conversely, if f_*H^i(E) vanishes, apply the same comparison to H^i(E)[0]:
   its derived direct image has zero cohomology in every degree. Its zero map to
   zero therefore has invertible derived direct image, and
   `lem-sc-affine-derived-pushforward-conservative` makes that map invertible.
   Thus H^i(E) vanishes. The descriptions of the standard t-structure in
   `def-sbc-standard-tstructure-derived-category` give both bound equivalences.
3. For a morphism between two objects with quasi-coherent cohomology, apply
   `lem-sc-affine-derived-pushforward-conservative` to reflect invertibility. -/
theorem schemeDerivedDirectImage_tExact_and_conservative_of_affine
    {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [IsAffineHom f] :
    (∀ E : schemeDerivedCategory X, schemeDerivedQCohProperty X E →
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E) ∧
      ∀ n : ℤ,
        (DerivedCategory.IsLE E n ↔
          DerivedCategory.IsLE ((schemeDerivedDirectImage f).obj E) n) ∧
        (DerivedCategory.IsGE E n ↔
          DerivedCategory.IsGE ((schemeDerivedDirectImage f).obj E) n)) ∧
    (∀ (E F : schemeDerivedCategory X),
      schemeDerivedQCohProperty X E → schemeDerivedQCohProperty X F →
      ∀ a : E ⟶ F, IsIso ((schemeDerivedDirectImage f).map a) → IsIso a) := by
  sorry

end AlgebraicGeometry
