/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
import Sheaf.AlgebraicGeometry.DerivedCategory
import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Upper shriek as the right adjoint to proper direct image

Source: Stacks Project, Duality for Schemes, Tag 0A9E, Lemma 48.3.1,
and Tag 0A9Y, Section 48.16
(blueprint: def-pc-upper-shriek-right-adjoint).

The node writes `h^!` for a chosen right adjoint of `Rh_*` on `D_QCoh`. Its existence
(`noetherian_schemeDerivedDirectImage_has_rightAdjoint`) is not yet proved, and no
proved right adjoint of the derived direct image exists upstream, so `h^!` is not
chosen as data here: `IsProperUpperShriek h u` says that the functor `u` is such a
right adjoint. A chosen adjoint is unique up to unique isomorphism, so every statement
about "the" `h^!` is a statement about any `u` with `IsProperUpperShriek h u`; the
landed binder forms `(R, eR : R ⋙ ι ≅ ι ⋙ Rh_*, u, adj : R ⊣ u)` give
`⟨R, ⟨eR⟩, ⟨adj⟩⟩ : IsProperUpperShriek h u`.
-/

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- For a proper morphism `h : X ⟶ Y` of Noetherian schemes, `u` is an upper shriek `h^!`:
a right adjoint to the derived direct image `Rh_* : D_QCoh(O_X) ⥤ D_QCoh(O_Y)`, that is,
to some functor `R` between the quasi-coherent derived categories whose composite with
the inclusion into `D(O_Y)` is isomorphic to `schemeDerivedDirectImage h` on `D_QCoh(O_X)`
(such an `R` is unique up to isomorphism, the inclusion being fully faithful).
Source: Stacks Project, Tags 0A9E and 0A9Y
(blueprint: def-pc-upper-shriek-right-adjoint). -/
def IsProperUpperShriek
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    [IsLocallyNoetherian Y] [CompactSpace Y]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (h : X ⟶ Y) [IsProper h]
    (u : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X) : Prop :=
  ∃ R : schemeDerivedQCohCategory X ⥤ schemeDerivedQCohCategory Y,
    Nonempty (R ⋙ (schemeDerivedQCohProperty Y).ι ≅
      (schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage h) ∧
    Nonempty (R ⊣ u)

end AlgebraicGeometry
