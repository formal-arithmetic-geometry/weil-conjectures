/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections

/-! # Ordinary higher direct images of quasi-coherent modules

## References

* [Stacks, Tag 01XJ]
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Ordinary higher direct images preserve quasi-coherence for qcqs scheme morphisms
(Stacks, Tag 01XJ). -/
theorem ordinaryHigherImage_isQuasicoherent
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (hM : M.IsQuasicoherent)
    (p : ℕ) :
    SheafOfModules.IsQuasicoherent.{u}
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj M) := by
  let : IsGrothendieckAbelian.{u} X.Modules := Scheme.Modules.isGrothendieckAbelian X
  let := hM
  exact Scheme.Modules.isQuasicoherent_higherDirectImage f M p

end AlgebraicGeometry
